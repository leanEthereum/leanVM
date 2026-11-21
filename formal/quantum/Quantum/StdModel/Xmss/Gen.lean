module

public import Quantum.Qrom.Xmss.Scheme

@[expose] public section

/-!
# leanXMSS's signer over abstract operations, and the events of the reduction

The signer of leanXMSS uses its secret only through four operations: the value of a chain at a
position, the leaf of a key from its chain ends, a tree node from its children, and the encoding
of a layer's message (the randomizer and the codeword digest). `Gen` is the signer over any
`Ops m`; the reductions run it with operations answered by their challengers, and the ideal game
(the PRF outputs replaced by uniform values) runs it with `idealOps h P c g`: the hash `h`, a
uniform parameter `P`, uniform chain starts `c` and uniform randomizer bases `g`.

The events of the reduction, at the ideal operations `o` and the hash `h`, for a forgery `F`
against the transcript `log`:

* `EncEv`: a layer's forged message and randomizer differ from those of the key's honest
  encoding, with the same digest (EncTCR$);
* `TcrEv`: the forged leaf input or a forged node input along the path differs from the honest one
  with the honest output (SM-TCR-C of the leaf compression and the node hash);
* `CpreEv`: a forged chain value walks to the honest chain end from a position below every opening
  of that chain, or differs from the honest value at its position (CPRE).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss

namespace Quantum.StdModel.Xmss

/-- **The message one layer signs**: a message on the bottom layer, a bottom root on the top. -/
abbrev LayerMsg := Message ⊕ Digest

namespace LayerMsg

/-- The layer that signs the message. -/
def layer : LayerMsg → Layer
  | .inl _ => bottomLayer
  | .inr _ => topLayer

/-- The bytes the layer digests. -/
def bytes : LayerMsg → HashInput
  | .inl m => littleEndianBytes 32 m
  | .inr r => littleEndianBytes 16 r

end LayerMsg

/-- The key of a tree position, as the scheme's tree takes it. -/
def keyAt (j : ℕ) : KeyIndex :=
  ⟨j % lifetime, Nat.mod_lt _ (by decide)⟩

/-- **The signer's operations**: chain `i` of key `(l, e)` at position `μ`, the leaf of a key
from its chain ends, the node `(l, k + 1, j)` from its children, and the encoding of a layer's
message (the randomizer and the codeword digest, or nothing). -/
structure Ops (m : Type → Type) where
  /-- Chain `i` of key `(l, e)` at position `μ`. -/
  chain : Layer → KeyIndex → ChainIndex → ℕ → m Digest
  /-- The leaf of key `(l, e)` from its chain ends. -/
  leaf : Layer → KeyIndex → (ChainIndex → Digest) → m Digest
  /-- The node at level `k + 1`, index `j`, of layer `l` from its children. -/
  node : Layer → ℕ → ℕ → Digest → Digest → m Digest
  /-- The encoding of key `e` of the message's layer. -/
  encode : KeyIndex → LayerMsg → m (Option (Randomizer × Digest))

namespace Gen

variable {m : Type → Type} [Monad m] (o : Ops m)

/-- The chain ends of key `(l, e)`. -/
def otsPublicKey (l : Layer) (e : KeyIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun i ↦ o.chain l e i (chainLength - 1)

/-- The leaf of key `(l, e)`. -/
def keyLeaf (l : Layer) (e : KeyIndex) : m Digest := do
  o.leaf l e (← otsPublicKey o l e)

/-- Node `j` at level `k` of layer `l`'s tree. -/
def treeNode (l : Layer) : ℕ → ℕ → m Digest
  | 0, j => keyLeaf o l (keyAt j)
  | k + 1, j => do
    let left ← treeNode l k (2 * j)
    let right ← treeNode l k (2 * j + 1)
    o.node l k j left right

/-- The authentication path of key `e` of layer `l`. -/
def treePath (l : Layer) (e : KeyIndex) : m (Fin layerHeight → Digest) :=
  sequenceFin fun level ↦ treeNode o l level.val (Nat.xor (e.val / 2 ^ level.val) 1)

/-- The root of the top tree. -/
def root : m Digest :=
  treeNode o topLayer layerHeight 0

/-- One layer's signature of `msg` by key `e`. -/
def signLayer (e : KeyIndex) (msg : LayerMsg) : m (Option LayerSignature) := do
  let some (ρ, d) ← o.encode e msg | return none
  let some x := Codeword.decode d | return none
  let values ← sequenceFin fun i ↦ o.chain msg.layer e i (x i).val
  let path ← treePath o msg.layer e
  return some ⟨ρ, values, path⟩

/-- **The signer** at leaf index `idx`. -/
def sign (idx : LeafIndex) (message : Message) : m (Option Signature) := do
  let bottomKey := keyIndexOnLayer idx bottomLayer
  let topKey := keyIndexOnLayer idx topLayer
  let some bottom ← signLayer o bottomKey (.inl message) | return none
  let bottomRoot ← treeNode o bottomLayer layerHeight topKey.val
  let some top ← signLayer o topKey (.inr bottomRoot) | return none
  return some ⟨idx, fun layer => if layer = bottomLayer then bottom else top⟩

end Gen

/-- **Grinding**: from the trial `t` with `n` trials left, the first randomizer `r0 + t` whose
message digest is a codeword, with that digest. -/
def grind {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (M : HashInput) (r0 : Randomizer) :
    ℕ → ℕ → m (Option (Randomizer × Digest))
  | 0, _ => pure none
  | n + 1, t => do
    let ρ := r0 + BitVec.ofNat digestBits t
    let d ← Qrom.Xmss.Over.messageDigest hash P l e M ρ
    if (Codeword.decode d).isSome then pure (some (ρ, d)) else grind hash P l e M r0 n (t + 1)

/-- **The ideal secret**: the parameter, the chain starts and the randomizer bases. -/
abbrev IdealKey :=
  PublicParameter × (Layer → KeyIndex → ChainIndex → Digest) × (KeyIndex × LayerMsg → Randomizer)

/-- **The ideal operations** at the hash `h`: chains from the starts `c`, the leaf and node hashes,
grinding from the base `g (e, msg)`. -/
def idealOps (h : HashInput → HashOutput) (P : PublicParameter)
    (c : Layer → KeyIndex → ChainIndex → Digest) (g : KeyIndex × LayerMsg → Randomizer) :
    Ops Id where
  chain l e i μ := Qrom.Xmss.Over.chainWalk (m := Id) h P l e i 0 μ (c l e i)
  leaf l e ends := Qrom.Xmss.Over.leafHash (m := Id) h P l e ends
  node l k j a b :=
    Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := grind (m := Id) h P msg.layer e msg.bytes (g (e, msg)) randomizerAttemptLimit 0

/-- The ideal operations of an ideal secret. -/
def IdealKey.ops (h : HashInput → HashOutput) (k : IdealKey) : Ops Id :=
  idealOps h k.1 k.2.1 k.2.2

/-! ## The forged layers -/

section Forged

variable (h : HashInput → HashOutput) (P : PublicParameter) (F : Forgery)

/-- The forged message of layer `l`: the message on the bottom layer, the bottom root the forgery
recovers on the top layer (if any). -/
def forgedMsg (l : Layer) : Option LayerMsg :=
  if l = bottomLayer then some (.inl F.message)
  else (Qrom.Xmss.Over.layerRoot (m := Id) h P bottomLayer
    (keyIndexOnLayer F.signature.leafIndex bottomLayer) (littleEndianBytes 32 F.message)
    (F.signature.layers bottomLayer)).map .inr

/-- The forged key of layer `l`. -/
def forgedKey (l : Layer) : KeyIndex :=
  keyIndexOnLayer F.signature.leafIndex l

/-- The forged message digest of layer `l` for its message `M`. -/
def forgedDigest (l : Layer) (M : LayerMsg) : Digest :=
  Qrom.Xmss.Over.messageDigest (m := Id) h P l (forgedKey F l) M.bytes
    (F.signature.layers l).randomizer

/-- The forged chain ends of layer `l` for its codeword `x`. -/
def forgedEnds (l : Layer) (x : Encoding) : ChainIndex → Digest := fun i ↦
  Qrom.Xmss.Over.recoverChain (m := Id) h P l (forgedKey F l) i (x i)
    ((F.signature.layers l).chainValues i)

/-- The forged value at level `k` of the fold of layer `l` from the leaf `leaf`. -/
def forgedFold (l : Layer) (leaf : Digest) (k : ℕ) : Digest :=
  Qrom.Xmss.Over.treeFold (m := Id) h P l (forgedKey F l)
    (F.signature.layers l).authenticationPath k leaf

/-- The forged children of the node at level `k + 1` above the value `v` at level `k`. -/
def forgedKids (l : Layer) (k : ℕ) (v : Digest) : Digest × Digest :=
  let sib := if hk : k < layerHeight then (F.signature.layers l).authenticationPath ⟨k, hk⟩
    else 0
  if (forgedKey F l).val.testBit k then (sib, v) else (v, sib)

end Forged

/-! ## The events -/

section Events

variable (h : HashInput → HashOutput) (P : PublicParameter) (o : Ops Id)
  (log : QueryLog SigningOracleSpec) (F : Forgery)

/-- The message the request `r` has key `keyIndexOnLayer r.leafIndex l` sign, when the signer
reaches layer `l`. -/
def requestMsg (r : SigningRequest) (l : Layer) : Option LayerMsg :=
  if l = bottomLayer then some (.inl r.message)
  else if (o.encode (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)).isSome then
    some (.inr (Gen.treeNode o bottomLayer layerHeight (keyIndexOnLayer r.leafIndex topLayer).val))
  else none

/-- The honest message of key `(l, e)`: the message some request of the transcript has the key
sign (a requested message on the bottom layer; on the top layer the honest bottom root, when the
request's bottom encoding succeeded). -/
def HonestMsg (l : Layer) (e : KeyIndex) (M : LayerMsg) : Prop :=
  ∃ x ∈ log, keyIndexOnLayer x.1.leafIndex l = e ∧ requestMsg o x.1 l = some M

/-- Chain `i` of key `(l, e)` is opened at or below `μ`: a request has the key encode a message
whose codeword's digit `i` is at most `μ`. -/
def Opened (l : Layer) (e : KeyIndex) (i : ChainIndex) (μ : ℕ) : Prop :=
  ∃ x ∈ log, keyIndexOnLayer x.1.leafIndex l = e ∧ ∃ M, requestMsg o x.1 l = some M ∧
    ∃ ρ D xx, o.encode e M = some (ρ, D) ∧ Codeword.decode D = some xx ∧ (xx i).val ≤ μ

/-- **EncTCR$ event**: some layer's forged message and randomizer differ from the key's honest
encoding and digest to its digest. -/
def EncEv : Prop :=
  ∃ l M', forgedMsg h P F l = some M' ∧ ∃ M ρ D, HonestMsg o log l (forgedKey F l) M ∧
    o.encode (forgedKey F l) M = some (ρ, D) ∧
    (M'.bytes, (F.signature.layers l).randomizer) ≠ (M.bytes, ρ) ∧
    forgedDigest h P F l M' = D

/-- **SM-TCR-C event**: on some layer, the forged leaf input or a forged node input differs from
the honest one and hashes to the honest output. -/
def TcrEv : Prop :=
  ∃ l M', forgedMsg h P F l = some M' ∧ ∃ x, Codeword.decode (forgedDigest h P F l M') = some x ∧
    let e := forgedKey F l
    let ends := forgedEnds h P F l x
    let leaf := Qrom.Xmss.Over.leafHash (m := Id) h P l e ends
    (ends ≠ Gen.otsPublicKey o l e ∧ leaf = Gen.keyLeaf o l e) ∨
    ∃ k < layerHeight,
      let kids := forgedKids F l k (forgedFold h P F l leaf k)
      let j := e.val / 2 ^ (k + 1)
      kids ≠ (Gen.treeNode o l k (2 * j), Gen.treeNode o l k (2 * j + 1)) ∧
      o.node l k j kids.1 kids.2 = Gen.treeNode o l (k + 1) j

/-- **CPRE event**: on some layer, a forged chain value at a position below the chain end walks to
the honest end, and differs from the honest value or lies below every opening of the chain. -/
def CpreEv : Prop :=
  ∃ l M', forgedMsg h P F l = some M' ∧ ∃ x, Codeword.decode (forgedDigest h P F l M') = some x ∧
    ∃ i, (x i).val < chainLength - 1 ∧
      Qrom.Xmss.Over.chainWalk (m := Id) h P l (forgedKey F l) i (x i).val
        (chainLength - 1 - (x i).val) ((F.signature.layers l).chainValues i) =
        o.chain l (forgedKey F l) i (chainLength - 1) ∧
      ((F.signature.layers l).chainValues i ≠ o.chain l (forgedKey F l) i (x i).val ∨
        ¬ Opened o log l (forgedKey F l) i (x i).val)

end Events

end Quantum.StdModel.Xmss

end
