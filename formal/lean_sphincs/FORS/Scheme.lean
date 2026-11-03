import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import Mathlib.Data.BitVec

/-!
# leanSPHINCS, FORS variant: FORS under a hypertree of WOTS+C keys

The scheme has a height `h = totalHeight` (20, 22, 24, 26 or 28) and a shape (`Params`): one tree of
height `h` of which the key keeps a subtree of `2^b` leaves (`numLayers = 1`, `b = subtreeHeight`,
`b = h` being the full key), or a hypertree of `numLayers = d` layers whose layers below the top have
one height (`lowerHeight`, at least 6) and whose key builds the top layer only (`b = h`). The few-time
signature under every bottom leaf is **FORS** with `k = forsTrees` trees of height `a = forsHeight`:

* a FORS leaf is the hash of a secret; one hash of the seed gives the secrets of leaves `2t` and
  `2t + 1` (its two 16-byte halves);
* a tree is hashed up to level `a - 1` only: its two level-`(a - 1)` nodes `t_κ[0]`, `t_κ[1]` are not
  hashed into a root. The FORS key is the `2k` nodes `t_0[0], t_0[1], ..., t_{k-1}[1]` themselves, the
  message the bottom WOTS+C key signs: no hash folds them, and the WOTS+C encoding absorbs them;
* the digest is `h + k a` bits, the index then the `k` leaf indices, read from the concatenation of
  `⌈(h + k a) / 256⌉` digest calls, which differ by their address; the index is in call 0;
* an opening reveals, per tree, the secret of the selected leaf and its `a` auth nodes. The last auth
  node of a tree is its other top node: the verifier folds all levels but the last and orders the two
  top nodes by index.

At every layer a WOTS+C key (64 chains of length 4, target sum 128) signs the message of the layer
below: the FORS key at the bottom layer, the 16-byte root of the tree below at a layer above.
Layers are numbered from the top (`topLayer = 0`), as in leanVM. Every hash input is
`P || A || payload`: the 16-byte public parameter, then the 16-byte address of the call (a 32-bit
field `lo`, a 24-bit field `hi`, one byte holding the type and a chain step, one byte for the layer
counted from the bottom, 4 bytes for the tree, then 3 zero bytes), so the payload starts at byte 32.
FORS hashes use types 14 (secret derivation), 15 (leaf) and 17 (node), with the instance `idx` in
`lo` and the tree and position in `hi`. The message digest hashes `m || rho` (the root is not hashed:
`P` binds the key) and the randomizer base `S || m`.

The model is one random oracle on these inputs; as for the forest, the statements cover the three
hashes and only the costs depend on the hash.
-/

open OracleComp OracleSpec ENNReal

namespace FORS

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 64
def targetSum : Nat := 128
/-- Randomizers tried per signature (`ctr` is a `u32`), `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per signature, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The key's shape and lifetime. The index has `totalHeight = h` bits. The key is a hypertree of
`numLayers = d` layers, every layer below the top one of height `lowerHeight ≥ 6` (`d = 1` is one
tree of height `h`). Its top layer keeps a subtree: the kept instances are the `2^subtreeHeight`
indices that land in it (`subtreeHeight = h` keeps them all: a full or a layered key). The key signs
at most `signatureLimit` messages. -/
class Params where
  totalHeight : Nat
  numLayers : Nat
  /-- `k`, the number of FORS trees. -/
  forsTrees : Nat
  /-- `a`, the height of a FORS tree. -/
  forsHeight : Nat
  /-- The height of every layer below the top one. -/
  lowerHeight : Nat
  subtreeHeight : Nat
  signatureLimit : Nat
  numLayers_pos : 0 < numLayers
  lowerHeight_ge : 6 ≤ lowerHeight
  /-- The top layer is at least as tall as the others. -/
  lower_le : lowerHeight * numLayers ≤ totalHeight
  /-- The index fields fit the digest and the 32-bit address fields. -/
  totalHeight_le : totalHeight ≤ 28
  /-- The kept subtree lies in the top layer. -/
  below_le : lowerHeight * (numLayers - 1) ≤ subtreeHeight
  subtreeHeight_le : subtreeHeight ≤ totalHeight
  forsTrees_pos : 0 < forsTrees
  /-- The tree fits the 6 bits of the address field `hi` that hold it. -/
  forsTrees_le : forsTrees ≤ 64
  /-- A tree has two top nodes below its root. -/
  forsHeight_ge : 2 ≤ forsHeight
  /-- A level and a node of a tree fit the rest of `hi`. -/
  forsHeight_le : forsHeight ≤ 12

export Params (totalHeight numLayers forsTrees forsHeight lowerHeight subtreeHeight signatureLimit)

/-- A **pruned key** (`numLayers = 1`): one tree of height `h` whose key generation builds the
subtree of height `b` that the public parameter places (`b = h`: the **full key**), with FORS of `k`
trees of height `a`, for at most `N` signatures. With one layer `lowerHeight` is not used; it is set
to 6. -/
abbrev Params.pruned (h b k a N : Nat) (hh : h ≤ 28 := by decide) (h6 : 6 ≤ h := by decide)
    (hb : b ≤ h := by decide) (hk : 0 < k := by decide) (hk' : k ≤ 64 := by decide)
    (ha : 2 ≤ a := by decide) (ha' : a ≤ 12 := by decide) : Params where
  totalHeight := h
  numLayers := 1
  forsTrees := k
  forsHeight := a
  lowerHeight := 6
  subtreeHeight := b
  signatureLimit := N
  numLayers_pos := Nat.one_pos
  lowerHeight_ge := Nat.le_refl 6
  lower_le := h6
  totalHeight_le := hh
  below_le := Nat.zero_le b
  subtreeHeight_le := hb
  forsTrees_pos := hk
  forsTrees_le := hk'
  forsHeight_ge := ha
  forsHeight_le := ha'

/-- A **layered key**: a hypertree of `d` layers and height `h` whose layers below the top have
height `ℓ` (the top layer has the rest, `h - ℓ (d - 1)`); key generation builds the whole top layer
(`subtreeHeight = h`), with FORS of `k` trees of height `a`. At most `N` signatures. -/
abbrev Params.layered (h d ℓ k a N : Nat) (hd : 0 < d := by decide) (hℓ : 6 ≤ ℓ := by decide)
    (hle : ℓ * d ≤ h := by decide) (hh : h ≤ 28 := by decide) (hk : 0 < k := by decide)
    (hk' : k ≤ 64 := by decide) (ha : 2 ≤ a := by decide) (ha' : a ≤ 12 := by decide) : Params where
  totalHeight := h
  numLayers := d
  forsTrees := k
  forsHeight := a
  lowerHeight := ℓ
  subtreeHeight := h
  signatureLimit := N
  numLayers_pos := hd
  lowerHeight_ge := hℓ
  lower_le := hle
  totalHeight_le := hh
  below_le := Nat.le_trans (Nat.mul_le_mul_left ℓ (Nat.sub_le d 1)) hle
  subtreeHeight_le := Nat.le_refl h
  forsTrees_pos := hk
  forsTrees_le := hk'
  forsHeight_ge := ha
  forsHeight_le := ha'

variable [Params]

/-- The height of the top layer, the tallest: `h - lowerHeight (d - 1)`. -/
def maxLayerHeight : Nat := totalHeight - lowerHeight * (numLayers - 1)

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
/-- A layer, `0` being the top one. -/
abbrev Layer := Fin numLayers
/-- `idx`, the bottom leaf and the FORS instance a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, a tree of a layer. Layer `lay` only uses the values below `2^heightAbove lay`. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- `e`, a leaf of a tree. Layer `lay` only uses the values below `2^layerHeight lay`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPair := Fin 32
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-! ### FORS types -/

/-- `κ`, a FORS tree. -/
abbrev FTree := Fin forsTrees
/-- A leaf, or a node index at any level, of a FORS tree. -/
abbrev FLeaf := Fin (2 ^ forsHeight)
/-- A pair of leaves `(2t, 2t + 1)` of a FORS tree: one seed derivation. -/
abbrev FPair := Fin (2 ^ (forsHeight - 1))
/-- A level of a FORS tree that is hashed, `1 .. a - 1`, as `level - 1`; `Fin forsHeight` also
names level `a`, whose address no algorithm uses. -/
abbrev FLevel := Fin forsHeight

/-- The height of a layer: `h - 6 (d - 1)` at the top, 6 below. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else lowerHeight

def topLayer : Layer := ⟨0, Params.numLayers_pos⟩

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := lowerHeight * (numLayers - 1 - lay.val)

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output (bytes 16 to 31). The seed derivations of chain starts and
FORS secrets and the step of the randomizer walk use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output for chain or FORS leaf `n`: the first for even `n`, the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-! ### The message digest: `h + k a` bits from `⌈(h + k a) / 256⌉` calls -/

/-- The message digest is `h + k a` bits: an index and the `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + forsTrees * forsHeight

/-- The number of digest calls: `⌈(h + k a) / 256⌉`. -/
def digestCalls : Nat := (messageDigestBits + hashOutputBits - 1) / hashOutputBits

theorem digestCalls_pos : 0 < digestCalls := by
  have hk := Params.forsTrees_pos
  have ha := Params.forsHeight_ge
  unfold digestCalls messageDigestBits hashOutputBits
  have : 1 ≤ forsTrees * forsHeight := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- A digest call. -/
abbrev DigestCall := Fin digestCalls

/-- The first digest call, which holds the index. -/
def firstCall : DigestCall := ⟨0, digestCalls_pos⟩

abbrev MessageDigest := BitVec messageDigestBits

/-- The outputs of the digest calls as one number, call 0 in the low 256 bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (hashOutputBits * call.val)

/-- The first `h + k a` bits of the concatenated calls. -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat messageDigestBits (digestValue outputs)

/-- The FORS key of an instance: the two level-`(a - 1)` nodes of every tree, `(t_κ[0], t_κ[1])`. It
is not hashed: the WOTS+C encoding absorbs the `2k` nodes (`Concrete.encode`). -/
abbrev ForsKey := FTree → Digest × Digest

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- The WOTS+C signature and authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The opening of one FORS tree: the secret of the selected leaf and its `a` auth nodes. -/
structure TreeOpening where
  secret : Digest
  path : Fin forsHeight → Digest
deriving DecidableEq

/-- The randomizer, the FORS opening, and the WOTS+C signature with its path at every layer:
`16 + 16 k (a + 1) + 1028 d + 16 h` bytes (`Layout.signature_size`). -/
structure Signature where
  randomness : Randomness
  fors : FTree → TreeOpening
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call (`Tweak` in `crates/sphincs`): its type `tag < 32`, a chain step
`step < 8`, the layer (counted from the bottom) and the tree, and two fields `hi < 2^24` and
`lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  layer : BitVec 8
  tree : BitVec 32
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || layer || tree || 0^3`: `lo` on 4 bytes,
`hi` on 3 bytes, the type byte, the layer byte, `tree` on 4 bytes, each least significant byte
first, then 3 zero bytes. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++
    bytesLE 1 fields.layer ++ bytesLE 4 fields.tree ++ bytesLE 3 0

/-- Convert the integer fields of an address outside the hypertree (layer and tree 0). -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, 0, 0, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The layer byte of layer `lay`: the layers are counted from the bottom on the wire. -/
def layerByte (lay : Layer) : Nat := numLayers - 1 - lay.val

/-- Convert the integer fields of an address in tree `tree` of layer `lay`. -/
def treeFields (tag step : Nat) (lay : Layer) (tree : TreeIndex) (hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 8 (layerByte lay), BitVec.ofNat 32 tree.val,
    BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-! ### FORS addresses -/

/-- `κ + 64 p`, a position `p` of tree `κ` of the instance. -/
def forsSlot (κ : FTree) (position : Nat) : Nat := κ.val + 64 * position

/-- The position of node `node` at level `level` of a tree: `level + 16 node`. -/
def nodePosition (level node : Nat) : Nat := level + 16 * node

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. A `forsNode` at `level` is the
node of FORS tree level `level + 1`: the scheme hashes levels 1 to `a - 1`, and the address of a
tree's root exists and no algorithm uses it. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | forsLeaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | forsNode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  | message (call : DigestCall)
deriving DecidableEq

/-- The address of a hash domain: types `TWEAK_CHAIN = 1`, ..., `TWEAK_MSG = 12`, FORS types 15 and
17. In the tree `lo` is the leaf (or the node index) and `hi` the chain (or the node level); a chain
step carries its step. In a FORS instance `lo` is `idx` and `hi` packs the tree, the level and the
node, `κ + 64 (level + 16 node)` (a leaf: `κ + 64 leaf`). A
hash of the hypertree carries its layer and its tree; a digest call carries its number in `hi`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => treeFields 1 step lay tree chainIdx leaf
  | .leaf lay tree leaf => treeFields 2 0 lay tree 0 leaf
  | .node lay tree level nodeIdx => treeFields 3 0 lay tree level nodeIdx
  | .encoding lay tree leaf => treeFields 4 0 lay tree 0 leaf
  | .forsLeaf index κ leaf => tweakFields 15 0 (forsSlot κ leaf.val) index
  | .forsNode index κ level node => tweakFields 17 0 (forsSlot κ (nodePosition (level.val + 1) node.val)) index
  | .message call => tweakFields 12 0 call.val 0

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `P || A || payload` of every tweakable hash call and of the message
digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- `P || A(7, 0, 0) || S || m` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes ⟨7#5, 0#3, 0#8, 0#32, 0#24, 0#32⟩ ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of leaves a leaf of a FORS tree belongs to. -/
def leafPair (leaf : FLeaf) : FPair :=
  ⟨leaf.val / 2, by
    have h := leaf.isLt
    have ha := Params.forsHeight_ge
    have : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega⟩

/-- The seed derivations, one hash each. `ots` gives the starts of chains `2t` and `2t + 1` of the
one-time key at a leaf, `fors` the secrets of leaves `2t` and `2t + 1` of tree `κ` of instance `idx`:
the two 16-byte halves of the hash. The parameter and a surrogate are the first 16 bytes of their
hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | fors (index : Index) (κ : FTree) (pair : FPair)
  | surrogate (level : Fin maxLayerHeight)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the leaf, with the layer
and the tree),
type 14 for a FORS secret pair (`hi` the tree and the pair of leaves, `lo = idx`), `TWEAK_SURROGATE = 13`
(`hi` the level). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots lay tree leaf pair => treeFields 0 0 lay tree pair leaf
  | .fors index κ pair => tweakFields 14 0 (forsSlot κ pair.val) index
  | .surrogate level => tweakFields 13 0 level 0

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 128`. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- Offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest) then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(P || tw || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau`, the tree of layer `lay` on the path of `idx`: the bits above the layer. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (heightBelow lay + layerHeight lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight
  split
  · exact le_refl _
  · have h1 := Params.lower_le
    have h2 := Params.numLayers_pos
    unfold maxLayerHeight
    have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- The tree below the leaf `leaf` of tree `tree` of layer `lay` (the tree that leaf's key signs the
root of), or at the bottom layer the FORS instance it signs the key of: `tree · 2^h_lay + leaf`. -/
def childTree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : TreeIndex :=
  ⟨(tree.val * 2 ^ layerHeight lay + leaf.val) % 2 ^ totalHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `e`, the leaf of that tree on the path of `idx`: the layer's bits of the index. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (layerHeight_le lay))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `steps` chain steps from position `start`: the step onto position `start + steps + 1` carries
step `start + steps` (`chain_tweak` with `to = start + steps + 1`). -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `t_0[0] || t_0[1] || ... || t_{k-1}[0] || t_{k-1}[1]`, the FORS key as bytes: the level-`(a - 1)`
nodes of the `k` trees. -/
def rootsPayload (tops : ForsKey) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- The message a layer's WOTS+C key signs, as bytes: the FORS key's `2k` nodes at the bottom layer
(`rootsPayload`), the 16-byte root of the tree below at a layer above. -/
def rootPayload (root : Digest) : HashInput := bytesLE 16 root

/-- `Enc(P, e, M, c)`: hash the message, then the counter, under the leaf's encoding tweak, and
decode. There is no message hash: the counter falls in the last block of this one
(`P || A || K || c`, `36 + 32 k` bytes, at the bottom layer; `P || A || root || c`, 52 bytes,
above). -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_recover`): the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### The tree -/

/-- `Tree.fold` (`tree_fold`): fold a leaf and a path into the root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### FORS -/

/-- A FORS leaf: the hash of its secret. -/
def forsLeafHash (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.forsLeaf index κ leaf) (bytesLE 16 secret)

/-- Fold a FORS leaf and a path over `levels` levels. -/
def forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← forsFold parameter index κ leaf path levels value
      if hlevel : levels < forsHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : FLeaf := ⟨leaf.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩
        if leaf.val.testBit levels then
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The two top nodes of a tree in index order, from the one the fold reached and the last path
element: the reached node is node 1 exactly when `bit`, the top bit of the leaf index, is set. -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- The last level of a FORS path: the other level-`(a - 1)` node. -/
def topLevel : Fin forsHeight := ⟨forsHeight - 1, by have := Params.forsHeight_ge; omega⟩

/-- The two level-`(a - 1)` nodes of a FORS tree that an opening reaches: the leaf is folded `a - 1`
levels, and the last path element is the other top node. -/
def treeRecover (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (opening : TreeOpening) : m (Digest × Digest) := do
  let value ← forsLeafHash parameter index κ leaf opening.secret
  let node ← forsFold parameter index κ leaf opening.path (forsHeight - 1) value
  return orderTops (leaf.val.testBit (forsHeight - 1)) node (opening.path topLevel)

/-- `Fts.recover`: the FORS key an opening reaches. A tree has no root hash, and the key has no hash:
the WOTS+C encoding absorbs it. -/
def forsRecover (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) : m ForsKey :=
  sequenceFin fun κ => treeRecover parameter index κ (leaves κ) (opening κ)

/-! ### The message digest -/

/-- `m || rho`, what the message digest hashes after the parameter and the address: `P || A || m ||
rho` is 80 bytes, within one Keccak-256 block (136 bytes). The root is not hashed (`P` binds the key); the
argument is kept for the callers. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- One untruncated digest call. -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : m HashOutput :=
  oracleHash (tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness))

/-- `idx`, the low `h` bits of the digest. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- The leaf index of the first digest call, where the index is. -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' 0 totalHeight).toFin

/-- `Digest(P, m, rho)`: the calls, concatenated and truncated to `h + k a` bits. The root is not an
input of the hash. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let outputs ← sequenceFin fun call => messageDigestCall parameter root message randomness call
  return truncateMessageDigest outputs

/-- Bit offset of the leaf index of tree `κ`: `h + a κ`. -/
def leafOffset (κ : FTree) : Nat := totalHeight + forsHeight * κ.val

/-- The leaf indices of a digest. -/
def digestLeaves (digest : MessageDigest) : FTree → FLeaf := fun κ =>
  (digest.extractLsb' (leafOffset κ) forsHeight).toFin

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The walk up the layers: `remaining + 1` enters at layer `remaining`, whose WOTS+C key signs
`message` (the FORS key at the bottom layer, the root of the tree below above it); the fold of the
top layer is the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → HashInput → m (Option Digest)
  | 0, _ => pure none
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        if remaining = 0 then
          return some root
        else
          verifyLayers parameter index signature remaining (rootPayload root)
      else
        pure none

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the FORS key, walk the layers (recover the
one-time leaf, fold the path) and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let forsKey ← forsRecover publicKey.parameter index (digestLeaves digest) signature.fors
  let some root ← verifyLayers publicKey.parameter index signature numLayers (rootsPayload forsKey)
    | return false
  return decide (root = publicKey.root)

/-! ### Signing -/

/-- The top layer holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- Run the `n` computations from index `0` up, stopping on the first failure. -/
def sequenceDep : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → m (Option (α i))) → m (Option ((i : Fin n) → α i))
  | 0, _, _ => pure (some fun i => Fin.elim0 i)
  | _ + 1, α, computation => do
      let some head ← computation 0 | return none
      let some tail ← sequenceDep (α := fun i => α i.succ) fun i => computation i.succ | return none
      return some (Fin.cases head tail)

/-- Run the layers from the top down, stopping on failure. -/
def sequenceLayers {α : Layer → Type}
    (computation : (lay : Layer) → m (Option (α lay))) : m (Option ((lay : Layer) → α lay)) :=
  sequenceDep computation

attribute [irreducible] verify

end Concrete

/-! ### Pruning -/

section Pruning

/-- `s`, the kept subtree of the top layer: the low `h - b` bits of `P`, read as a little-endian
number (`0` for a full or a layered key). -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- The kept instances are `s * 2^b .. (s + 1) * 2^b` (`XmssTree::contains` on the top layer's
leaf `idx >> heightBelow topLayer`). -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

/-- The height of the kept part of a layer's tree: `b - heightBelow topLayer` at the top layer, the
whole tree below it. -/
def keptHeight (lay : Layer) : Nat := if lay.val = 0 then subtreeHeight - heightBelow lay else layerHeight lay

/-- The position of the kept part among the nodes of level `keptHeight`: `s` at the top layer, `0`
below it. -/
def keptPosition (parameter : PublicParameter) (lay : Layer) : Nat :=
  if lay.val = 0 then subtreePosition parameter else 0

end Pruning

/-- One seed derivation, first 16 bytes: the parameter and the surrogates. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes (`th_pair`): its two halves are the starts of two chains or the
secrets of two FORS leaves. -/
def deriveOutput {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

/-- The step of a randomizer walk: its lowest bit is set, so the walk `R0 + i * step` does not come
back before `2^128` attempts. -/
def walkStep (half : Randomness) : Randomness := half ||| 1#digestBits

/-- One hash per message (`randomizer_walk`): its first half is the base randomizer `R0`, its second
half gives the step of the walk. -/
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : m (Randomness × Randomness) := do
  let output ← Concrete.oracleHash (randomizerHashInput parameter seed message)
  return (truncateHash output, walkStep (upperHash output))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, from 32 seed
derivations. Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPair => deriveOutput parameter (.ots lay tree leaf pair) seed
  return fun chainIdx => hashHalf chainIdx.val (outputs (chainPair chainIdx))

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay tree leaf seed
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets parameter lay tree leaf seed
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf seed message encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf seed
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree seed level (2 * nodeIdx)
      let right ← treeNode parameter lay tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- The surrogate sibling at `level >= b`, derived from the seed (`TWEAK_SURROGATE`). Honest calls
have `level < h`. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel : level < maxLayerHeight then deriveKey parameter (.surrogate ⟨level, hlevel⟩) seed else pure 0

/-- The node at level `k + steps` above the kept part (`k = keptHeight lay`): its root folded with
the first `steps` surrogates (`XmssTree::from_leaves`). -/
def spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → m Digest
  | 0 => treeNode parameter lay tree seed (keptHeight lay) (keptPosition parameter lay)
  | steps + 1 => do
      let below ← spineNode parameter lay tree seed steps
      let sibling ← surrogate parameter seed (keptHeight lay + steps)
      let nodeIdx := keptPosition parameter lay / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root of a layer's tree: the spine's top (the whole tree's root below the top layer). -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  spineNode parameter lay tree seed (layerHeight lay - keptHeight lay)

/-- The authentication path of a kept leaf (`XmssTree::path`): nodes of the kept part below level
`keptHeight`, surrogates from that level on. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin (layerHeight lay) → Digest) :=
  sequenceFin fun level =>
    if level.val < keptHeight lay then
      treeNode parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate parameter seed level.val

end Seeded

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The secret of one FORS leaf, by its own derivation of its pair: a level-0 `forsNode`. Key
generation and signing derive each pair once (`forsNode` from level 1, `treeOpen`). -/
def forsSecret (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.fors index κ (leafPair leaf)) seed
  return hashHalf leaf.val output

/-- A node of a FORS tree at tree level `level`. A level-1 node derives its pair of leaves once:
the two halves of the hash are their secrets. -/
def forsNode (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => do
      let leaf : FLeaf := ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let secret ← forsSecret parameter index κ leaf seed
      forsLeafHash parameter index κ leaf secret
  | 1, node => do
      let left : FLeaf := ⟨2 * node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let right : FLeaf := ⟨(2 * node + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let output ← deriveOutput parameter (.fors index κ (leafPair left)) seed
      let leftLeaf ← forsLeafHash parameter index κ left (hashHalf 0 output)
      let rightLeaf ← forsLeafHash parameter index κ right (hashHalf 1 output)
      tweakableHash parameter (.forsNode index κ ⟨0, by have := Params.forsHeight_ge; omega⟩
        ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload leftLeaf rightLeaf)
  | level + 2, node => do
      let left ← forsNode parameter index κ seed (level + 1) (2 * node)
      let right ← forsNode parameter index κ seed (level + 1) (2 * node + 1)
      if hlevel : level + 1 < forsHeight then
        tweakableHash parameter (.forsNode index κ ⟨level + 1, hlevel⟩
          ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The FORS key of instance `idx`: the two level-`(a - 1)` nodes of every tree (no hash). -/
def forsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m ForsKey :=
  sequenceFin fun κ => do
    let left ← forsNode parameter index κ seed (forsHeight - 1) 0
    let right ← forsNode parameter index κ seed (forsHeight - 1) 1
    return (left, right)

/-- The opening of one tree at a leaf. One derivation gives the secret and the sibling leaf (path
level 0); the last path element (level `a - 1`) is the top node the verifier does not compute. -/
def treeOpen (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m TreeOpening := do
  let output ← deriveOutput parameter (.fors index κ (leafPair leaf)) seed
  let sibling : FLeaf := ⟨Nat.xor leaf.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let siblingLeaf ← forsLeafHash parameter index κ sibling (hashHalf sibling.val output)
  let path ← sequenceFin fun level : Fin forsHeight =>
    if level.val = 0 then pure siblingLeaf
    else forsNode parameter index κ seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return ⟨hashHalf leaf.val output, path⟩

/-- `Fts.sign`: the opening of every tree. -/
def forsOpen (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (seed : MasterSeed) : m (FTree → TreeOpening) :=
  sequenceFin fun κ => treeOpen parameter index κ (leaves κ) seed

/-- `Gen` (`key_gen`): derive the public parameter, which places the kept subtree, and build the root
of the top layer. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

/-- One grinding attempt: the index read from the first digest call (`digest_index`). -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness firstCall
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

/-- What the WOTS+C key at leaf `leaf` of tree `tree` of layer `lay` signs: the root of the tree
below it, or the FORS key of its instance at the bottom layer. -/
def keyMessage (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : m HashInput :=
  if hbelow : lay.val + 1 < numLayers then do
    let root ← treeRoot parameter ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) seed
    return rootPayload root
  else do
    let key ← forsKey parameter (childTree lay tree leaf) seed
    return rootsPayload key

/-- What the WOTS+C key of layer `lay` on the path of `idx` signs. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m HashInput :=
  keyMessage secretKey.parameter secretKey.seed lay (treeIndexAt index lay) (leafIndexAt index lay)

def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) : m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- Try `randomness, randomness + step, randomness + 2 step, ...`, stopping at the first that lands
in the kept subtree. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) (step : Randomness) : Nat → Randomness →
    m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message step attempts (randomness + step)

/-- `Sign`: derive the randomizer base `R0` and the step `delta` of the message (one hash), scan
`R0, R0 + delta, ...` into the kept subtree, compute the digest, open FORS, and at every layer sign
the message of the layer below (the FORS key's `2k` top nodes at the bottom) with WOTS+C and attach
the path. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let walk ← deriveRandomizer secretKey.parameter secretKey.seed message
  let some (randomness, _) ← signDigestLoop secretKey message walk.2 digestAttemptLimit walk.1
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forsOpen secretKey.parameter index (digestLeaves digest) secretKey.seed
  let some layers ← sequenceLayers (fun lay => signLayer secretKey index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

end FORS
