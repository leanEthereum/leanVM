/-
  Statement.Fast.Schemes

  The signature schemes' verifiers as the compiled node checks and hint generator run them:
  `sequenceFin` with a constant-depth lookup, and the functions above it restated word for word,
  swapped in by `@[csimp]`.

  Speed only: `@[csimp]` lemmas, each proved, that change how the statement's definitions are
  compiled and nothing they mean. Not part of what a reviewer of `Statement/` must read.
-/

module

public import Statement.LeanXmss
public import Statement.LeanSphincs

/-!
# The compiled signature schemes

Both schemes collect a one-time key's chain ends with `sequenceFin`, which returns
`Fin.cases head tail`. Compiled, `Fin.cases` is `Fin.induction`, which evaluates the value below an
index before discarding it, so looking up index `i` looks up every index below it in the tail: a
lookup costs `2^i`, out of reach at the `58` and `64` chains of a leaf. `sequenceFin` is restated
here with `cons`, whose lookup peels one index, and proved equal (`sequenceFin_eq`); the
verifiers' functions that call it are restated word for word, each equal to its definition by
`rfl`, so that every module importing this one compiles them with it (a `@[csimp]` lemma acts
where code is compiled, so it does not reach the schemes' own modules; `Statement.LeanVmGuest`
imports this one, so the guest's specification and every module after it compile them so).
Nothing here transcribes a source.
-/

namespace LeanVM.Schemes.Fast

@[expose] public section

/-- `Fin.cases head tail`, looking up an index without the ones below it. -/
def cons {α : Type} {n : Nat} (head : α) (tail : Fin n → α) : Fin (n + 1) → α :=
  fun i ↦ if h : i.val = 0 then head else tail ⟨i.val - 1, by omega⟩

/-- `Fin.cases` is `cons`. -/
theorem cases_eq_cons {α : Type} {n : Nat} (head : α) (tail : Fin n → α) :
    (Fin.cases head tail : Fin (n + 1) → α) = cons head tail := by
  funext i
  induction i using Fin.cases with
  | zero => simp [cons]
  | succ j => simp [cons]

/-- `sequenceFin`, with `cons`. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} :
    {n : Nat} → (Fin n → m α) → m (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, computation => do
    let head ← computation 0
    let tail ← sequenceFin fun index : Fin n ↦ computation index.succ
    return cons head tail

/-- The schemes' `sequenceFin` (leanSPHINCS's is leanXMSS's) is `sequenceFin`. -/
theorem sequenceFin_xmss {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      HashSig.OverPermutation.sequenceFin computation = sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
    simp only [HashSig.OverPermutation.sequenceFin, sequenceFin, cases_eq_cons]
    congr 1
    funext head
    rw [sequenceFin_xmss]

/-- The schemes' `sequenceFin` compiles as `sequenceFin`. -/
@[csimp] theorem xmss_sequenceFin_eq : @HashSig.OverPermutation.sequenceFin = @sequenceFin := by
  funext m _ α n computation
  exact sequenceFin_xmss computation

/-! ## leanXMSS -/

namespace Xmss

open LeanXmss HashSig LeanXmss.Verification HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `LeanXmss.Verification.otsLeaf`. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomizer) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest π parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← HashSig.OverPermutation.sequenceFin fun chainIdx =>
    recoverChain π parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash π parameter lay key endpoints
  return some value

/-- `LeanXmss.Verification.otsLeaf` compiles as its restatement. -/
@[csimp] theorem otsLeaf_eq : @LeanXmss.Verification.otsLeaf = @otsLeaf := rfl

/-- `LeanXmss.Verification.layerRoot`, with `otsLeaf`. -/
def layerRoot (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← LeanXmss.Verification.otsLeaf π parameter lay key message part.randomizer
    part.chainValues | return none
  let root ← treeFold π parameter lay key part.authenticationPath layerHeight leaf
  return some root

/-- `LeanXmss.Verification.layerRoot` compiles as its restatement. -/
@[csimp] theorem layerRoot_eq : @LeanXmss.Verification.layerRoot = @layerRoot := rfl

/-- `LeanXmss.Verification.verify`, with `layerRoot`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let index := signature.leafIndex
  let some bottomRoot ← LeanXmss.Verification.layerRoot π publicKey.parameter bottomLayer
      (keyIndexOnLayer index bottomLayer) (littleEndianBytes 32 message) (signature.layers
          bottomLayer) | return false
  let some root ← LeanXmss.Verification.layerRoot π publicKey.parameter topLayer (keyIndexOnLayer
      index topLayer)
      (littleEndianBytes 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

/-- `LeanXmss.Verification.verify` compiles as its restatement. -/
@[csimp] theorem verify_eq : @LeanXmss.Verification.verify = @verify := by
  unfold LeanXmss.Verification.verify
  rfl

/-- `LeanXmss.verifyWithKeccak`, restated, so that it compiles with `verify` above. -/
def verifyWithKeccak (publicKey : HashSig.PublicKey) (message : HashSig.Message)
    (signature : LeanXmss.Signature) : Bool :=
  Id.run (LeanXmss.Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey message
    signature)

/-- `LeanXmss.verifyWithKeccak` compiles as its restatement. -/
@[csimp] theorem verifyWithKeccak_eq : @LeanXmss.verifyWithKeccak = @verifyWithKeccak := rfl

end Xmss

/-! ## leanSPHINCS -/

namespace Sphincs

open HashSig HashSig.OverPermutation _root_.Sphincs _root_.Sphincs.Verification
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `Sphincs.Verification.otsLeaf`. -/
def otsLeaf (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode π publicSeed layer tree leaf message counter | return none
  let endpoints ← HashSig.OverPermutation.sequenceFin fun chainIndex =>
    recoverChain π publicSeed layer tree leaf chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash π publicSeed layer tree leaf endpoints
  return some value

/-- `Sphincs.Verification.otsLeaf` compiles as its restatement. -/
@[csimp] theorem otsLeaf_eq : @_root_.Sphincs.Verification.otsLeaf = @otsLeaf := rfl

/-- `Sphincs.Verification.forsRecover`. -/
def forsRecover (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    m Digest := do
  let roots ← HashSig.OverPermutation.sequenceFin fun forsTree =>
    forsTreeRecover π publicSeed index forsTree (leaves forsTree) (opening forsTree)
  forsPublicKey π publicSeed index roots

/-- `Sphincs.Verification.forsRecover` compiles as its restatement. -/
@[csimp] theorem forsRecover_eq : @_root_.Sphincs.Verification.forsRecover = @forsRecover := rfl

/-- `Sphincs.Verification.messageDigest`. -/
def messageDigest (publicKey : _root_.Sphincs.PublicKey) (randomizer : Randomizer)
    (message : Message) : m MessageDigest := do
  let outputs ← HashSig.OverPermutation.sequenceFin fun call =>
    messageDigestCall π randomizer publicKey.publicSeed publicKey.root message call
  return truncateMessageDigest outputs

/-- `Sphincs.Verification.messageDigest` compiles as its restatement. -/
@[csimp] theorem messageDigest_eq :
    @_root_.Sphincs.Verification.messageDigest = @messageDigest := rfl

/-- `Sphincs.Verification.verifyLayers`, with `otsLeaf`. -/
def verifyLayers (publicSeed : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, _ => pure none
  | layersLeft + 1, message => do
      if hlayer : layersLeft < layerCount then
        let layer : Layer := ⟨layerCount - 1 - layersLeft, by omega⟩
        let tree := treeOfIndex layer index
        let leaf := leafOfIndex layer index
        let some value ← _root_.Sphincs.Verification.otsLeaf π publicSeed layer tree leaf message
            (signature.layers layer).counter (signature.layers layer).chainValues
          | return none
        let root ← treeFold π publicSeed layer tree leaf (layerPath signature layer)
          (layerHeight layer) value
        if layersLeft = 0 then
          return some root
        else
          verifyLayers publicSeed index signature layersLeft root
      else
        pure none

/-- `Sphincs.Verification.verifyLayers` compiles as its restatement. -/
@[csimp] theorem verifyLayers_eq :
    @_root_.Sphincs.Verification.verifyLayers = @verifyLayers := by
  funext m _ π publicSeed index signature layersLeft message
  induction layersLeft generalizing message with
  | zero => rfl
  | succ layersLeft ih =>
    simp only [_root_.Sphincs.Verification.verifyLayers, verifyLayers, ih]
    rfl

/-- `Sphincs.Verification.verify`, with `messageDigest`, `forsRecover` and `verifyLayers`. -/
def verify (publicKey : _root_.Sphincs.PublicKey) (message : Message) (signature : Signature) :
    m Bool := do
  let digest ← _root_.Sphincs.Verification.messageDigest π publicKey signature.randomizer message
  let index := digestIndex digest
  let forsKey ← _root_.Sphincs.Verification.forsRecover π publicKey.publicSeed index
    (digestForsLeaves digest) signature.forsOpening
  let some root ← _root_.Sphincs.Verification.verifyLayers π publicKey.publicSeed index signature
      layerCount forsKey
    | return false
  return decide (root = publicKey.root)

/-- `Sphincs.Verification.verify` compiles as its restatement. -/
@[csimp] theorem verify_eq : @_root_.Sphincs.Verification.verify = @verify := by
  unfold _root_.Sphincs.Verification.verify
  rfl

/-- `Sphincs.verifyWithKeccak`, restated, so that it compiles with `verify` above. -/
def verifyWithKeccak (publicKey : _root_.Sphincs.PublicKey) (message : HashSig.Message)
    (signature : _root_.Sphincs.Signature) : Bool :=
  Id.run (_root_.Sphincs.Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey
    message signature)

/-- `Sphincs.verifyWithKeccak` compiles as its restatement. -/
@[csimp] theorem verifyWithKeccak_eq : @_root_.Sphincs.verifyWithKeccak = @verifyWithKeccak := rfl

end Sphincs

end
end LeanVM.Schemes.Fast
