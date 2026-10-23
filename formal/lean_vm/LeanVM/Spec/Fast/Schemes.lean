/-
  LeanVM.Spec.Fast.Schemes

  The signature schemes' verifiers as the compiled node checks and hint generator run them:
  `sequenceFin` with a constant-depth lookup, and the functions above it restated word for word,
  swapped in by `@[csimp]`.
-/

module

public import LeanXmss.Scheme
public import Sphincs.Scheme

/-!
# The compiled signature schemes

Both schemes collect a one-time key's chain ends with `sequenceFin`, which returns
`Fin.cases head tail`. Compiled, `Fin.cases` is `Fin.induction`, which evaluates the value below an
index before discarding it, so looking up index `i` looks up every index below it in the tail: a
lookup costs `2^i`, out of reach at the `58` and `64` chains of a leaf. `sequenceFin` is restated
here with `cons`, whose lookup peels one index, and proved equal (`sequenceFin_eq`); the
verifiers' functions that call it are restated word for word, each equal to its definition by
`rfl`, so that every module importing this one compiles them with it (a `@[csimp]` lemma acts
where code is compiled, so it does not reach the schemes' own modules). Nothing here transcribes
a source.
-/

namespace LeanVM.Schemes.Fast

@[expose] public section

/-- `Fin.cases head tail`, looking up an index without the ones below it. -/
def cons {α : Type} {n : Nat} (head : α) (tail : Fin n → α) : Fin (n + 1) → α :=
  fun i ↦ if h : i.val = 0 then head else tail ⟨i.val - 1, by omega⟩

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

theorem sequenceFin_xmss {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      LeanXmss.Concrete.sequenceFin computation = sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
    simp only [LeanXmss.Concrete.sequenceFin, sequenceFin, cases_eq_cons]
    congr 1
    funext head
    rw [sequenceFin_xmss]

theorem sequenceFin_sphincs {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      Sphincs.Concrete.sequenceFin computation = sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
    simp only [Sphincs.Concrete.sequenceFin, sequenceFin, cases_eq_cons]
    congr 1
    funext head
    rw [sequenceFin_sphincs]

@[csimp] theorem xmss_sequenceFin_eq : @LeanXmss.Concrete.sequenceFin = @sequenceFin := by
  funext m _ α n computation
  exact sequenceFin_xmss computation

@[csimp] theorem sphincs_sequenceFin_eq : @Sphincs.Concrete.sequenceFin = @sequenceFin := by
  funext m _ α n computation
  exact sequenceFin_sphincs computation

/-! ## leanXMSS -/

namespace Xmss

open LeanXmss LeanXmss.Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `LeanXmss.Concrete.otsLeaf`. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomness) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← LeanXmss.Concrete.sequenceFin fun chainIdx =>
    recoverChain parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay key endpoints
  return some value

@[csimp] theorem otsLeaf_eq : @LeanXmss.Concrete.otsLeaf = @otsLeaf := rfl

/-- `LeanXmss.Concrete.layerRoot`, with `otsLeaf`. -/
def layerRoot (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← LeanXmss.Concrete.otsLeaf parameter lay key message part.randomness
    part.chainValues | return none
  let root ← treeFold parameter lay key part.path layerHeight leaf
  return some root

@[csimp] theorem layerRoot_eq : @LeanXmss.Concrete.layerRoot = @layerRoot := rfl

/-- `LeanXmss.Concrete.verify`, with `layerRoot`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let index := signature.leafIndex
  let some bottomRoot ← LeanXmss.Concrete.layerRoot publicKey.parameter bottomLayer
      (keyAt index bottomLayer) (bytesLE 32 message) (signature.layers bottomLayer) | return false
  let some root ← LeanXmss.Concrete.layerRoot publicKey.parameter topLayer (keyAt index topLayer)
      (bytesLE 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

@[csimp] theorem verify_eq : @LeanXmss.Concrete.verify = @verify := by
  unfold LeanXmss.Concrete.verify
  rfl

end Xmss

/-! ## leanSPHINCS -/

namespace Sphincs

open _root_.Sphincs _root_.Sphincs.Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `Sphincs.Concrete.otsLeaf`. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← _root_.Sphincs.Concrete.sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

@[csimp] theorem otsLeaf_eq : @_root_.Sphincs.Concrete.otsLeaf = @otsLeaf := rfl

/-- `Sphincs.Concrete.verifyLayers`, with `otsLeaf`. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← _root_.Sphincs.Concrete.otsLeaf parameter lay tree leaf message part.counter
            part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none

@[csimp] theorem verifyLayers_eq : @_root_.Sphincs.Concrete.verifyLayers = @verifyLayers := by
  funext m _ _ parameter index signature remaining message
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
    simp only [_root_.Sphincs.Concrete.verifyLayers, verifyLayers, ih]
    rfl

/-- `Sphincs.Concrete.verify`, with `verifyLayers`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let ftsPublicKey ← forestRecover publicKey.parameter index (digestMarks digest) signature.forest
  let some root ← _root_.Sphincs.Concrete.verifyLayers publicKey.parameter index signature numLayers
      ftsPublicKey | return false
  return decide (root = publicKey.root)

@[csimp] theorem verify_eq : @_root_.Sphincs.Concrete.verify = @verify := by
  unfold _root_.Sphincs.Concrete.verify
  rfl

end Sphincs

end
end LeanVM.Schemes.Fast
