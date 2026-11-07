import FORS.Seed.Guess
import FORS.Scheme.Recovery

/-!
Seed-independent prepared key material and its exact full-output oracle programming interface.

A *secret* is the start of one WOTS+C chain, the secret of one FORS leaf or a surrogate; each is one
derivation, the first 16 bytes (`truncateHash`) of one hash of `SK.seed` at `PK.seed`. Besides the
secrets the seed gives two unaddressed hashes of `leanSPHINCS || SK.seed || d`: `PK.seed`, the first
16 bytes at `d = 0`, and `SK.prf`, the whole output at `d = 1`, which keys the randomizers.

The material holds the two key-seed outputs and one 256-bit value per secret: the full answers of
the programmed entries, including the high 128 bits that honest derivation discards. Only the
secrets' entries depend on the public parameter, the truncated parameter output. This module
defines and verifies the programming operation. It does not assume that an existing honest-game
cache is independent of the master seed or already has the prepared distribution.
-/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SeedModel

variable [Params]

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev ForsPosition := Index × FTree × FLeaf
abbrev SecretPosition := OtsPosition ⊕ (ForsPosition ⊕ Fin maxLayerHeight)
abbrev SecretOutputs := SecretPosition → HashOutput

instance forsPositionDecEq : DecidableEq ForsPosition := inferInstance
instance otsPositionDecEq : DecidableEq OtsPosition := inferInstance
instance secretPositionDecEq : DecidableEq SecretPosition :=
  @instDecidableEqSum _ _ otsPositionDecEq (@instDecidableEqSum _ _ forsPositionDecEq inferInstance)
instance secretPositionFintype : Fintype SecretPosition := inferInstance
noncomputable instance secretOutputsFintype : Fintype SecretOutputs := Pi.instFintype

attribute [local instance] Classical.propDecidable

/-- The outputs at `keySeedInput seed 0` and `keySeedInput seed 1`, then one per secret. -/
abbrev Material := (HashOutput × HashOutput) × SecretOutputs

/-- The output whose first half is `PK.seed`. -/
def parameterOutput (material : Material) : HashOutput := material.1.1

def parameter (material : Material) : PublicParameter := truncateHash (parameterOutput material)

/-- `SK.prf`. -/
def prf (material : Material) : HashOutput := material.1.2

noncomputable opaque secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- This sampling procedure has no master seed as an input. `SK.prf` is drawn last. -/
noncomputable def sampleMaterial : ProbComp Material := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ SecretOutputs
  let prf ← $ᵗ HashOutput
  return ((parameterOutput, prf), outputs)

/-! ### The derivation of each secret -/

/-- The hash domain of the derivation that gives a secret. -/
def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (.inl (index, κ, leaf)) => .fors index κ leaf
  | .inr (.inr level) => .surrogate level

theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  rcases left with ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | _ <;> rcases right with ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | _ <;>
    simp_all [secretDomain]

/-! ### Programming the cache -/

/-- The input whose output gives `PK.seed`. -/
def parameterInput (seed : MasterSeed) : HashInput := keySeedInput seed 0

/-- The input whose output is `SK.prf`. -/
def prfInput (seed : MasterSeed) : HashInput := keySeedInput seed 1

/-- The input of the derivation that gives a secret, at the public parameter of the material. -/
def secretInput (seed : MasterSeed) (material : Material) (position : SecretPosition) : HashInput :=
  keygenHashInput (parameter material) (secretDomain position) seed

theorem secretInput_injective (seed : MasterSeed) (material : Material) :
    Function.Injective (secretInput seed material) := by
  intro left right h
  exact secretDomain_injective (keygenInput_injective h).2.1

theorem prfInput_ne_parameterInput (seed : MasterSeed) : prfInput seed ≠ parameterInput seed := fun h =>
  absurd (keySeedInput_injective (by decide) (by decide) h).2 (by decide)

theorem secretInput_ne_parameterInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ parameterInput seed := fun h =>
  keySeedInput_ne_keygenHashInput seed seed 0 _ _ h.symm

theorem secretInput_ne_prfInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ prfInput seed := fun h =>
  keySeedInput_ne_keygenHashInput seed seed 1 _ _ h.symm

/-- Program the two key-seed outputs and every secret over a base cache. This definition overwrites
its specified entries; a later lemma explicitly requires those entries fresh to preserve the base. -/
noncomputable def programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) : QueryCache HashSpec := fun input =>
  if input = parameterInput seed then some (parameterOutput material)
  else if input = prfInput seed then some (prf material)
  else if h : ∃ position, input = secretInput seed material position then
    some (material.2 (Classical.choose h))
  else base input

theorem programCache_parameter (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (parameterInput seed) = some (parameterOutput material) := by
  simp [programCache]

theorem programCache_prf (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (prfInput seed) = some (prf material) := by
  rw [programCache, if_neg (prfInput_ne_parameterInput seed), if_pos rfl]

theorem programCache_secret (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (position : SecretPosition) :
    programCache base seed material (secretInput seed material position) =
      some (material.2 position) := by
  rw [programCache, if_neg (secretInput_ne_parameterInput seed material position),
    if_neg (secretInput_ne_prfInput seed material position)]
  have h : ∃ other, secretInput seed material position = secretInput seed material other :=
    ⟨position, rfl⟩
  rw [dif_pos h]
  exact congrArg (fun p => some (material.2 p))
    (secretInput_injective seed material (Classical.choose_spec h).symm)

/-- Precisely the key-seed and secret entries are programmed; other seed-bearing inputs are left
alone, including derivations under any other public parameter. -/
theorem programCache_other (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hparameter : input ≠ parameterInput seed) (hprf : input ≠ prfInput seed)
    (hsecret : ∀ position, input ≠ secretInput seed material position) :
    programCache base seed material input = base input := by
  simp only [programCache, hparameter, hprf, ↓reduceIte]
  refine dif_neg ?_
  rintro ⟨position, hd⟩
  exact hsecret position hd

/-! ### The inputs that name the seed -/

/-- This input names the master seed: a derivation of it, or a hash of `leanSPHINCS || seed || d`. -/
abbrev SeedNamed (input : HashInput) (seed : MasterSeed) : Prop := SeedGuess.SeedHit input seed

def AgreeOutsideSeed (seed : MasterSeed) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬SeedNamed input seed → left input = right input

/-- Programming cannot affect an input that does not name the hidden seed. -/
theorem programCache_agreeOutside (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    AgreeOutsideSeed seed (programCache base seed material) base := by
  intro input hnot
  apply programCache_other
  · intro heq
    exact hnot (.inr ⟨0, heq.symm⟩)
  · intro heq
    exact hnot (.inr ⟨1, heq.symm⟩)
  · intro position heq
    exact hnot (.inl ⟨parameter material, secretDomain position, heq.symm⟩)

/-- The concrete verifier never touches a programmed entry. -/
theorem programCache_verifier (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    programCache base seed material (tweakableHashInput p domain payload) =
      base (tweakableHashInput p domain payload) := by
  apply programCache_agreeOutside
  rintro (⟨p', domain', heq⟩ | ⟨index, heq⟩)
  · exact keygenInput_ne_hashInput p' p domain' domain seed payload heq
  · exact keySeedInput_ne_tweakableHashInput seed index p domain payload heq

/-- An answer function extends the complete prepared table. -/
def PreparedAgreement (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) : Prop :=
  f (parameterInput seed) = parameterOutput material ∧ f (prfInput seed) = prf material ∧
    ∀ position, f (secretInput seed material position) = material.2 position

/-- **Every secret reads the sampled table at the actual public parameter**: the signer's secret is
the first half of the material's value at that secret. -/
theorem secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    truncateHash (f (secretInput seed material position)) = truncateHash (material.2 position) := by
  rw [h.2.2]

/-- `PK.seed` reads the sampled table. -/
theorem eval_parameter_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) :
    evalWithAnswerFn f (derivePublicSeed seed : OracleComp HashSpec PublicParameter) = parameter material := by
  simp only [derivePublicSeed]
  exact congrArg truncateHash h.1

/-- `SK.prf` reads the sampled table. -/
theorem eval_prf_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) :
    evalWithAnswerFn f (derivePrf seed : OracleComp HashSpec HashOutput) = prf material := by
  simp only [derivePrf, Completeness.eval_oracleHash]
  exact h.2.1

/-- The start of a WOTS+C chain reads the sampled table. -/
theorem eval_ots_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) :
    evalWithAnswerFn f (Seeded.otsStart (parameter material) lay tree leaf chain seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inl (lay, tree, leaf, chain))) := by
  rw [← secret_prepared f seed material h (.inl (lay, tree, leaf, chain))]
  exact Completeness.otsSecret_eq f _ lay tree leaf seed chain

/-- The secret of a FORS leaf reads the sampled table. -/
theorem eval_fors_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (index : Index) (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (Seeded.forsSecret (parameter material) index κ leaf seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inr (.inl (index, κ, leaf)))) := by
  rw [← secret_prepared f seed material h (.inr (.inl (index, κ, leaf)))]
  exact Completeness.forsSecretValue_eq f _ index κ seed leaf

/-- A surrogate reads the sampled table. -/
theorem eval_surrogate_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (level : Fin maxLayerHeight) :
    evalWithAnswerFn f (deriveKey (parameter material) (.surrogate level) seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inr (.inr level))) := by
  rw [← secret_prepared f seed material h (.inr (.inr level)), Completeness.eval_deriveKey]
  rfl

end FORS.Security.SeedModel
