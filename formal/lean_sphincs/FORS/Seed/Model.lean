import FORS.Seed.Guess
import FORS.Scheme.Recovery

/-!
Seed-independent prepared key material and its exact full-output oracle programming interface.

A *secret* is the start of one WOTS+C chain, the secret of one FORS leaf or a surrogate; a
*derivation* is one hash of the seed. A surrogate is one derivation (its first 16 bytes). The starts
of chains `2t` and `2t + 1` of a key, and the secrets of leaves `2t` and `2t + 1` of a FORS tree, are
the two 16-byte halves of one derivation.

The material holds one 256-bit value per secret; the secret is its first 16 bytes (`truncateHash`),
as for a scheme with one derivation per secret. The programmed answer of a derivation
(`derivedOutput`) is the surrogate's value, or the two secrets of its pair side by side.
Uniform material gives independent uniform answers (`SeedCoupling.evalDist_derivedOutput_uniform`).
Only the parameter derivation uses the zero public parameter; all other entries use its truncated
sampled output. This module defines and verifies the programming operation. It does not assume that
an existing honest-game cache is independent of the master seed or already has the prepared
distribution.
-/

open OracleComp OracleSpec

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

/-- The derivations of the chain starts of a one-time key: one per pair of chains. -/
abbrev OtsDerivation := Layer × TreeIndex × LeafIndex × ChainPair
/-- The derivations of the secrets of a FORS tree: one per pair of leaves. -/
abbrev ForsDerivation := Index × FTree × FPair
/-- The seed derivations at the public parameter: one hash each. -/
abbrev Derivation := OtsDerivation ⊕ (ForsDerivation ⊕ Fin maxLayerHeight)
abbrev DerivedOutputs := Derivation → HashOutput

instance forsDerivationDecEq : DecidableEq ForsDerivation := inferInstance
instance otsDerivationDecEq : DecidableEq OtsDerivation := inferInstance
instance derivationDecEq : DecidableEq Derivation :=
  @instDecidableEqSum _ _ otsDerivationDecEq (@instDecidableEqSum _ _ forsDerivationDecEq inferInstance)
instance derivationFintype : Fintype Derivation := inferInstance
noncomputable instance derivedOutputsFintype : Fintype DerivedOutputs := Pi.instFintype

attribute [local instance] Classical.propDecidable

/-- Full256-bit responses are retained, including the high128bits that honest derivation discards. -/
abbrev Material := HashOutput × SecretOutputs

def parameter (material : Material) : PublicParameter := truncateHash material.1

noncomputable opaque secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- This sampling procedure has no master seed as an input. -/
noncomputable def sampleMaterial : ProbComp Material := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ SecretOutputs
  return (parameterOutput, outputs)

/-! ### Derivations and the secrets they give -/

def derivationDomain : Derivation → KeygenDomain
  | .inl (lay, tree, leaf, pair) => .ots lay tree leaf pair
  | .inr (.inl (index, κ, pair)) => .fors index κ pair
  | .inr (.inr level) => .surrogate level

theorem derivationDomain_injective : Function.Injective derivationDomain := by
  intro left right h
  cases left with
  | inl left =>
      rcases left with ⟨lay, tree, leaf, pair⟩
      cases right with
      | inl right => rcases right with ⟨lay', tree', leaf', pair'⟩; simpa [derivationDomain] using h
      | inr right => cases right <;> cases h
  | inr left =>
      cases left with
      | inl left =>
          rcases left with ⟨index, κ, pair⟩
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => rcases right with ⟨index', κ', pair'⟩; simpa [derivationDomain] using h
              | inr right => cases h
      | inr left =>
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => cases h
              | inr right => simpa [derivationDomain] using h

theorem derivationDomain_ne_parameter (derivation : Derivation) :
    derivationDomain derivation ≠ .parameter := by
  cases derivation with
  | inl p => rcases p with ⟨_, _, _, _⟩; simp [derivationDomain]
  | inr p => cases p <;> simp [derivationDomain]

/-- The derivation that gives a secret. -/
def secretDerivation : SecretPosition → Derivation
  | .inl (lay, tree, leaf, chain) => .inl (lay, tree, leaf, chainPair chain)
  | .inr (.inl (index, κ, leaf)) => .inr (.inl (index, κ, leafPair leaf))
  | .inr (.inr level) => .inr (.inr level)

/-- The half of its derivation that is a secret: the half of its parity for a chain start, the first
half for a surrogate. -/
def secretHalf : SecretPosition → HashOutput → Digest
  | .inl (_, _, _, chain) => hashHalf chain.val
  | .inr (.inl (_, _, leaf)) => hashHalf leaf.val
  | .inr (.inr _) => truncateHash

/-- The hash domain of the derivation that gives a secret. -/
def secretDomain (position : SecretPosition) : KeygenDomain :=
  derivationDomain (secretDerivation position)

/-- Chain `2t` of a one-time key. -/
def evenChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; simp only [numChains]; omega⟩
/-- Chain `2t + 1` of a one-time key. -/
def oddChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; simp only [numChains]; omega⟩
theorem two_pow_forsHeight_eq : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
  rw [← Nat.pow_succ']; congr 1; have := Params.forsHeight_ge; omega

/-- Leaf `2t` of a FORS tree. -/
def evenLeaf (pair : FPair) : FLeaf := ⟨2 * pair.val, by have := pair.isLt; rw [two_pow_forsHeight_eq]; omega⟩
/-- Leaf `2t + 1` of a FORS tree. -/
def oddLeaf (pair : FPair) : FLeaf := ⟨2 * pair.val + 1, by have := pair.isLt; rw [two_pow_forsHeight_eq]; omega⟩

theorem chainPair_evenChain (pair : ChainPair) : chainPair (evenChain pair) = pair := by
  apply Fin.ext; simp only [chainPair, evenChain]; omega

theorem chainPair_oddChain (pair : ChainPair) : chainPair (oddChain pair) = pair := by
  apply Fin.ext; simp only [chainPair, oddChain]; omega

theorem leafPair_evenLeaf (pair : FPair) : leafPair (evenLeaf pair) = pair := by
  apply Fin.ext; simp only [leafPair, evenLeaf]; omega

theorem leafPair_oddLeaf (pair : FPair) : leafPair (oddLeaf pair) = pair := by
  apply Fin.ext; simp only [leafPair, oddLeaf]; omega

theorem chain_eq_of_even (chain : ChainIndex) (h : chain.val % 2 = 0) : evenChain (chainPair chain) = chain := by
  apply Fin.ext; simp only [chainPair, evenChain]; omega

theorem chain_eq_of_odd (chain : ChainIndex) (h : ¬chain.val % 2 = 0) : oddChain (chainPair chain) = chain := by
  apply Fin.ext; simp only [chainPair, oddChain]; omega

theorem leaf_eq_of_even (leaf : FLeaf) (h : leaf.val % 2 = 0) : evenLeaf (leafPair leaf) = leaf := by
  apply Fin.ext; simp only [leafPair, evenLeaf]; omega

theorem leaf_eq_of_odd (leaf : FLeaf) (h : ¬leaf.val % 2 = 0) : oddLeaf (leafPair leaf) = leaf := by
  apply Fin.ext; simp only [leafPair, oddLeaf]; omega

/-- Every derivation gives a secret. -/
theorem secretDerivation_surjective : Function.Surjective secretDerivation := by
  intro derivation
  cases derivation with
  | inl p =>
      rcases p with ⟨lay, tree, leaf, pair⟩
      exact ⟨.inl (lay, tree, leaf, evenChain pair), by simp only [secretDerivation, chainPair_evenChain]⟩
  | inr p =>
      cases p with
      | inl p =>
          rcases p with ⟨index, κ, pair⟩
          exact ⟨.inr (.inl (index, κ, evenLeaf pair)),
            by simp only [secretDerivation, leafPair_evenLeaf]⟩
      | inr level => exact ⟨.inr (.inr level), rfl⟩

/-! ### The two halves of a hash output -/

/-- The hash output with the given first and second 16 bytes. -/
noncomputable def joinHalves (low high : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem split_joinHalves (low high : Digest) :
    splitHashOutput digestBits (joinHalves low high) = (low, high) :=
  (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)

@[simp] theorem truncateHash_joinHalves (low high : Digest) : truncateHash (joinHalves low high) = low :=
  congrArg Prod.fst (split_joinHalves low high)

@[simp] theorem upperHash_joinHalves (low high : Digest) : upperHash (joinHalves low high) = high :=
  congrArg Prod.snd (split_joinHalves low high)

@[simp] theorem joinHalves_halves (output : HashOutput) :
    joinHalves (truncateHash output) (upperHash output) = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

theorem hashHalf_even {n : Nat} (h : n % 2 = 0) (output : HashOutput) :
    hashHalf n output = truncateHash output := by
  simp only [hashHalf, h, ↓reduceIte]

theorem hashHalf_odd {n : Nat} (h : ¬n % 2 = 0) (output : HashOutput) :
    hashHalf n output = upperHash output := by
  simp only [hashHalf, h, ↓reduceIte]

/-! ### The answers of the derivations -/

/-- The answer of each derivation: the two secrets of a pair side by side, the full value of a
surrogate. -/
noncomputable def derivedOutput (outputs : SecretOutputs) : Derivation → HashOutput
  | .inl (lay, tree, leaf, pair) =>
      joinHalves (truncateHash (outputs (.inl (lay, tree, leaf, evenChain pair))))
        (truncateHash (outputs (.inl (lay, tree, leaf, oddChain pair))))
  | .inr (.inl (index, κ, pair)) =>
      joinHalves (truncateHash (outputs (.inr (.inl (index, κ, evenLeaf pair)))))
        (truncateHash (outputs (.inr (.inl (index, κ, oddLeaf pair)))))
  | .inr (.inr level) => outputs (.inr (.inr level))

/-- **Every secret is read back from the answer of its derivation.** -/
theorem secretHalf_derivedOutput (outputs : SecretOutputs) (position : SecretPosition) :
    secretHalf position (derivedOutput outputs (secretDerivation position)) =
      truncateHash (outputs position) := by
  cases position with
  | inl p =>
      rcases p with ⟨lay, tree, leaf, chain⟩
      simp only [secretHalf, secretDerivation, derivedOutput]
      by_cases h : chain.val % 2 = 0
      · rw [hashHalf_even h, truncateHash_joinHalves, chain_eq_of_even chain h]
      · rw [hashHalf_odd h, upperHash_joinHalves, chain_eq_of_odd chain h]
  | inr p =>
      cases p with
      | inl p =>
          rcases p with ⟨index, κ, leaf⟩
          simp only [secretHalf, secretDerivation, derivedOutput]
          by_cases h : leaf.val % 2 = 0
          · rw [hashHalf_even h, truncateHash_joinHalves, leaf_eq_of_even leaf h]
          · rw [hashHalf_odd h, upperHash_joinHalves, leaf_eq_of_odd leaf h]
      | inr level => rfl

/-- What a table of answers requires of the value at one secret position: for a chain start, its
first half is the half of the answer of its pair; for a surrogate, it is the answer. -/
def Compatible (table : DerivedOutputs) : SecretPosition → HashOutput → Prop
  | .inl p, value => truncateHash value = secretHalf (.inl p) (table (secretDerivation (.inl p)))
  | .inr (.inl p), value =>
      truncateHash value = secretHalf (.inr (.inl p)) (table (secretDerivation (.inr (.inl p))))
  | .inr (.inr level), value => value = table (.inr (.inr level))

/-- The material that gives a table of answers is described position by position. -/
theorem derivedOutput_eq_iff (outputs : SecretOutputs) (table : DerivedOutputs) :
    derivedOutput outputs = table ↔ ∀ position, Compatible table position (outputs position) := by
  constructor
  · rintro rfl position
    cases position with
    | inl p => exact (secretHalf_derivedOutput outputs (.inl p)).symm
    | inr p =>
        cases p with
        | inl p => exact (secretHalf_derivedOutput outputs (.inr (.inl p))).symm
        | inr level => rfl
  · intro h
    funext derivation
    cases derivation with
    | inl p =>
        rcases p with ⟨lay, tree, leaf, pair⟩
        have he := h (.inl (lay, tree, leaf, evenChain pair))
        have ho := h (.inl (lay, tree, leaf, oddChain pair))
        simp only [Compatible, secretHalf, secretDerivation, chainPair_evenChain,
          chainPair_oddChain] at he ho
        rw [hashHalf_even (by simp only [evenChain]; omega)] at he
        rw [hashHalf_odd (by simp only [oddChain]; omega)] at ho
        simp only [derivedOutput, he, ho, joinHalves_halves]
    | inr p =>
        cases p with
        | inl p =>
            rcases p with ⟨index, κ, pair⟩
            have he := h (.inr (.inl (index, κ, evenLeaf pair)))
            have ho := h (.inr (.inl (index, κ, oddLeaf pair)))
            simp only [Compatible, secretHalf, secretDerivation, leafPair_evenLeaf,
              leafPair_oddLeaf] at he ho
            rw [hashHalf_even (by simp only [evenLeaf]; omega)] at he
            rw [hashHalf_odd (by simp only [oddLeaf]; omega)] at ho
            simp only [derivedOutput, he, ho, joinHalves_halves]
        | inr level => exact h (.inr (.inr level))

/-! ### Programming the cache -/

def parameterInput (seed : MasterSeed) : HashInput := keygenHashInput 0 .parameter seed

/-- The input of a derivation at the public parameter of the material. -/
def derivationInput (seed : MasterSeed) (material : Material) (derivation : Derivation) : HashInput :=
  keygenHashInput (parameter material) (derivationDomain derivation) seed

/-- The input of the derivation that gives a secret. The two chains of a pair have the same input. -/
def secretInput (seed : MasterSeed) (material : Material) (position : SecretPosition) : HashInput :=
  keygenHashInput (parameter material) (secretDomain position) seed

theorem secretInput_eq (seed : MasterSeed) (material : Material) (position : SecretPosition) :
    secretInput seed material position = derivationInput seed material (secretDerivation position) := rfl

theorem derivationInput_injective (seed : MasterSeed) (material : Material) :
    Function.Injective (derivationInput seed material) := by
  intro left right h
  exact derivationDomain_injective (keygenInput_injective h).2.1

theorem derivationInput_ne_parameterInput (seed : MasterSeed) (material : Material)
    (derivation : Derivation) : derivationInput seed material derivation ≠ parameterInput seed := by
  intro h
  exact derivationDomain_ne_parameter derivation (keygenInput_injective h).2.1

/-- Program the complete derivation table over a base cache. This definition overwrites its
specified entries; a later lemma explicitly requires those entries fresh to preserve the base. -/
noncomputable def programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) : QueryCache HashSpec := fun input =>
  if input = parameterInput seed then some material.1
  else if h : ∃ derivation, input = derivationInput seed material derivation then
    some (derivedOutput material.2 (Classical.choose h))
  else base input

theorem programCache_parameter (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (parameterInput seed) = some material.1 := by
  simp [programCache]

theorem programCache_derivation (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (derivation : Derivation) :
    programCache base seed material (derivationInput seed material derivation) =
      some (derivedOutput material.2 derivation) := by
  rw [programCache, if_neg (derivationInput_ne_parameterInput seed material derivation)]
  have h : ∃ other, derivationInput seed material derivation = derivationInput seed material other :=
    ⟨derivation, rfl⟩
  rw [dif_pos h]
  exact congrArg (fun p => some (derivedOutput material.2 p))
    (derivationInput_injective seed material (Classical.choose_spec h).symm)

/-- Precisely the addressed parameter/secret entries are programmed; other seed-bearing inputs
are left alone, including derivations under any other public parameter. -/
theorem programCache_other (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hparameter : input ≠ parameterInput seed)
    (hsecret : ∀ position, input ≠ secretInput seed material position) :
    programCache base seed material input = base input := by
  simp only [programCache, hparameter, ↓reduceIte]
  refine dif_neg ?_
  rintro ⟨derivation, hd⟩
  obtain ⟨position, rfl⟩ := secretDerivation_surjective derivation
  exact hsecret position hd

def AgreeOutsideSeed (seed : MasterSeed) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬SeedGuess.SeedHit input seed → left input = right input

/-- Programming cannot affect an input that fails the exact hidden-seed predicate. -/
theorem programCache_agreeOutside (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    AgreeOutsideSeed seed (programCache base seed material) base := by
  intro input hnot
  apply programCache_other
  · intro heq
    exact hnot ⟨0, .parameter, heq.symm⟩
  · intro position heq
    exact hnot ⟨parameter material, secretDomain position, heq.symm⟩

/-- The concrete verifier never touches a programmed derivation entry. -/
theorem programCache_verifier (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    programCache base seed material (tweakableHashInput p domain payload) =
      base (tweakableHashInput p domain payload) := by
  apply programCache_agreeOutside
  rintro ⟨p', domain', heq⟩
  exact keygenInput_ne_hashInput p' p domain' domain seed payload heq

/-- An answer function extends the complete prepared derivation table. -/
def PreparedAgreement (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) : Prop :=
  f (parameterInput seed) = material.1 ∧
    ∀ derivation, f (derivationInput seed material derivation) = derivedOutput material.2 derivation

/-- **Every secret reads the sampled table at the actual public parameter**: the half of the answer
of its derivation that the signer takes is the first half of the material's value at that secret. -/
theorem secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    secretHalf position (f (secretInput seed material position)) = truncateHash (material.2 position) := by
  rw [secretInput_eq, h.2, secretHalf_derivedOutput]

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
