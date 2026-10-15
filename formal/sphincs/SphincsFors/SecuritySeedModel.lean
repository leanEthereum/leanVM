import SphincsFors.SecuritySeedGuess
import SphincsFors.Recovery

/-!
Seed-independent prepared key material and its exact full-output oracle programming interface.
The table includes all OTS and FORS derivations and every possible surrogate. Only the parameter
derivation uses the zero public parameter; all other entries use its truncated sampled output.
The material holds one uniform 256-bit value per derived value, of which the low half is the
value. One hash of the seed gives two chain starts or two FORS secrets, so the programmed answer of
that hash is the two low halves joined (`mix`); `mix` is an involution of the table, hence the
programmed answers are independent uniform outputs.
This module defines and verifies the programming operation. It does not assume that an existing
honest-game cache is independent of the master seed or already has the prepared distribution.
-/

open OracleComp OracleSpec

namespace SphincsFors.Security.SeedModel

attribute [local instance] Classical.propDecidable

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev ForsPosition := Index × FtsTree × FtsLeaf
abbrev SecretPosition := OtsPosition ⊕ (ForsPosition ⊕ Fin totalHeight)
abbrev SecretOutputs := SecretPosition → HashOutput

/-- One 256-bit value per derived value: its low 128 bits are the value, and its high 128 bits
are not used by the scheme. -/
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

def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (.inl (index, tree, leaf)) => .fts index tree leaf
  | .inr (.inr level) => .surrogate level

theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  cases left with
  | inl left =>
      rcases left with ⟨lay, tree, leaf, chain⟩
      cases right with
      | inl right => rcases right with ⟨lay', tree', leaf', chain'⟩; simpa [secretDomain] using h
      | inr right => cases right <;> cases h
  | inr left =>
      cases left with
      | inl left =>
          rcases left with ⟨index, tree, leaf⟩
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => rcases right with ⟨index', tree', leaf'⟩; simpa [secretDomain] using h
              | inr right => cases h
      | inr left =>
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => cases h
              | inr right => simpa [secretDomain] using h

theorem secretDomain_ne_parameter (position : SecretPosition) : secretDomain position ≠ .parameter := by
  cases position with
  | inl p => rcases p with ⟨_, _, _, _⟩; simp [secretDomain]
  | inr p => cases p <;> simp [secretDomain]

/-- The first value of the hash that derives the value at `position`: the even chain start, the
even FORS secret; a surrogate has its own hash. -/
def firstOf : SecretPosition → SecretPosition
  | .inl (lay, tree, leaf, chain) =>
      .inl (lay, tree, leaf, ⟨2 * (chain.val / 2), Nat.lt_of_le_of_lt (Nat.mul_div_le _ 2) chain.isLt⟩)
  | .inr (.inl (index, tree, leaf)) =>
      .inr (.inl (index, tree, ⟨2 * (leaf.val / 2), Nat.lt_of_le_of_lt (Nat.mul_div_le _ 2) leaf.isLt⟩))
  | .inr (.inr level) => .inr (.inr level)

/-- The second value of that hash: the odd chain start, the odd FORS secret. -/
def secondOf : SecretPosition → SecretPosition
  | .inl (lay, tree, leaf, chain) =>
      .inl (lay, tree, leaf, ⟨2 * (chain.val / 2) + 1, by
        have := chain.isLt; simp only [numChains] at *; omega⟩)
  | .inr (.inl (index, tree, leaf)) =>
      .inr (.inl (index, tree, ⟨2 * (leaf.val / 2) + 1, by
        have := leaf.isLt; simp only [ftsTreeHeight] at *; omega⟩))
  | .inr (.inr level) => .inr (.inr level)

/-- The value is the second half of its hash. -/
def isSecond (position : SecretPosition) : Bool := (secretDomain position).second

/-- The hash of the value gives two values. -/
def Paired : SecretPosition → Bool
  | .inr (.inr _) => false
  | _ => true

theorem secretDomain_firstOf (position : SecretPosition) :
    secretDomain (firstOf position) = pairDomain (secretDomain position) := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level <;> rfl

theorem firstOf_of_not_second {position : SecretPosition} (h : isSecond position = false) :
    firstOf position = position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp only [isSecond, secretDomain, KeygenDomain.second, beq_eq_false_iff_ne] at h
    simp only [firstOf, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp only [isSecond, secretDomain, KeygenDomain.second, beq_eq_false_iff_ne] at h
    simp only [firstOf, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · rfl

theorem secondOf_of_second {position : SecretPosition} (h : isSecond position = true) :
    secondOf position = position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp only [isSecond, secretDomain, KeygenDomain.second, beq_iff_eq] at h
    simp only [secondOf, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp only [isSecond, secretDomain, KeygenDomain.second, beq_iff_eq] at h
    simp only [secondOf, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp [isSecond, secretDomain, KeygenDomain.second] at h

theorem isSecond_firstOf (position : SecretPosition) : isSecond (firstOf position) = false := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level <;>
    simp [isSecond, firstOf, secretDomain, KeygenDomain.second]

theorem isSecond_secondOf {position : SecretPosition} (h : Paired position = true) :
    isSecond (secondOf position) = true := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp [isSecond, secondOf, secretDomain, KeygenDomain.second]
  · simp [isSecond, secondOf, secretDomain, KeygenDomain.second]
  · simp [Paired] at h

theorem paired_firstOf (position : SecretPosition) : Paired (firstOf position) = Paired position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level <;> rfl

theorem paired_secondOf (position : SecretPosition) : Paired (secondOf position) = Paired position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level <;> rfl

theorem firstOf_firstOf (position : SecretPosition) : firstOf (firstOf position) = firstOf position :=
  firstOf_of_not_second (isSecond_firstOf position)

theorem firstOf_secondOf (position : SecretPosition) : firstOf (secondOf position) = firstOf position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp only [firstOf, secondOf, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp only [firstOf, secondOf, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · rfl

theorem secondOf_firstOf (position : SecretPosition) : secondOf (firstOf position) = secondOf position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp only [firstOf, secondOf, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp only [firstOf, secondOf, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · rfl

theorem secondOf_secondOf (position : SecretPosition) : secondOf (secondOf position) = secondOf position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp only [secondOf, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · simp only [secondOf, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.ext_iff]
    omega
  · rfl

theorem firstOf_of_not_paired {position : SecretPosition} (h : Paired position = false) :
    firstOf position = position := by
  rcases position with ⟨lay, tree, leaf, chain⟩ | ⟨index, tree, leaf⟩ | level
  · simp [Paired] at h
  · simp [Paired] at h
  · rfl

/-- The answers of the derivation hashes, indexed by the first value of each hash: the low halves of
the two values the hash gives, joined. At the second value of a hash the table keeps the two unused
high halves, which makes the map an involution. -/
noncomputable def mix (outputs : SecretOutputs) : SecretOutputs := fun position =>
  if Paired position then
    if isSecond position then
      joinHalves (truncateHashHigh (outputs (firstOf position)))
        (truncateHashHigh (outputs (secondOf position)))
    else
      joinHalves (truncateHash (outputs (firstOf position)))
        (truncateHash (outputs (secondOf position)))
  else outputs position

theorem mix_firstOf (outputs : SecretOutputs) {position : SecretPosition} (h : Paired position = true) :
    mix outputs (firstOf position) =
      joinHalves (truncateHash (outputs (firstOf position)))
        (truncateHash (outputs (secondOf position))) := by
  simp only [mix, paired_firstOf, h, isSecond_firstOf, firstOf_firstOf, secondOf_firstOf, if_true]
  rfl

theorem mix_secondOf (outputs : SecretOutputs) {position : SecretPosition} (h : Paired position = true) :
    mix outputs (secondOf position) =
      joinHalves (truncateHashHigh (outputs (firstOf position)))
        (truncateHashHigh (outputs (secondOf position))) := by
  simp only [mix, paired_secondOf, h, isSecond_secondOf h, firstOf_secondOf, secondOf_secondOf,
    if_true]

theorem mix_involutive : Function.Involutive mix := by
  intro outputs
  funext position
  cases hp : Paired position with
  | false => simp only [mix, hp, Bool.false_eq_true, if_false]
  | true =>
      cases hs : isSecond position with
      | false =>
          have hfirst := firstOf_of_not_second hs
          conv_lhs => rw [mix, if_pos hp, hs, if_neg (by simp)]
          rw [mix_firstOf outputs hp, mix_secondOf outputs hp, truncateHash_joinHalves,
            truncateHash_joinHalves, hfirst, joinHalves_halves]
      | true =>
          have hsecond := secondOf_of_second hs
          conv_lhs => rw [mix, if_pos hp, hs, if_pos rfl]
          rw [mix_firstOf outputs hp, mix_secondOf outputs hp, truncateHashHigh_joinHalves,
            truncateHashHigh_joinHalves, hsecond, joinHalves_halves]

/-- The answer of the hash that derives the value at `position`. -/
noncomputable def pairOutput (outputs : SecretOutputs) (position : SecretPosition) : HashOutput :=
  mix outputs (firstOf position)

/-- The half of the programmed answer that is the value at `position` is the low half of the
material at `position`. -/
theorem secretHalf_pairOutput (outputs : SecretOutputs) (position : SecretPosition) :
    secretHalf (secretDomain position) (pairOutput outputs position) =
      truncateHash (outputs position) := by
  unfold pairOutput
  cases hp : Paired position with
  | false =>
      have hfirst := firstOf_of_not_paired hp
      have hs : (secretDomain position).second = false := by
        rw [← hfirst]; exact isSecond_firstOf position
      rw [secretHalf_of_not_second hs, hfirst, mix, hp]
      rfl
  | true =>
      rw [mix_firstOf outputs hp]
      cases hs : isSecond position with
      | false =>
          rw [secretHalf_of_not_second hs, truncateHash_joinHalves, firstOf_of_not_second hs]
      | true =>
          rw [secretHalf_of_second hs, truncateHashHigh_joinHalves, secondOf_of_second hs]

def parameterInput (seed : MasterSeed) : HashInput := keygenHashInput 0 .parameter seed

def secretInput (seed : MasterSeed) (material : Material) (position : SecretPosition) : HashInput :=
  keygenHashInput (parameter material) (secretDomain position) seed

/-- The two values of one hash have the same derivation input. -/
theorem secretInput_firstOf (seed : MasterSeed) (material : Material) (position : SecretPosition) :
    secretInput seed material (firstOf position) = secretInput seed material position := by
  rw [secretInput, secretDomain_firstOf, keygenHashInput_pairDomain]
  rfl

/-- Two values with the same derivation input are the two values of one hash. -/
theorem firstOf_eq_of_secretInput_eq {seed : MasterSeed} {material : Material}
    {left right : SecretPosition}
    (h : secretInput seed material left = secretInput seed material right) :
    firstOf left = firstOf right := by
  apply secretDomain_injective
  rw [secretDomain_firstOf, secretDomain_firstOf]
  exact (keygenInput_injective h).2.1

theorem secretInput_ne_parameterInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ parameterInput seed := by
  intro h
  have hpair := (keygenInput_injective h).2.1
  rw [← secretDomain_firstOf] at hpair
  exact secretDomain_ne_parameter _ hpair

/-- Program the complete derivation table over a base cache: the parameter hash, and every hash of
a derived value, answered with `pairOutput`. This definition overwrites its specified entries; a
later lemma explicitly requires those entries fresh to preserve the base. -/
noncomputable def programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) : QueryCache HashSpec := fun input =>
  if input = parameterInput seed then some material.1
  else if h : ∃ position, input = secretInput seed material position then
    some (pairOutput material.2 (Classical.choose h))
  else base input

theorem programCache_parameter (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (parameterInput seed) = some material.1 := by
  simp [programCache]

theorem programCache_secret (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (position : SecretPosition) :
    programCache base seed material (secretInput seed material position) =
      some (pairOutput material.2 position) := by
  rw [programCache, if_neg (secretInput_ne_parameterInput seed material position)]
  have h : ∃ other, secretInput seed material position = secretInput seed material other := ⟨position, rfl⟩
  rw [dif_pos h]
  exact congrArg (fun p => some (mix material.2 p))
    (firstOf_eq_of_secretInput_eq (Classical.choose_spec h)).symm

/-- Precisely the addressed parameter/secret entries are programmed; other seed-bearing inputs
are left alone, including derivations under any other public parameter. -/
theorem programCache_other (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hparameter : input ≠ parameterInput seed)
    (hsecret : ∀ position, input ≠ secretInput seed material position) :
    programCache base seed material input = base input := by
  simp only [programCache, hparameter, ↓reduceIte]
  exact dif_neg (by simpa only [not_exists] using hsecret)

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
    ∀ position, f (secretInput seed material position) = pairOutput material.2 position

/-- A total oracle implementing the prepared table, with the supplied oracle everywhere else. -/
noncomputable def preparedOracle (fallback : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) : QueryImpl HashSpec Id := fun input =>
  (programCache ∅ seed material input).getD (fallback input)

/-- Every OTS/FORS/surrogate derivation reads the sampled table at the actual public parameter. -/
theorem eval_secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    evalWithAnswerFn f (deriveKey (parameter material) (secretDomain position) seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 position) := by
  rw [Completeness.eval_deriveKey]
  exact (congrArg (secretHalf (secretDomain position)) (h.2 position)).trans
    (secretHalf_pairOutput material.2 position)

end SphincsFors.Security.SeedModel
