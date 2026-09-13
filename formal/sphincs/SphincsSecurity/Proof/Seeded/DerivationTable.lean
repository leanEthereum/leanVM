import SphincsSecurity.Proof.Seeded.FiniteTable
import SphincsSecurity.Proof.Seeded.KeyDerivation
import SphincsSecurity.Proof.Seeded.SeedGuessing
import SphincsSecurity.Proof.Seeded.CacheCoupling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev FtsPosition := Index × FtsTree × FtsLeaf
abbrev SecretPosition := OtsPosition ⊕ FtsPosition
abbrev SecretOutputs := SecretPosition → HashOutput
abbrev SecretValues := SecretPosition → Digest

noncomputable opaque secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

noncomputable def sampleSecretOutputs : ProbComp SecretOutputs := $ᵗ SecretOutputs

def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (index, tree, leaf) => .fts index tree leaf

theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  cases left with
  | inl left =>
      rcases left with ⟨lay, tree, leaf, chain⟩
      cases right <;> simp_all [secretDomain]
  | inr left =>
      rcases left with ⟨index, tree, leaf⟩
      cases right <;> simp_all [secretDomain]

def secretInputs (parameter : PublicParameter) (seed : MasterSeed) (position : SecretPosition) : HashInput :=
  keygenHashInput parameter (secretDomain position) seed

theorem secretInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (secretInputs parameter seed) := by
  intro left right h
  exact secretDomain_injective (keygenHashInput_injective h).2.1

def parameterCache (seed : MasterSeed) (output : HashOutput) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (keygenHashInput 0 .parameter seed) output

theorem parameterCache_secret_fresh (seed : MasterSeed) (output : HashOutput)
    (parameter : PublicParameter) (position : SecretPosition) :
    parameterCache seed output (secretInputs parameter seed position) = none := by
  apply QueryCache.cacheQuery_of_ne
  intro h
  have hd := (keygenHashInput_injective h).2.1
  cases position <;> cases hd

noncomputable def derivationCache (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) : QueryCache HashSpec :=
  cacheTable (parameterCache seed parameterOutput) (secretInputs (truncateHash parameterOutput) seed) outputs

theorem derivationCache_secret (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (position : SecretPosition) :
    derivationCache seed parameterOutput outputs (secretInputs (truncateHash parameterOutput) seed position) =
      some (outputs position) :=
  cacheTable_apply _ _ (secretInputs_injective _ seed) outputs position

theorem derivationCache_agreeOutside (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) :
    AgreeOutside (fun input => SeedHit input seed) (derivationCache seed parameterOutput outputs) ∅ := by
  intro input hinput
  unfold derivationCache
  rw [cacheTable_apply_of_not_mem]
  · apply QueryCache.cacheQuery_of_ne
    intro heq
    exact hinput ⟨0, .parameter, heq.symm⟩
  · intro position heq
    exact hinput ⟨truncateHash parameterOutput, secretDomain position, heq.symm⟩

noncomputable def prepareSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec SecretOutputs := queryTable (secretInputs parameter seed)

theorem evalDist_prepareSecrets (seed : MasterSeed) (parameterOutput : HashOutput) :
    𝒟[(simulateQ randomOracle (prepareSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] =
        𝒟[(fun outputs => (outputs, derivationCache seed parameterOutput outputs)) <$> sampleSecretOutputs] :=
  evalDist_queryTable_fresh _ (secretInputs_injective _ seed) _ (parameterCache_secret_fresh seed parameterOutput _)

end SphincsSecurity.Seeded
