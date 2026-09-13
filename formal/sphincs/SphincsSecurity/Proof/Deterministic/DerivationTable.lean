import SphincsSecurity.Proof.Seeded.DerivationTable

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev RandomizerPosition := Message × BitVec 32
abbrev RandomizerOutputs := RandomizerPosition → HashOutput

noncomputable opaque randomizerOutputsSampleableType : SampleableType RandomizerOutputs :=
  SampleableType.ofFintype RandomizerOutputs

noncomputable local instance : SampleableType RandomizerOutputs := randomizerOutputsSampleableType

noncomputable def sampleRandomizerOutputs : ProbComp RandomizerOutputs := $ᵗ RandomizerOutputs

def randomizerInputs (parameter : PublicParameter) (seed : MasterSeed) (position : RandomizerPosition) : HashInput :=
  randomizerHashInput parameter seed position.1 position.2

theorem randomizerInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (randomizerInputs parameter seed) := by
  intro left right h
  have heq := randomizerHashInput_injective h
  exact Prod.ext heq.2.2.1 heq.2.2.2

theorem derivationCache_randomizer_fresh (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (position : RandomizerPosition) :
    derivationCache seed parameterOutput outputs
      (randomizerInputs (truncateHash parameterOutput) seed position) = none := by
  unfold derivationCache
  rw [cacheTable_apply_of_not_mem]
  · exact QueryCache.cacheQuery_of_ne _ _
      (randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ .parameter)
  · intro secret
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ (secretDomain secret)

noncomputable def signingDerivationCache (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) : QueryCache HashSpec :=
  cacheTable (derivationCache seed parameterOutput outputs)
    (randomizerInputs (truncateHash parameterOutput) seed) randomizers

theorem signingDerivationCache_randomizer (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) (position : RandomizerPosition) :
    signingDerivationCache seed parameterOutput outputs randomizers
      (randomizerInputs (truncateHash parameterOutput) seed position) = some (randomizers position) :=
  cacheTable_apply _ _ (randomizerInputs_injective _ _) _ _

theorem signingDerivationCache_secret (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) (position : SecretPosition) :
    signingDerivationCache seed parameterOutput outputs randomizers
      (secretInputs (truncateHash parameterOutput) seed position) = some (outputs position) := by
  unfold signingDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · exact derivationCache_secret _ _ _ _
  · intro randomizer
    exact (randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ (secretDomain position)).symm

theorem signingDerivationCache_agreeOutside (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    AgreeOutside (fun input => SeedHit input seed)
      (signingDerivationCache seed parameterOutput outputs randomizers) ∅ := by
  intro input hinput
  unfold signingDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · exact derivationCache_agreeOutside seed parameterOutput outputs input hinput
  · intro position heq
    exact hinput (heq.symm ▸ derivationSeedHit_randomizer (truncateHash parameterOutput) seed position.1 position.2)

noncomputable def prepareRandomizers (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec RandomizerOutputs := queryTable (randomizerInputs parameter seed)

theorem evalDist_prepareRandomizers (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) :
    𝒟[(simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)).run
      (derivationCache seed parameterOutput outputs)] =
        𝒟[(fun randomizers => (randomizers, signingDerivationCache seed parameterOutput outputs randomizers)) <$>
          sampleRandomizerOutputs] :=
  evalDist_queryTable_fresh _ (randomizerInputs_injective _ seed) _
    (derivationCache_randomizer_fresh seed parameterOutput outputs)

end SphincsSecurity.Seeded
