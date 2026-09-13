import XmssSecurity.Proof.Deterministic.KeygenBudget

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev SigningMaterial := HashOutput × ChainOutputs × RandomizerOutputs

noncomputable def drawSigningMaterial : ProbComp SigningMaterial := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← ($ᵗ ChainOutputs)
  let randomizers ← sampleRandomizerOutputs
  return (parameterOutput, outputs, randomizers)

noncomputable def independentTableGame (adversary : Adversary) : ProbComp Bool := do
  let material ← drawSigningMaterial
  (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run' ∅

theorem evalDist_programmedDeterministicGame_seed_last (adversary : Adversary) :
    𝒟[programmedDeterministicGame adversary] = 𝒟[do
      let material ← drawSigningMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] := by
  have heq : programmedDeterministicGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawSigningMaterial
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)) := by
    simp only [programmedDeterministicGame, drawSigningMaterial, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

theorem forgeAdvantage_deterministic_le_table (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget adversary q) :
    forgeAdvantage scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | drawSigningMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | drawSigningMaterial >>= fun material =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_le _
    (fun seed => signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
    (fun seed => signingDerivationCache_agreeOutside seed _ _ _) q
    (hbound material.1 material.2.1 material.2.2) (fun value => value = true)

end XmssSecurity.Seeded
