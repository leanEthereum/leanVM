import XmssSecurity.Proof.Deterministic.TableToReference
import XmssSecurity.Proof.Seeded.GameComparison

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] gameAfterSecrets

theorem evalDist_parameter_continuation {α : Type} (next : PublicParameter → ProbComp α) :
    𝒟[do let output ← ($ᵗ HashOutput : ProbComp HashOutput); next (truncateHash output)] =
      𝒟[do let parameter ← Concrete.samplePublicParameter; next parameter] := by
  have h := Rom.evalDist_truncate_uniformHashOutput.trans evalDist_samplePublicParameter.symm
  have heq := congrArg (fun distribution => distribution >>= fun parameter => 𝒟[next parameter]) h
  simpa only [evalDist_bind, evalDist_map, bind_map_left, bind_pure_comp, bind_assoc, pure_bind] using heq

theorem evalDist_secrets_continuation {α : Type} (next : ChainSecrets → ProbComp α) :
    𝒟[do let outputs ← ($ᵗ ChainOutputs); next (outputSecrets outputs)] =
      𝒟[do let secret ← Concrete.sampleSecret; next secret] := by
  conv_rhs => rw [evalDist_bind, evalDist_sampleSecret, ← evalDist_bind]
  rw [evalDist_bind, evalDist_chainOutputs_from_halves, ← evalDist_bind]
  simp only [bind_assoc, pure_bind, outputSecrets_from_halves]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  apply evalDist_ext
  intro value
  simp

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary (truncateHash parameterOutput)
        (outputSecrets outputs))).run' ∅] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ ChainOutputs)
    (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅]
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒟[independentTableGame (memoAdversary adversary)] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme (memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (truncateHash parameterOutput) (outputSecrets outputs) ∅
  rw [worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalDist_map, evalDist_bind, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget adversary q) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table adversary q hbound).trans (add_le_add hmemo le_rfl)

end XmssSecurity.Seeded
