import SphincsSecurity.Proof.Deterministic.TableToReference
import SphincsSecurity.Proof.Seeded.GameComparison

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] Concrete.gameAfterSecrets

theorem evalDist_parameter_continuation {α : Type} (next : PublicParameter → ProbComp α) :
    𝒟[do let output ← ($ᵗ HashOutput : ProbComp HashOutput); next (truncateHash output)] =
      𝒟[do let parameter ← Concrete.sampleParameter; next parameter] := by
  have h := evalDist_truncateHash_uniform.trans evalDist_sampleParameter.symm
  have heq := congrArg (fun distribution => distribution >>= fun parameter => 𝒟[next parameter]) h
  simpa only [evalDist_bind, evalDist_map, bind_map_left, bind_pure_comp, bind_assoc, pure_bind] using heq

theorem evalDist_secrets_continuation {α : Type} (next : Secrets → ProbComp α) :
    𝒟[do let outputs ← sampleSecretOutputs; next (tableOts outputs, tableFts outputs)] =
      𝒟[do let secret ← sampleSecrets; next secret] := by
  rw [evalDist_bind, evalDist_secretOutputs_from_halves, ← evalDist_bind]
  simp only [bind_assoc, pure_bind, tableOts_from_halves, tableFts_from_halves]
  apply evalDist_bind_congr'
  intro secret
  apply evalDist_ext
  intro value
  simp

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← sampleSecretOutputs
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary (truncateHash parameterOutput)
        (tableOts outputs) (tableFts outputs))).run' ∅] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Concrete.sampleParameter
    let outputs ← sampleSecretOutputs
    (simulateQ romImpl (Concrete.gameAfterSecrets adversary parameter (tableOts outputs) (tableFts outputs))).run' ∅]
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← sampleSecretOutputs
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary parameter (tableOts outputs) (tableFts outputs))).run' ∅
  apply evalDist_bind_congr'
  intro parameter
  rw [run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (Concrete.gameAfterSecrets adversary parameter secret.1 secret.2)).run' ∅

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒟[independentTableGame (memoAdversary adversary)] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme (memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro parameterOutput
  apply evalDist_bind_congr'
  intro outputs
  have h := evalDist_tableGameAfterParameter_memo randomOracle adversary (truncateHash parameterOutput) outputs ∅
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

end SphincsSecurity.Seeded
