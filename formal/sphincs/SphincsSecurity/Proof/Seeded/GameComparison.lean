import SphincsSecurity.Proof.Seeded.KeygenBudget

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev KeyMaterial := PublicParameter × Secrets × Digest × Secrets

noncomputable def drawKeyMaterial : ProbComp KeyMaterial := do
  let parameter ← Concrete.sampleParameter
  let secret ← sampleSecrets
  let parameterHigh ← $ᵗ Digest
  let secretHigh ← sampleSecrets
  return (parameter, secret, parameterHigh, secretHigh)

noncomputable def materialCache (seed : MasterSeed) (material : KeyMaterial) : QueryCache HashSpec :=
  programmedCache seed material.1 material.2.1 material.2.2.1 material.2.2.2

theorem evalDist_programmedGame_seed_last (adversary : Adversary) :
    𝒟[programmedGame adversary] = 𝒟[do
      let material ← drawKeyMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary material.1 material.2.1.1 material.2.1.2)).run'
        (materialCache seed material)] := by
  have heq : programmedGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawKeyMaterial
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary material.1 material.2.1.1 material.2.1.2)).run'
        (materialCache seed material)) := by
    simp only [programmedGame, drawKeyMaterial, materialCache, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

theorem gameCore_independent_eq (adversary : Adversary) :
    gameCore Concrete.scheme adversary = (do
      let parameter ← liftM Concrete.sampleParameter
      let secret ← liftM sampleSecrets
      Concrete.gameAfterSecrets adversary parameter secret.1 secret.2) := by
  rw [Concrete.gameCore_eq_secrets]
  simp only [sampleSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

theorem evalDist_independentGame_material (adversary : Adversary) :
    𝒟[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] = 𝒟[do
      let material ← drawKeyMaterial
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary material.1 material.2.1.1 material.2.1.2)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  unfold drawKeyMaterial
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro parameter
  rw [run'_lift_sample_bind]
  apply evalDist_bind_congr'
  intro secret
  apply evalDist_ext
  intro value
  simp

theorem hashQueryBound_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (parameter : PublicParameter) (secret : Secrets) :
    HashQueryBound (Concrete.gameAfterSecrets adversary parameter secret.1 secret.2) ∅ q := by
  apply Concrete.hashQueryBound_gameAfterSecrets adversary q hbound
  · rw [mem_support_iff]
    unfold Concrete.sampleParameter
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [mem_support_iff]
    unfold Concrete.sampleOtsSecrets
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [mem_support_iff]
    unfold Concrete.sampleFtsSecrets
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- The seeded game differs from the independent game by at most one 256-bit guess per hash call. -/
theorem forgeAdvantage_seeded_le_of_independent_budget (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme adversary +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage
  simp only [probOutput_def, evalDist_gameCore_eq_programmed,
    evalDist_programmedGame_seed_last, evalDist_independentGame_material]
  change Pr[= true | drawKeyMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary material.1 material.2.1.1 material.2.1.2)).run'
        (materialCache seed material)] ≤
    Pr[= true | drawKeyMaterial >>= fun material =>
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary material.1 material.2.1.1 material.2.1.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_le _ (fun seed => materialCache seed material) ∅
    (fun seed => programmedCache_agreeOutside seed _ _ _ _) q
    (hashQueryBound_gameAfterSecrets adversary q hbound _ _) (fun value => value = true)

end SphincsSecurity.Seeded
