import SphincsSecurity.Proof.Seeded.GameErasure
import SphincsSecurity.Proof.Seeded.Presampling
import SphincsSecurity.Proof.Seeded.TableSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem run'_lift_hash_bind {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

theorem run_deriveParameter (seed : MasterSeed) :
    (simulateQ randomOracle (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)).run ∅ =
      (fun output => (truncateHash output, parameterCache seed output)) <$> ($ᵗ HashOutput) := by
  have hquery : (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) =
      truncateHash <$> (liftM (HashSpec.query (keygenHashInput 0 .parameter seed)) :
        OracleComp HashSpec HashOutput) := by
    simp only [deriveKey, Concrete.oracleHash, bind_pure_comp]
    rfl
  rw [hquery, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [Functor.map_map]
  rfl

theorem evalDist_gameAfterParameter_prepared (adversary : Adversary) (seed : MasterSeed)
    (parameterOutput : HashOutput) :
    𝒟[(simulateQ romImpl (gameAfterParameter adversary (truncateHash parameterOutput) seed)).run'
      (parameterCache seed parameterOutput)] =
      𝒟[do
        let outputs ← sampleSecretOutputs
        (simulateQ romImpl (Concrete.gameAfterSecrets adversary (truncateHash parameterOutput)
          (tableOts outputs) (tableFts outputs))).run' (derivationCache seed parameterOutput outputs)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareSecrets (truncateHash parameterOutput) seed) : OracleComp OracleWorld SecretOutputs)]
  rw [show simulateQ romImpl (liftM (prepareSecrets (truncateHash parameterOutput) seed) :
      OracleComp OracleWorld SecretOutputs) = simulateQ randomOracle (prepareSecrets (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareSecrets, ← evalDist_bind, bind_map_left]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  rw [(erases_gameAfterParameter _ _ seed outputs
    (derivationCache_secret seed parameterOutput outputs) adversary).evalDist_run _ le_rfl]

noncomputable def programmedGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let parameter ← Concrete.sampleParameter
  let secret ← sampleSecrets
  let parameterHigh ← $ᵗ Digest
  let secretHigh ← sampleSecrets
  (simulateQ romImpl (Concrete.gameAfterSecrets adversary parameter secret.1 secret.2)).run'
    (programmedCache seed parameter secret parameterHigh secretHigh)

theorem evalDist_gameCore_eq_programmed (adversary : Adversary) :
    𝒟[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] = 𝒟[programmedGame adversary] := by
  rw [gameCore_seeded_eq, run'_lift_sample_bind]
  unfold programmedGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  rw [run'_lift_hash_bind, run_deriveParameter, bind_map_left]
  trans 𝒟[do
    let parameterOutput ← $ᵗ HashOutput
    let outputs ← sampleSecretOutputs
    (simulateQ romImpl (Concrete.gameAfterSecrets adversary (truncateHash parameterOutput)
      (tableOts outputs) (tableFts outputs))).run' (derivationCache seed parameterOutput outputs)]
  · apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    exact evalDist_gameAfterParameter_prepared adversary seed
  · rw [evalDist_bind, evalDist_parameterOutput_from_halves, ← evalDist_bind]
    simp only [bind_assoc, pure_bind, truncate_from_halves]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro parameter
    trans 𝒟[do
      let parameterHigh ← $ᵗ Digest
      let secret ← sampleSecrets
      let secretHigh ← sampleSecrets
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary parameter secret.1 secret.2)).run'
        (programmedCache seed parameter secret parameterHigh secretHigh)]
    · apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameterHigh
      rw [evalDist_bind, evalDist_secretOutputs_from_halves, ← evalDist_bind]
      simp only [bind_assoc, pure_bind, tableOts_from_halves, tableFts_from_halves, programmedCache]
    · exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

end SphincsSecurity.Seeded
