import SphincsSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def gameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
  gameAfterParameter adversary parameter seed

theorem gameCore_seeded_split (adversary : Adversary) :
    gameCore scheme adversary = ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
      gameAfterSeed adversary) := gameCore_seeded_eq adversary

theorem afterSeed_first_query (adversary : Adversary) (seed : MasterSeed) :
    gameAfterSeed adversary seed = (do
      let output ← liftM (OracleWorld.query (.inr (keygenHashInput 0 .parameter seed)))
      gameAfterParameter adversary (truncateHash output) seed) := by
  simp only [gameAfterSeed, deriveKey, Concrete.oracleHash, liftM_bind,
    liftM_pure, bind_assoc, pure_bind]
  rfl

attribute [local irreducible] gameAfterSeed sampleMasterSeed gameAfterParameter
  Concrete.gameAfterSecrets derivationCache prepareSecrets sampleSecretOutputs

theorem mem_support_secretOutputs (outputs : SecretOutputs) : outputs ∈ support sampleSecretOutputs := by
  rw [mem_support_iff]
  unfold sampleSecretOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem hashQueryBound_after_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) :
    1 ≤ q ∧ HashQueryBound
      (Concrete.gameAfterSecrets adversary (truncateHash parameterOutput) (tableOts outputs) (tableFts outputs))
      (derivationCache seed parameterOutput outputs) (q - 1) := by
  rw [hasHashQueryBound_iff, gameCore_seeded_split] at hbound
  have hs : seed ∈ support sampleMasterSeed := by
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hseed : HashQueryBound (gameAfterSeed adversary seed) ∅ q :=
    hashQueryBound_of_sampling_bind sampleMasterSeed (gameAfterSeed adversary) ∅ q hbound seed hs
  rw [afterSeed_first_query] at hseed
  have hparameter : (parameterOutput, parameterCache seed parameterOutput) ∈
      support ((romImpl (.inr (keygenHashInput 0 .parameter seed))).run ∅) := by
    change (parameterOutput, parameterCache seed parameterOutput) ∈
      support ((randomOracle (spec := HashSpec) (keygenHashInput 0 .parameter seed)).run ∅)
    rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _), support_map]
    exact ⟨parameterOutput, mem_support_uniformSample _, rfl⟩
  have hfirst := hashQueryBound_query_bind _ _ ∅ q hseed _ hparameter
  have houtputs : (outputs, derivationCache seed parameterOutput outputs) ∈
      support ((simulateQ romImpl (liftM (prepareSecrets (truncateHash parameterOutput) seed) :
        OracleComp OracleWorld _)).run (parameterCache seed parameterOutput)) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right,
      mem_support_iff_of_evalDist_eq (evalDist_prepareSecrets seed parameterOutput), support_map]
    exact ⟨outputs, mem_support_secretOutputs outputs, rfl⟩
  have hprepared := hashQueryBound_after_preparation _ _ _ _ hfirst.2 _ houtputs
  exact ⟨hfirst.1, (erases_gameAfterParameter _ _ seed outputs
    (derivationCache_secret seed parameterOutput outputs) adversary).hashQueryBound _ le_rfl _ hprepared⟩

theorem hashQueryBound_programmed_from_seeded (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : Secrets) (parameterHigh : Digest) (secretHigh : Secrets) :
    HashQueryBound (Concrete.gameAfterSecrets adversary parameter secret.1 secret.2)
      (programmedCache seed parameter secret parameterHigh secretHigh) (q - 1) := by
  have h := (hashQueryBound_after_derivation adversary q hbound seed
    (outputHalves.symm (parameter, parameterHigh)) (secretHalves.symm (secret, secretHigh))).2
  simpa only [programmedCache, truncate_from_halves, tableOts_from_halves, tableFts_from_halves] using h

theorem programmedCache_agreeOutside (seed : MasterSeed) (parameter : PublicParameter)
    (secret : Secrets) (parameterHigh : Digest) (secretHigh : Secrets) :
    AgreeOutside (fun input => SeedHit input seed)
      (programmedCache seed parameter secret parameterHigh secretHigh) ∅ :=
  derivationCache_agreeOutside seed _ _

theorem hashQueryBound_independent_from_seeded (adversary : Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : HasHashQueryBound scheme adversary q) :
    HasHashQueryBound Concrete.scheme adversary (q - 1) := by
  rw [hasHashQueryBound_iff, Concrete.gameCore_eq_secrets]
  have htail (parameter : PublicParameter) (ots : OtsSecrets) (fts : FtsSecrets) :
      HashQueryBound (Concrete.gameAfterSecrets adversary parameter ots fts) ∅ (q - 1) := by
    let high : Secrets := (fun _ _ _ _ => 0, fun _ _ _ => 0)
    exact hashQueryBound_of_seed_caches _ (q - 1) []
      (fun seed => programmedCache seed parameter (ots, fts) 0 high) ∅
      (by simpa using lt_of_le_of_lt (Nat.sub_le q 1) hsmall)
      (fun seed _ => programmedCache_agreeOutside seed _ _ _ _)
      (fun seed _ => hashQueryBound_programmed_from_seeded adversary q hbound seed parameter (ots, fts) 0 high)
  intro result hresult
  simp only [countHashQueries_bind, countHashQueries_lift_prob, simulateQ_bind,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run,
    bind_map_left, map_bind, Nat.zero_add, bind_pure_comp, Functor.map_map,
    support_bind, Set.mem_iUnion, support_map] at hresult
  obtain ⟨parameter, _, ots, _, fts, _, record, hrecord, rfl⟩ := hresult
  apply htail parameter ots fts record.1
  rw [StateT.run'_eq, support_map]
  exact ⟨record, hrecord, rfl⟩

end SphincsSecurity.Seeded
