import XmssSecurity.Proof.Seeded.BudgetTransfer

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def gameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (parameter, secret) ← liftM (deriveParametersAndSecrets seed)
  gameAfterSecrets adversary parameter secret

theorem gameCore_seeded_split (adversary : Adversary) :
    gameCore scheme adversary = ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
      gameAfterSeed adversary) := gameCore_seeded_eq adversary

theorem afterSeed_first_query (adversary : Adversary) (seed : MasterSeed) :
    gameAfterSeed adversary seed = (do
      let output ← liftM (OracleWorld.query (.inr (keygenHashInput 0 .parameter seed)))
      let secret ← liftM (deriveChainSecrets (truncateHash output) seed)
      gameAfterSecrets adversary (truncateHash output) secret) := by
  simp only [gameAfterSeed, deriveParametersAndSecrets, deriveKey, Concrete.oracleHash, liftM_bind,
    liftM_pure, bind_assoc, pure_bind]
  rfl

attribute [local irreducible] gameAfterSeed sampleMasterSeed deriveChainSecrets gameAfterSecrets
  derivationCache drawChainOutputs

theorem mem_support_drawChainOutputs (outputs : ChainOutputs) : outputs ∈ support drawChainOutputs := by
  rw [mem_support_iff_evalDist_apply_ne_zero, evalDist_drawChainOutputs, ← probOutput_def,
    probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem hashQueryBound_after_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    1 ≤ q ∧ HashQueryBound (gameAfterSecrets adversary (truncateHash parameterOutput) (outputSecrets outputs))
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
  have houtputs : (outputSecrets outputs, derivationCache seed parameterOutput outputs) ∈
      support ((simulateQ romImpl (liftM (deriveChainSecrets (truncateHash parameterOutput) seed) :
        OracleComp OracleWorld _)).run (parameterCache seed parameterOutput)) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right, run_deriveChainSecrets, support_map]
    exact ⟨outputs, mem_support_drawChainOutputs outputs, rfl⟩
  exact ⟨hfirst.1, hashQueryBound_bind_right _ _ _ _ hfirst.2 _ houtputs⟩

theorem hashQueryBound_programmed_from_seeded (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : ChainSecrets) (parameterHigh : Digest)
    (secretHigh : ChainSecrets) :
    HashQueryBound (gameAfterSecrets adversary parameter secret)
      (programmedCache seed parameter secret parameterHigh secretHigh) (q - 1) := by
  have h := (hashQueryBound_after_derivation adversary q hbound seed
    (Rom.hashOutputEquivDigestPair.symm (parameterHigh, parameter))
    (chainOutputHalves.symm (secretHigh, secret))).2
  simpa only [programmedCache, truncate_from_halves, outputSecrets_from_halves] using h

theorem hashQueryBound_independent_from_seeded (adversary : Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : HasHashQueryBound scheme adversary q) :
    HasHashQueryBound Concrete.scheme adversary (q - 1) := by
  rw [hasHashQueryBound_iff, gameCore_independent_eq]
  have htail (parameter : PublicParameter) (secret : ChainSecrets) :
      HashQueryBound (gameAfterSecrets adversary parameter secret) ∅ (q - 1) := by
    exact hashQueryBound_of_programmed adversary parameter secret 0 (fun _ _ => 0) (q - 1)
      (lt_of_le_of_lt (Nat.sub_le _ _) hsmall)
      (fun seed => hashQueryBound_programmed_from_seeded adversary q hbound seed parameter secret 0 (fun _ _ => 0))
  intro result hresult
  simp only [countHashQueries_bind, countHashQueries_lift_prob, simulateQ_bind,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run,
    bind_map_left, map_bind, Nat.zero_add, bind_pure_comp, Functor.map_map,
    support_bind, Set.mem_iUnion, support_map] at hresult
  obtain ⟨parameter, _, secret, _, record, hrecord, rfl⟩ := hresult
  apply htail parameter secret record.1
  rw [StateT.run'_eq, support_map]
  exact ⟨record, hrecord, rfl⟩

end XmssSecurity.Seeded
