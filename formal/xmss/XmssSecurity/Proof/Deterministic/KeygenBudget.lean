import XmssSecurity.Proof.Seeded.KeygenBudget
import XmssSecurity.Proof.Deterministic.GameExpansion

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def deterministicGameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (parameter, secret) ← liftM (deriveParametersAndSecrets seed)
  deterministicGameAfterSecrets adversary seed parameter secret

theorem gameCore_deterministic_split (adversary : Adversary) :
    gameCore scheme adversary = ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
      deterministicGameAfterSeed adversary) := gameCore_deterministic_eq adversary

theorem deterministicAfterSeed_first_query (adversary : Adversary) (seed : MasterSeed) :
    deterministicGameAfterSeed adversary seed = (do
      let output ← liftM (OracleWorld.query (.inr (keygenHashInput 0 .parameter seed)))
      let secret ← liftM (deriveChainSecrets (truncateHash output) seed)
      deterministicGameAfterSecrets adversary seed (truncateHash output) secret) := by
  simp only [deterministicGameAfterSeed, deriveParametersAndSecrets, deriveKey, Concrete.oracleHash, liftM_bind,
    liftM_pure, bind_assoc, pure_bind]
  rfl

attribute [local irreducible] deterministicGameAfterSeed sampleMasterSeed deriveChainSecrets deterministicGameAfterSecrets
  derivationCache drawChainOutputs signingDerivationCache prepareRandomizers sampleRandomizerOutputs tableGameAfterSecrets

theorem hashQueryBound_after_deterministic_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    1 ≤ q ∧ HashQueryBound (deterministicGameAfterSecrets adversary seed (truncateHash parameterOutput) (outputSecrets outputs))
      (derivationCache seed parameterOutput outputs) (q - 1) := by
  rw [hasHashQueryBound_iff, gameCore_deterministic_split] at hbound
  have hs : seed ∈ support sampleMasterSeed := by
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hseed : HashQueryBound (deterministicGameAfterSeed adversary seed) ∅ q :=
    hashQueryBound_of_sampling_bind sampleMasterSeed (deterministicGameAfterSeed adversary) ∅ q hbound seed hs
  rw [deterministicAfterSeed_first_query] at hseed
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

theorem hashQueryBound_after_signing_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    1 ≤ q ∧ HashQueryBound
      (tableGameAfterSecrets adversary (truncateHash parameterOutput) (outputSecrets outputs) randomizers)
      (signingDerivationCache seed parameterOutput outputs randomizers) (q - 1) := by
  have hfirst := hashQueryBound_after_deterministic_derivation adversary q hbound seed parameterOutput outputs
  have hrandomizers : (randomizers, signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ romImpl (liftM (prepareRandomizers (truncateHash parameterOutput) seed) :
        OracleComp OracleWorld _)).run (derivationCache seed parameterOutput outputs)) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right,
      mem_support_iff_of_evalDist_eq (evalDist_prepareRandomizers seed parameterOutput outputs), support_map]
    refine ⟨randomizers, ?_, rfl⟩
    rw [mem_support_iff]
    unfold sampleRandomizerOutputs
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hprepared := hashQueryBound_after_preparation _ _ _ _ hfirst.2 _ hrandomizers
  exact ⟨hfirst.1, (erases_deterministicGameAfterSecrets _ seed _ _ randomizers
    (signingDerivationCache_randomizer seed parameterOutput outputs randomizers) adversary).hashQueryBound
      _ le_rfl _ hprepared⟩

def HasTableBudget (adversary : Adversary) (q : Nat) : Prop :=
  ∀ (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs),
    HashQueryBound (tableGameAfterSecrets adversary (truncateHash parameterOutput) (outputSecrets outputs) randomizers) ∅ q

theorem tableBudget_from_deterministic (adversary : Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : HasHashQueryBound scheme adversary q) :
    HasTableBudget adversary (q - 1) := by
  intro parameterOutput outputs randomizers
  exact hashQueryBound_of_seed_caches _ (q - 1) []
    (fun seed => signingDerivationCache seed parameterOutput outputs randomizers) ∅
    (by simpa using lt_of_le_of_lt (Nat.sub_le q 1) hsmall)
    (fun seed _ => signingDerivationCache_agreeOutside seed parameterOutput outputs randomizers)
    (fun seed _ => (hashQueryBound_after_signing_derivation adversary q hbound seed parameterOutput outputs randomizers).2)

end XmssSecurity.Seeded
