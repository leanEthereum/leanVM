import XmssSecurity.Proof.Deterministic.RequestSampling
import XmssSecurity.Proof.Deterministic.ReferenceSource
import XmssSecurity.Proof.Deterministic.MemoTable
import XmssSecurity.Proof.Deterministic.CostState

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableSign

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : ChainSecrets) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (worldHandler hash) (gameAfterSecrets (memoAdversary adversary)
        parameter outputs)).run state] := by
  unfold tableGameAfterSecrets gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  have hleft (randomizers) := runSigning_sourceGame randomizers (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    ⟨result.1.1, parameter⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    (sourceGame ⟨result.1.1, parameter⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem hashQueryBound_reference_afterSecrets (adversary : Adversary) (parameterOutput : HashOutput)
    (outputs : ChainSecrets) (q : Nat)
    (hbound : ∀ randomizers, HashQueryBound
      (tableGameAfterSecrets (memoAdversary adversary) (truncateHash parameterOutput) outputs randomizers) ∅ q) :
    HashQueryBound (gameAfterSecrets (memoAdversary adversary)
      (truncateHash parameterOutput) outputs) ∅ q := by
  rw [hashQueryBound_iff_costState]
  intro result hresult
  rw [← mem_support_iff_of_evalDist_eq (evalDist_tableGameAfterSecrets_memo costHash adversary
    (truncateHash parameterOutput) outputs (∅, 0)), mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact (hashQueryBound_iff_costState _ ∅ q).1 (hbound randomizers) result hresult

theorem referenceBudget_from_table (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget (memoAdversary adversary) q) :
    HasHashQueryBound Concrete.scheme (memoAdversary adversary) q := by
  rw [hasHashQueryBound_iff, gameCore_independent_eq]
  have htail (parameter : PublicParameter) (secret : ChainSecrets) :
      HashQueryBound (gameAfterSecrets (memoAdversary adversary) parameter secret) ∅ q := by
    have h := hashQueryBound_reference_afterSecrets adversary (Rom.hashOutputEquivDigestPair.symm (0, parameter))
      secret q (fun randomizers => by
        simpa only [truncate_from_halves, outputSecrets_from_halves] using
          hbound (Rom.hashOutputEquivDigestPair.symm (0, parameter))
            (chainOutputHalves.symm ((fun _ _ => 0), secret)) randomizers)
    simpa only [truncate_from_halves] using h
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
