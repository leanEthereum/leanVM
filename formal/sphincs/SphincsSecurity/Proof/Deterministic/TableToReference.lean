import SphincsSecurity.Proof.Deterministic.RequestSampling
import SphincsSecurity.Proof.Deterministic.ReferenceSource
import SphincsSecurity.Proof.Deterministic.MemoTable
import SphincsSecurity.Proof.Deterministic.CostState

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] Concrete.treeRoot tableSign

theorem evalDist_tableGameAfterParameter_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : SecretOutputs) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterParameter (memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.gameAfterSecrets (memoAdversary adversary)
        parameter (tableOts outputs) (tableFts outputs))).run state] := by
  unfold tableGameAfterParameter Concrete.gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply evalDist_bind_congr'
  intro result
  change _ = 𝒟[(simulateQ (worldHandler hash) (gameRest Concrete.scheme (memoAdversary adversary)
    ⟨result.1, parameter⟩ (tableKey parameter result.1 outputs))).run result.2]
  have hleft (randomizers) := runSigning_sourceGame randomizers (tableKey parameter result.1 outputs)
    ⟨result.1, parameter⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (tableKey parameter result.1 outputs)
    (sourceGame ⟨result.1, parameter⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem hashQueryBound_reference_afterSecrets (adversary : Adversary) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (q : Nat)
    (hbound : ∀ randomizers, HashQueryBound
      (tableGameAfterParameter (memoAdversary adversary) (truncateHash parameterOutput) outputs randomizers) ∅ q) :
    HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary)
      (truncateHash parameterOutput) (tableOts outputs) (tableFts outputs)) ∅ q := by
  rw [hashQueryBound_iff_costState]
  intro result hresult
  rw [← mem_support_iff_of_evalDist_eq (evalDist_tableGameAfterParameter_memo costHash adversary
    (truncateHash parameterOutput) outputs (∅, 0)), mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact (hashQueryBound_iff_costState _ ∅ q).1 (hbound randomizers) result hresult

theorem referenceBudget_from_table (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget (memoAdversary adversary) q) :
    HasHashQueryBound Concrete.scheme (memoAdversary adversary) q := by
  rw [hasHashQueryBound_iff, Concrete.gameCore_eq_secrets]
  have htail (parameter : PublicParameter) (ots : OtsSecrets) (fts : FtsSecrets) :
      HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary) parameter ots fts) ∅ q := by
    let high : Secrets := (fun _ _ _ _ => 0, fun _ _ _ => 0)
    have h := hashQueryBound_reference_afterSecrets adversary (outputHalves.symm (parameter, 0))
      (secretHalves.symm ((ots, fts), high)) q (hbound _ _)
    simpa only [truncate_from_halves, tableOts_from_halves, tableFts_from_halves] using h
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
