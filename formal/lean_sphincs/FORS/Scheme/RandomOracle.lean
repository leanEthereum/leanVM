import FORS.Scheme.Lemmas

/-! The uncounted shared random-oracle interpreter, and the replay of a lazy random-oracle run by
any answer function that extends its cache. -/

open OracleComp OracleSpec

namespace FORS.Completeness

variable [Params]

noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

theorem simulate_lift_hash {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α) = simulateQ randomOracle oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

theorem run_lift_prob {α : Type} (oa : ProbComp α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM oa : OracleComp OracleWorld α)).run cache =
      (fun x => (x, cache)) <$> oa :=
  roSim.run_liftM _ oa cache

/-- A lazy-oracle query records its answer and preserves all previous answers. -/
theorem query_support_cached (input : HashInput) (cache : QueryCache HashSpec)
    (answer : HashOutput) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    cache ≤ cache' ∧ cache' input = some answer := by
  refine ⟨QueryImpl.withCaching_cache_le uniformSampleImpl input cache (answer, cache') hmem, ?_⟩
  cases hc : cache input with
  | some old =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hc
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, support_map] at hmem
      obtain ⟨sample, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      exact QueryCache.cacheQuery_self cache input answer

/-- Any answer function extending a lazy-oracle run's cache replays that run. -/
theorem replay_hash_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ evalWithAnswerFn f oa = a := by
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨le_rfl, rfl⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      obtain ⟨hqueryLe, hcached⟩ := query_support_cached input cache answer cacheMid hquery
      obtain ⟨hrestLe, heval⟩ := ih answer cacheMid a cache' hrest hf
      have hfinput : f input = answer := hf (hrestLe hcached)
      refine ⟨hqueryLe.trans hrestLe, ?_⟩
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, hfinput]
      exact heval

/-- Hash-only runs never delete or overwrite previous oracle answers. -/
theorem hash_support_cache_le {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache)) :
    cache ≤ cache' := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cache'
  exact (replay_hash_support oa cache a cache' hmem f hf).1

end FORS.Completeness
