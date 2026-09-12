import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Cached
import SphincsSecurity.Proof.Scheme.Execution
/-!
# Replaying the full oracle world

Once a final random-oracle cache fixes an answer function, the same execution can be replayed with
those hash answers deterministic while uniform-sampling queries remain probabilistic.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

noncomputable def replayRomImpl (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (f.liftTarget ProbComp).withCaching

noncomputable def replayHashImpl (f : QueryImpl HashSpec Id) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  (f.liftTarget ProbComp).withCaching

theorem replayRom_of_mem_support {alpha : Type} (oa : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support ((simulateQ romImpl oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    (a, finalCache) ∈ support ((simulateQ (replayRomImpl f) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest hf⟩
      cases input with
      | inl sample =>
          change (answer, middleCache) ∈ support (((unifFwdImpl HashSpec) sample).run cache)
            at hquery ⊢
          exact hquery
      | inr hashInput =>
          change HashOutput at answer
          change (answer, middleCache) ∈ support
            (((randomOracle : QueryImpl HashSpec _) hashInput).run cache) at hquery
          have hmiddleLe : middleCache ≤ finalCache :=
            simulateQ_romImpl_cache_le (next answer) middleCache _ hrest
          change (answer, middleCache) ∈ support
            ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) hashInput).run cache)
          cases hcache : cache hashInput with
          | some old =>
              rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
                Set.mem_singleton_iff] at hquery
              obtain ⟨rfl, rfl⟩ := hquery
              rw [QueryImpl.withCaching_run_some _ hcache, support_pure, Set.mem_singleton_iff]
          | none =>
              rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
              obtain ⟨sampled, _, heq⟩ := hquery
              obtain ⟨rfl, rfl⟩ := heq
              have hfanswer : f hashInput = answer :=
                hf (hmiddleLe (QueryCache.cacheQuery_self cache hashInput answer))
              rw [QueryImpl.withCaching_run_none _ hcache, support_map]
              refine ⟨f hashInput, ?_, ?_⟩
              · change f hashInput ∈ support (pure (f hashInput) : ProbComp HashOutput)
                exact Set.mem_singleton _
              · rw [hfanswer]

theorem replayHash_mem_randomOracle {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache)) :
    (a, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest⟩
      change (answer, middleCache) ∈ support
        ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) input).run cache)
        at hquery
      change (answer, middleCache) ∈ support
        (((randomOracle : QueryImpl HashSpec _) input).run cache)
      cases hcache : cache input with
      | some old =>
          rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
            Set.mem_singleton_iff] at hquery
          obtain ⟨rfl, rfl⟩ := hquery
          rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
            Set.mem_singleton_iff]
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hquery
          obtain ⟨sampled, hsampled, heq⟩ := hquery
          have hsampledEq : sampled = f input := by
            change sampled ∈ support (pure (f input) : ProbComp HashOutput) at hsampled
            simpa using hsampled
          subst sampled
          obtain ⟨rfl, rfl⟩ := heq
          rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map]
          exact ⟨f input, by simp [uniformSampleImpl], rfl⟩

theorem replayHash_of_mem_support {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache))
    (hf : finalCache.AgreesWithFn f) :
    cache ≤ finalCache ∧ evalWithAnswerFn f oa = a ∧ CachedRun finalCache f oa := by
  have hrandom := replayHash_mem_randomOracle f oa cache a finalCache hmem
  obtain ⟨hle, heval, hqueries⟩ := replay_of_mem_support oa cache a finalCache hrandom f hf
  exact ⟨hle, heval, hqueries⟩

theorem simulateQ_replayRom_liftM {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) :
    simulateQ (replayRomImpl f) (liftM oa : OracleComp OracleWorld alpha)
      = simulateQ (replayHashImpl f) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

end SphincsSecurity
