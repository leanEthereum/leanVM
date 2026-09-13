import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Charge
/-!
# First creation of a monotone cache event

A cache property cannot change on a uniform query or a cached hash query. If a supported run starts
without the property and ends with it, one fresh random-oracle transition is therefore its first
creation point. The witness retains the cache inclusions on both sides of that transition.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

theorem finite_cache_of_mem_support {alpha : Type}
    (oa : OracleComp OracleWorld alpha)
    (initialCache : QueryCache HashSpec) (result : alpha)
    (finalCache : QueryCache HashSpec)
    (hrun : (result, finalCache) ∈ support ((simulateQ romImpl oa).run initialCache))
    (hfinite : Finite initialCache) : Finite finalCache := by
  induction oa using OracleComp.inductionOn generalizing initialCache result finalCache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact hfinite
  | query_bind query next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hrun
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hrun
      apply ih answer middleCache result finalCache hrest
      cases query with
      | inl uniformInput =>
          change (answer, middleCache) ∈ support
            (((unifFwdImpl HashSpec) uniformInput).run initialCache) at hquery
          have hrunUniform :
              ((unifFwdImpl HashSpec) uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          rw [hrunUniform, support_map] at hquery
          obtain ⟨sample, hsample, heq⟩ := hquery
          obtain ⟨rfl, rfl⟩ := heq
          exact hfinite
      | inr input =>
          change HashOutput at answer
          change (answer, middleCache) ∈ support
            (((randomOracle : QueryImpl HashSpec _) input).run initialCache) at hquery
          cases hcached : initialCache input with
          | some cachedAnswer =>
              rw [QueryImpl.withCaching_run_some uniformSampleImpl hcached,
                support_pure, Set.mem_singleton_iff] at hquery
              obtain ⟨rfl, rfl⟩ := hquery
              exact hfinite
          | none =>
              rw [QueryImpl.withCaching_run_none uniformSampleImpl hcached, support_map] at hquery
              obtain ⟨freshAnswer, hfresh, heq⟩ := hquery
              obtain ⟨rfl, rfl⟩ := heq
              exact finite_cacheQuery hfinite input answer

end SphincsSecurity
