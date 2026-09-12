import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

/-!
# Random-oracle cache size

A run starting from a cache can add at most one entry per hash query. Uniform-sampling queries leave
the cache unchanged.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem QueryCache.enncard_mono {first second : QueryCache HashSpec}
    (hle : first ≤ second) : QueryCache.enncard first ≤ QueryCache.enncard second := by
  exact ENat.toENNReal_mono (Set.encard_le_encard (QueryCache.toSet_mono hle))

theorem romImpl_uniform_query_enncard_eq
    (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : unifSpec.Range input × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inl input)).run cache)) :
    QueryCache.enncard result.2 = QueryCache.enncard cache := by
  change result ∈ support ((unifFwdImpl HashSpec input).run cache) at hmem
  have hrun : (unifFwdImpl HashSpec input).run cache =
      (fun sample => (sample, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) cache)
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, rfl⟩ := hmem
  rfl

theorem romImpl_hash_query_enncard_le
    (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inr input)).run cache)) :
    QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  change result ∈ support ((randomOracle input).run cache) at hmem
  by_cases hcache : cache input = none
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache,
      support_map] at hmem
    obtain ⟨output, _houtput, rfl⟩ := hmem
    exact QueryCache.enncard_cacheQuery_le cache input output
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcache
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ houtput,
      support_pure, Set.mem_singleton_iff] at hmem
    subst result
    exact le_add_right le_rfl

end SphincsSecurity
