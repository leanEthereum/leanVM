import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

open OracleComp OracleSpec

namespace OracleComp

variable {D R : Type} [DecidableEq D] [SampleableType R]

omit [SampleableType R] in
theorem QueryCache.cacheQuery_comm_of_ne
    (cache : (D →ₒ R).QueryCache) {left right : D} (h : left ≠ right)
    (leftValue rightValue : R) :
    (cache.cacheQuery left leftValue).cacheQuery right rightValue =
      (cache.cacheQuery right rightValue).cacheQuery left leftValue := by
  funext input
  by_cases hleft : input = left
  · subst input
    simp [QueryCache.cacheQuery_of_ne, h]
  · by_cases hright : input = right
    · subst input
      simp [QueryCache.cacheQuery_of_ne, hleft]
    · simp [QueryCache.cacheQuery_of_ne, hleft, hright]

/-- Sampling one absent entry before a computation preserves the full result and final-cache distribution when every execution of the computation caches that entry. -/
theorem evalDist_randomOracle_run_eq_presample_of_cached
    {α : Type} (computation : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (habsent : cache target = none)
    (hcached : ∀ result ∈ support
      ((simulateQ randomOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    𝒟[(simulateQ randomOracle computation).run cache] =
      𝒟[do
        let value ← $ᵗ R
        (simulateQ randomOracle computation).run
          (cache.cacheQuery target value)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      exfalso
      obtain ⟨output, houtput⟩ := hcached (value, cache) (by simp)
      change cache target = some output at houtput
      rw [habsent] at houtput
      simp at houtput
  | query_bind input next ih =>
      have hrun (initialCache : (D →ₒ R).QueryCache) :
          (simulateQ randomOracle
            (liftM ((D →ₒ R).query input) >>= next)).run initialCache =
          ((randomOracle (spec := D →ₒ R) input).run initialCache) >>= fun result =>
            (simulateQ randomOracle (next result.1)).run result.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      by_cases htarget : input = target
      · subst input
        rw [hrun, QueryImpl.withCaching_run_none _ habsent,
          map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro sampled
        rw [hrun, QueryImpl.withCaching_run_some _
          (QueryCache.cacheQuery_self cache target sampled), pure_bind]
      · cases hinput : cache input with
        | some answer =>
            rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
            have hnextCached : ∀ result ∈ support
                ((simulateQ randomOracle (next answer)).run cache),
                ∃ output, result.2 target = some output := by
              intro result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_some _ hinput]
              simp
            calc
              𝒟[(simulateQ randomOracle (next answer)).run cache] =
                  𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle (next answer)).run
                      (cache.cacheQuery target sampled)] :=
                ih answer cache habsent hnextCached
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hcachedInput :
                    (cache.cacheQuery target sampled) input = some answer := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_some _ hcachedInput, pure_bind]
            rfl
        | none =>
            have htargetAfterInput : ∀ answer : R,
                (cache.cacheQuery input answer) target = none := by
              intro answer
              simpa [QueryCache.cacheQuery_of_ne, Ne.symm htarget] using habsent
            rw [hrun, QueryImpl.withCaching_run_none _ hinput,
              map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            have hnextCached : ∀ answer : R, ∀ result ∈ support
                ((simulateQ randomOracle (next answer)).run
                  (cache.cacheQuery input answer)),
                ∃ output, result.2 target = some output := by
              intro answer result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache.cacheQuery input answer), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_none _ hinput, support_map]
              exact ⟨answer, mem_support_uniformSample R, rfl⟩
            calc
              𝒟[$ᵗ R >>= fun answer =>
                  (simulateQ randomOracle (next answer)).run
                    (cache.cacheQuery input answer)] =
                  𝒟[$ᵗ R >>= fun answer =>
                    $ᵗ R >>= fun sampled =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                exact ih answer (cache.cacheQuery input answer)
                  (htargetAfterInput answer) (hnextCached answer)
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery target sampled).cacheQuery input answer)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                rw [QueryCache.cacheQuery_comm_of_ne cache htarget]
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hnone : (cache.cacheQuery target sampled) input = none := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_none _ hnone,
                  map_eq_bind_pure_comp]
                simp only [Function.comp_apply, bind_assoc, pure_bind]
                rfl
            rfl

/-- Querying one entry and discarding its answer before a computation preserves the full result and final-cache distribution when the computation always caches that entry. -/
theorem evalDist_randomOracle_run_eq_query_then_of_cached
    {α : Type} (computation : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (hcached : ∀ result ∈ support
      ((simulateQ randomOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    𝒟[(simulateQ randomOracle computation).run cache] =
      𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun queryResult =>
        (simulateQ randomOracle computation).run queryResult.2] := by
  cases htarget : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ htarget,
        map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      exact evalDist_randomOracle_run_eq_presample_of_cached
        computation cache target htarget hcached
  | some output =>
      rw [QueryImpl.withCaching_run_some _ htarget, pure_bind]

end OracleComp
