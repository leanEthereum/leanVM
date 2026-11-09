module

public import XmssSecurity.Proof.CacheReplayEval
public import XmssSecurity.Proof.IdealStatement
public import XmssSecurity.Proof.Execution
public import XmssSecurity.Proof.LazyScheme

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

theorem randomOracle_query_result_cache_eq_cacheQuery
    (input : HashInput) (initialCache middleCache : QueryCache HashSpec)
    (output : HashOutput)
    (hmem : (output, middleCache) ∈ support
      ((randomOracle (spec := HashSpec) input).run initialCache)) :
    middleCache = initialCache.cacheQuery input output := by
  cases hcached : initialCache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcached, support_map,
        Set.mem_image] at hmem
      obtain ⟨sampled, _hsampled, heq⟩ := hmem
      cases heq
      rfl
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      apply QueryCache.ext
      intro candidate
      by_cases heq : candidate = input
      · subst candidate
        rw [QueryCache.cacheQuery_self, hcached]
      · rw [QueryCache.cacheQuery_of_ne _ _ heq]

theorem withQueryLog_finalCache_eq_extendHashCacheWithLog {alpha : Type}
    (computation : OracleComp HashSpec alpha)
    (initialCache : QueryCache HashSpec)
    (result : (alpha × QueryLog HashSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ randomOracle computation.withQueryLog).run initialCache)) :
    result.2 = extendHashCacheWithLog initialCache result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      rfl
  | query_bind input next ih =>
      change result ∈ support ((simulateQ randomOracle
        ((simulateQ loggingOracle
          (liftM (OracleSpec.query input) >>= next)).run)).run initialCache) at hmem
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind,
        simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      rw [simulateQ_map, StateT.run_map, support_map] at hrest
      obtain ⟨continuationResult, hcontinuation, rfl⟩ := hrest
      rw [extendHashCacheWithLog]
      rw [← randomOracle_query_result_cache_eq_cacheQuery input initialCache
        middleCache output (by simpa only [simulateQ_spec_query] using hquery)]
      exact ih output middleCache continuationResult hcontinuation

theorem hashCacheOfLog_eq_finalCache_of_empty {alpha : Type}
    (computation : OracleComp HashSpec alpha)
    (result : (alpha × QueryLog HashSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ randomOracle computation.withQueryLog).run ∅)) :
    hashCacheOfLog result.1.2 = result.2 := by
  rw [hashCacheOfLog]
  exact (withQueryLog_finalCache_eq_extendHashCacheWithLog
    computation ∅ result hmem).symm

theorem withQueryLog_cache_projection {alpha : Type}
    (computation : OracleComp HashSpec alpha)
    (initialCache : QueryCache HashSpec) :
    Prod.map Prod.fst id <$>
        (simulateQ randomOracle computation.withQueryLog).run initialCache =
      (simulateQ randomOracle computation).run initialCache := by
  change (fun result : (alpha × QueryLog HashSpec) × QueryCache HashSpec =>
    (result.1.1, result.2)) <$>
      (simulateQ randomOracle computation.withQueryLog).run initialCache = _
  rw [← StateT.run_map, ← simulateQ_map,
    show Prod.fst <$> computation.withQueryLog = computation from
      loggingOracle.fst_map_run_simulateQ computation]

namespace Concrete

def materializePrecomputation (cache : QueryCache HashSpec)
    (secretKey : SecretKey) : SecretKey :=
  precomputedSecretKey secretKey.parameter secretKey.chainStart secretKey.topChainStart
    secretKey.topSigned cache

def materializeCachedKeyResult
    (result : (PublicKey × SecretKey) × QueryCache HashSpec) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((result.1.1, materializePrecomputation result.2 result.1.2), result.2)

theorem precomputedKeygen_support_secretKey_uses_finalCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl precomputedKeygen).run ∅)) :
    keyResult.1.2 = materializePrecomputation keyResult.2 keyResult.1.2 := by
  unfold precomputedKeygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨secret, secretCache⟩, hsecret, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨topSecret, topSecretCache⟩, htopSecret, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨topBase, topBaseCache⟩, htopBase, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨treeResult, rootCache⟩, hroot, hout⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  subst keyResult
  have h1 : parameterCache = ∅ :=
    xmssRom_lift_probComp_cache_eq samplePublicParameter ∅ (parameter, parameterCache) hparameter
  have h2 : secretCache = parameterCache :=
    xmssRom_lift_probComp_cache_eq sampleSecret parameterCache (secret, secretCache) hsecret
  have h3 : topSecretCache = secretCache :=
    xmssRom_lift_probComp_cache_eq sampleTopSecret secretCache (topSecret, topSecretCache) htopSecret
  have h4 : topBaseCache = topSecretCache :=
    xmssRom_lift_probComp_cache_eq sampleTopBase topSecretCache (topBase, topBaseCache) htopBase
  have hcache0 : topBaseCache = ∅ := h4.trans (h3.trans (h2.trans h1))
  let honest : OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
    honestKeygen parameter secret topSecret (fun key _ => pure (topBase key))
  have hroute :
      simulateQ romImpl (liftM honest.withQueryLog) = simulateQ randomOracle honest.withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest.withQueryLog
  rw [hroute, hcache0] at hroot
  have hcache := hashCacheOfLog_eq_finalCache_of_empty honest (treeResult, rootCache) hroot
  simp only [materializePrecomputation, precomputedSecretKey]
  rw [hcache]

theorem evalDist_materialized_keygen_eq_precomputedKeygen :
    (materializeCachedKeyResult <$>
      (simulateQ romImpl keygen).run ∅) =ᵈ
      ((simulateQ romImpl precomputedKeygen).run ∅) := by
  rw [← erasePrecomputedKeygen_eq_keygen, simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  rw [map_eq_bind_pure_comp]
  conv_rhs => rw [← bind_pure
    ((simulateQ romImpl precomputedKeygen).run ∅)]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro keyResult hmem
  apply EvalDistEq.of_eq
  apply congrArg pure

  simp only [materializeCachedKeyResult,
    erasePrecomputedKeyResult, erasePrecomputation]
  change ((keyResult.1.1,
    materializePrecomputation keyResult.2 keyResult.1.2), keyResult.2) = keyResult
  rw [← precomputedKeygen_support_secretKey_uses_finalCache keyResult hmem]

end Concrete

end XmssSecurity
