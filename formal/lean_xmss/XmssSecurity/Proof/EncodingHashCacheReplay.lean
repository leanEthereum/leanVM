module

public import XmssSecurity.Proof.CacheReplayEval
public import XmssSecurity.Proof.HashInputLemmas

@[expose] public section

/-!
# Encoding digests read back from a later cache

After a lazy random-oracle run of `Concrete.encodingHash` returns a digest, every cache extending
the run's final cache reads the same digest at that input
(`Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le`).
-/

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.encodingHash largerCache parameter leafIndex
      (message, randomness) = digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter leafIndex
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  have hcachedLarger := hle hcached
  rw [Concrete.CacheView.encodingHash,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]
  exact congrArg Prod.fst heq

end XmssSecurity
