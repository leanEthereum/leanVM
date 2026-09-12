import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform
import SphincsSecurity.Proof.Fts.MessagePrehit
namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem cachedMessageEntryCount_cacheQuery_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message ≤
      cachedMessageEntryCount cache parameter root message + 1 := by
  have hsubset : cachedMessageInputSet (cache.cacheQuery input output) parameter root message ⊆
      insert ⟨input, output⟩ (cachedMessageInputSet cache parameter root message) := by
    intro entry hentry
    rcases QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  exact (ENat.toENNReal_mono (Set.encard_le_encard hsubset)).trans
    (by simpa only [cachedMessageEntryCount, ENat.toENNReal_add, ENat.toENNReal_one] using
      ENat.toENNReal_mono (Set.encard_insert_le (cachedMessageInputSet cache parameter root message) ⟨input, output⟩))

theorem randomOracle_cachedMessageEntryCount_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    cachedMessageEntryCount result.2 parameter root message ≤ cachedMessageEntryCount cache parameter root message + 1 := by
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact cachedMessageEntryCount_cacheQuery_le parameter root message cache input output
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact le_self_add

namespace Concrete

theorem signAttempt_cachedMessageEntryCount_le (key : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache)) :
    cachedMessageEntryCount result.2 key.parameter key.root message ≤ cachedMessageEntryCount cache key.parameter key.root message + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hr
  obtain ⟨oracleResult, horacle, hpure⟩ := hr
  simp only [mem_support_pure_iff] at hpure
  subst result
  exact randomOracle_cachedMessageEntryCount_le key.parameter key.root message
    (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) cache oracleResult horacle

end Concrete
end SphincsSecurity
