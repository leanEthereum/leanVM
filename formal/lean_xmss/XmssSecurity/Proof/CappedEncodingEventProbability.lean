import XmssSecurity.Proof.CappedEncodingActionTrace
import XmssSecurity.Proof.CappedSigningCacheTrace
import XmssSecurity.Proof.EncodingEventProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem cappedWinning_encoding_event_trace_postSigning_decomposition
    (adversary : Adversary)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (cappedDetailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    ∃ entry ∈ execution.2.2,
      entry.CachedSelectionCollision execution.1.secretKey execution.2.1 ∨
        entry.FreshSigningEncodingCollision execution.1.secretKey ∨
          entry.PostSigningFreshForgedEncodingCollision execution.1.secretKey
            execution.1.forgery execution.2.1 := by
  obtain ⟨hlog, hcaches, hcached⟩ :=
    cappedDetailedGameWithSigningTrace_invariants adversary execution hmem
  obtain ⟨entry, hentry, hcachedSelection | hsigning | ⟨hforged, signature, hsignature,
      hsignedFresh⟩⟩ :=
    winning_encoding_event_trace_monitor_decomposition execution.2.1 execution.1
      execution.2.2 hlog hcaches hcached hevent
  · exact ⟨entry, hentry, Or.inl hcachedSelection⟩
  · exact ⟨entry, hentry, Or.inr (Or.inl hsigning)⟩
  · obtain ⟨encoding, hdecode⟩ := hevent.forgery_decode
    exact ⟨entry, hentry, Or.inr (Or.inr
      (entry.postSigningFreshForgedEncodingCollision_of_valid_fresh
        execution.1.secretKey execution.1.forgery execution.2.1
        (cappedDetailedGameWithSigningTrace_preservesOtherValidEncodingInputs
          adversary execution hmem entry hentry)
        (hcaches entry hentry).2 hforged encoding hdecode
        signature hsignature hsignedFresh))⟩

end XmssSecurity
