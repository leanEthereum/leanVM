module

public import XmssSecurity.Proof.UnifiedBadEvent
public import XmssSecurity.Proof.CappedEncodingActionTrace
public import XmssSecurity.Proof.EncodingEventProbability

@[expose] public section

/-!
# A winning capped game is a cached selection or a digest bad event

In the capped game with its signing trace, a winning encoding event is a cached-selection collision,
a fresh signing collision or a post-signing fresh forged collision of one trace entry
(`cappedWinning_encoding_event_trace_postSigning_decomposition`). With the encoding trace, every
winning execution is a `WinningCachedSelectionOccurs` or a `WinningDigestBadEventOccurs` (an
encoding event that hits the capped encoding monitor, a revealed chain value, a structural collision
or a top guess) (`capped_winning_implies_cachedSelection_or_digestBad`), which
`CappedExactFirstLane` splits into lanes.
-/

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

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)

def WinningCachedSelectionOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
    ∃ entry ∈ execution.2.1.2,
      entry.CachedSelectionCollision execution.1.secretKey execution.2.1.1

def WinningDigestBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  (WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2.2 = true) ∨
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1 ∨
      WinningStructuralCollisionOccurs execution.2.1.1 execution.1 ∨
        WinningTopGuessOccurs execution.2.1.1 execution.1

theorem capped_winning_implies_cachedSelection_or_digestBad
    (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hwin : execution.1.won = true) :
    WinningCachedSelectionOccurs execution ∨
      WinningDigestBadEventOccurs execution := by
  have hcache : (execution.1, execution.2.1.1) ∈ support
      (detailedGameWithCache Concrete.scheme adversary) := by
    rw [← cappedDetailedGameWithEncodingTrace_cache_projection, support_map]
    exact ⟨execution, hmem, rfl⟩
  have hunified := winning_outcome_has_unifiedBadEvent execution.2.1.1
    execution.1 (capped_detailed_execution_consistent adversary _ hcache) hwin
  rcases hunified with hencoding | hchain | hstructural | htop
  · have hencoding' : WinningOutcomeBadEventOccurs execution.2.1.1
        execution.1 .encoding := by
      simpa [WinningEncodingEventOccurs, WinningGlobalBadEventOccurs,
        GlobalOutcomeBadEventOccurs, WinningOutcomeBadEventOccurs] using hencoding
    have hsigning : (execution.1, execution.2.1) ∈ support
        (cappedDetailedGameWithSigningTrace adversary) := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
      exact ⟨execution, hmem, rfl⟩
    obtain ⟨entry, hentry, hcachedSelection | hsigningCollision |
        hforgedCollision⟩ :=
      cappedWinning_encoding_event_trace_postSigning_decomposition adversary
        (execution.1, execution.2.1) hsigning hencoding'
    · exact Or.inl ⟨hencoding', entry, hentry, hcachedSelection⟩
    · exact Or.inr (Or.inl ⟨hencoding',
        cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
          adversary execution hmem hencoding'
            ⟨entry, hentry, hsigningCollision⟩⟩)
    · obtain ⟨encoding, hdecode⟩ := hencoding'.forgery_decode
      exact Or.inr (Or.inl ⟨hencoding',
        cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
          adversary execution hmem hencoding' encoding hdecode
            ⟨entry, hentry, hforgedCollision⟩⟩)
  · exact Or.inr (Or.inr (Or.inl hchain))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hstructural)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htop)))

end XmssSecurity
