module

public import XmssSecurity.Proof.UnifiedBadEvent

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

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
