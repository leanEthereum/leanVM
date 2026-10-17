import XmssSecurity.Proof.GlobalBadEvent
import XmssSecurity.Proof.CappedSuffixEventProbability
import XmssSecurity.Proof.CappedMerkleEventProbability
import XmssSecurity.Proof.ExpectedAdaptiveFreshTarget

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem outcomePredicate_probability_le_expectedMovedQueries_of_afterKeygen_freshCollision
    (adversary : Adversary)
    (event : GameOutcome × QueryCache HashSpec → Prop)
    (targetInput :
      (PublicKey × SecretKey) → QueryCache HashSpec → HashInput → HashInput)
    (horient : ∀ keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ execution ∈ support
        ((simulateQ romImpl
          (detailedGameAfterKeygen Concrete.scheme adversary
            keyResult.1.1 keyResult.1.2)).run keyResult.2),
        event execution →
          Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (targetInput keyResult.1 keyResult.2)) :
    Pr[event | detailedGameWithCache Concrete.scheme adversary] ≤
      (∑' keyResult,
        Pr[= keyResult |
          (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          expectedSimulatedQueryCount romImpl
            (Rom.IsRelevantHashQuery fun input =>
              targetInput keyResult.1 keyResult.2 input ≠ input)
            (detailedGameAfterKeygen Concrete.scheme adversary
              keyResult.1.1 keyResult.1.2) keyResult.2) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  unfold detailedGameWithCache detailedGameCore
  apply Rom.mixed_adaptiveFreshDigestCollision_after_prefix_le_expectedMovedContinuation
    Concrete.scheme.keygen
    (fun key => detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2)
    ∅ targetInput event
  exact horient

theorem globalSuffixCollision_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : GlobalOutcomeBadEventOccurs execution.2 execution.1
      .suffixCollision) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (CappedSuffix.keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨slot, hslot⟩ := hevent
  exact CappedSuffix.suffixCollision_event_afterKeygen_orientation adversary
    keyResult hkeygen execution hafter slot hslot

theorem globalMerkle_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : GlobalOutcomeBadEventOccurs execution.2 execution.1 .merkle) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (CappedMerkle.keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨level, hlevel⟩ := hevent
  exact CappedMerkle.merkle_event_afterKeygen_orientation adversary keyResult
    hkeygen execution hafter level hlevel

end XmssSecurity
