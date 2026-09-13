import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateBoundaryInvariants
import SphincsSecurity.Proof.Fts.MessageCacheProjection
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable

theorem observedTargetShapeVector_messageOnlyCache (key : SecretKey) (payload : HashInput) (target : FewTimeView)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    observedTargetShapeVector key payload target (messageOnlyCache key.parameter cache, log) =
      observedTargetShapeVector key payload target (cache, log) := by
  funext groups remaining
  simp only [observedTargetShapeVector, targetShapeMoments, normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_messageOnlyCache, normalizedTargetLogProduct, normalizedTargetLogMatch,
    messageAnswers_messageOnlyCache]

theorem targetCertificateForecast_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (input : HashInput) (target : FewTimeView) :
    targetCertificateForecast key reuse budget signatures required (messageOnlyCache key.parameter cache, log) input target =
      targetCertificateForecast key reuse budget signatures required (cache, log) input target := by
  simp only [targetCertificateForecast, reuseTargetEnvelope, observedTargetShapeVector_messageOnlyCache]

theorem bankedCacheWeight_messageOnlyCache (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool) (stopped : Bool) (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank stopped (messageOnlyCache parameter cache) =
      bankedCacheWeight parameter weight bank stopped cache := by
  cases stopped <;> simp only [bankedCacheWeight_stopped, bankedCacheWeight_live, cacheMessageWeight_messageOnlyCache]

theorem bankedTargetEnvelope_messageOnlyCache (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required (messageOnlyCache key.parameter cache, log) bank stopped =
      bankedTargetEnvelope key reuse budget signatures required (cache, log) bank stopped := by
  simp only [bankedTargetEnvelope]
  have hweight := funext fun input => funext fun target =>
    targetCertificateForecast_messageOnlyCache key reuse budget signatures required cache log input target
  rw [hweight, bankedCacheWeight_messageOnlyCache]

theorem bankedTargetEnvelope_congr_messageHistory (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (before after : QueryCache HashSpec)
    (hcache : messageAnswers key.parameter before = messageAnswers key.parameter after)
    (log : QueryLog SigningSpec) (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required (before, log) bank stopped =
      bankedTargetEnvelope key reuse budget signatures required (after, log) bank stopped := by
  rw [← bankedTargetEnvelope_messageOnlyCache key reuse budget signatures required before log bank stopped,
    ← bankedTargetEnvelope_messageOnlyCache key reuse budget signatures required after log bank stopped,
    messageOnlyCache_eq_of_messageAnswers_eq key.parameter before after hcache]

theorem bankedTargetEnvelope_complete_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) :
    bankedTargetEnvelope key reuse budget signatures required state (completedTargetBank key required state bank) stopped ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false := by
  apply bankedCacheWeight_bank_le
  intro input hcomplete
  exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required state input
    (of_decide_eq_true hcomplete)

theorem bankedProposalRecordValue_world_le_of_messageHistory (key : SecretKey) (reuse : ENNReal)
    (budget signatures : Nat) (required : Finset FtsTree) (state : CoverLogState)
    (bank : HashInput → Bool) (input : OracleWorld.Domain) (record : ProposalExecutionRecord (.inl input))
    (stopped : Bool) (hcache : messageAnswers key.parameter record.cache = messageAnswers key.parameter state.1) :
    bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) record stopped ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false := by
  simp only [bankedProposalRecordValue, proposalRecordLogState, signingLogFragment, List.append_nil]
  apply (bankedTargetEnvelope_complete_le key reuse (budget - record.trace.hashCalls) signatures required
    (record.cache, state.2) bank stopped).trans
  rw [bankedTargetEnvelope_congr_messageHistory key reuse (budget - record.trace.hashCalls) signatures required
    record.cache state.1 hcache state.2 bank false]
  exact bankedTargetEnvelope_budget_mono key reuse signatures required state bank false (Nat.sub_le _ _)

end SphincsSecurity.Concrete
