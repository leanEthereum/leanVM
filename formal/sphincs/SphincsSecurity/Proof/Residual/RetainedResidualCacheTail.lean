import SphincsSecurity.Proof.Residual.RetainedResidualCacheHistory
import SphincsSecurity.Proof.Residual.RetainedResidualPaymentBudget
import SphincsSecurity.Proof.Residual.RetainedResidualProposalTail
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs gameInputs
  certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

theorem exceptionHistoryRun_cache_le_budget (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory)
    (q : Nat) (hq : ∀ result, monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state.1 result ≠ 0 →
      result.2.1.memory.external.hashCalls ≤ q) :
    Pr[fun result => result.2.2.1 = true |
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] ≤
      cacheHistoryWeight key state + q * certificateCacheExceptionRate := by
  apply le_trans (exceptionHistoryRun_cache_le key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state hvalid hinputs hbound)
  rw [expectedMonitoredPayment_mul]
  exact add_le_add le_rfl (mul_le_mul' (expectedMonitoredPayment_le_budget key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state.1 hvalid hinputs q hq) le_rfl)

theorem initialExceptionHistorySource_cache_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) :
    Pr[fun result => result.2.2.1 = true | initialExceptionHistorySource key adversary encoding dummy exposed high budget] ≤
      (budget : ENNReal) * (2 ^ 169 : ENNReal)⁻¹ := by
  apply le_trans (exceptionHistoryRun_cache_le_budget key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false))
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor 1212415 false), (false, false))
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (1212415 : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le)
    budget (initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false hparameter hencoding hroot hcost))
  change certificateCacheExceptionWeight key (∅ : QueryCache HashSpec) + (budget : ENNReal) * certificateCacheExceptionRate ≤ _
  rw [certificateCacheExceptionWeight_initial key ∅ (fun _ _ => rfl), zero_add]
  exact mul_le_mul' le_rfl certificateCacheExceptionRate_le

theorem exceptionHistorySourceGame_cache_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hcost : HasHashQueryBound scheme adversary budget) :
    Pr[fun result => result.2.2.1 = true | exceptionHistorySourceGame dummy adversary budget] ≤
      (budget : ENNReal) * (2 ^ 169 : ENNReal)⁻¹ := by
  unfold exceptionHistorySourceGame
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  have hp : parameter ∈ support sampleParameter := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hparameter
  apply probEvent_bind_le_of_forall_le
  intro encoding hencoding
  have he : encoding ∈ referenceEncodingAuxiliarySample.support := by
    simpa only [PMF.evalDist_eq, SPMF.support_eq_support, SPMF.support_liftM] using hencoding
  apply probEvent_bind_le_of_forall_le
  intro high _
  apply probEvent_bind_le_of_forall_le
  intro exposed _
  unfold initialExceptionHistoryPrior
  apply probEvent_bind_le_of_forall_le
  intro labels _
  exact initialExceptionHistorySource_cache_le _ adversary encoding dummy exposed high budget hp he rfl hcost

theorem forgeAdvantage_le_native_bound (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        ((budget : ENNReal) * (2 ^ 169 : ENNReal)⁻¹ + (2 ^ 700 : ENNReal)⁻¹) :=
  (forgeAdvantage_le_native_bound_add_cache_history dummy hdummy adversary budget hcost hbudget).trans
    (add_le_add le_rfl (add_le_add (exceptionHistorySourceGame_cache_le dummy adversary budget hcost) le_rfl))

end SphincsSecurity.Concrete.RetainedResidual
