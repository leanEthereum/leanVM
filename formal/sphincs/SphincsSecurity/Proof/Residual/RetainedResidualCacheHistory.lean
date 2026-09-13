import SphincsSecurity.Proof.Residual.RetainedResidualCacheKernels
import SphincsSecurity.Proof.Residual.RetainedResidualExceptionHistory
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheHistoryWeight {inputs : Finset HashInput} (key : SecretKey) (state : ExceptionHistoryState inputs) : ENNReal :=
  if state.2.1 then 1 else certificateCacheExceptionWeight key state.1.1.memory.external.cache

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem expected_exceptionHistoryStep_cacheWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1) (hinputs : requestInputs key input ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    (∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      cacheHistoryWeight key result.2) ≤ cacheHistoryWeight key state +
        nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate := by
  rw [exceptionHistoryStep, tsum_probOutput_map_mul]
  cases hflag : state.2.1 with
  | true =>
      simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.true_or, ite_true, mul_one]
      exact tsum_probOutput_le_one.trans le_self_add
  | false =>
      conv_rhs => simp only [cacheHistoryWeight, hflag, Bool.false_eq_true, if_false]
      by_cases hbefore : CertificateCacheExceptional key state.1.1.memory.external.cache
      · simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_true hbefore, Bool.true_or, ite_true, mul_one]
        exact tsum_probOutput_le_one.trans ((certificateCacheExceptionWeight_bad key _ (Finite.of_enncard_le hbound) hbefore).trans le_self_add)
      · apply le_trans ?_ (expected_monitoredStep_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state.1 hvalid hinputs hbound)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1] = 0
        · simp only [hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          apply mul_le_mul' le_rfl
          have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state.1 hvalid hinputs hbound result hr
          simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_false hbefore, Bool.false_or, decide_eq_true_eq]
          split
          · exact certificateCacheExceptionWeight_bad key _ (Finite.of_enncard_le hb) (by assumption)
          · exact le_rfl

theorem expected_exceptionHistoryRun_cacheWeight_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    (∑' result, Pr[= result | exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      cacheHistoryWeight key result.2) ≤ cacheHistoryWeight key state +
        expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
          (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) computation state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionHistoryRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, tsum_probOutput_bind_mul]
      let payment (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) : ENNReal :=
        result.1.elim 0 (fun answer => expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
          (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) (next answer) result.2)
      have herasure := congrArg (fun law : SPMF (Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) =>
          ∑' result, Pr[= result | law] * payment result)
        (exceptionHistoryStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state)
      rw [tsum_probOutput_map_mul] at herasure
      calc
        _ ≤ ∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (cacheHistoryWeight key result.2 + payment (result.1, result.2.1)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hn := (exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stopAfter input state result hr).1
            have hv := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 hvalid _ hn
            have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
              input state.1 hvalid ((requestInputs_subset key input next).trans hinputs) hbound _ hn
            apply mul_le_mul' le_rfl
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [payment, Option.elim_none, tsum_probOutput_pure_mul, add_zero, le_refl]
            | some answer => exact ih answer after hv ((sourceInputs_next_subset key input next answer).trans hinputs) hb
        _ ≤ (cacheHistoryWeight key state + nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate) +
            ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1] * payment result := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [herasure]
          exact add_le_add (expected_exceptionHistoryStep_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state hvalid ((requestInputs_subset key input next).trans hinputs) hbound) le_rfl
        _ = _ := by
          change (cacheHistoryWeight key state + _) + _ = cacheHistoryWeight key state + (_ + _)
          exact add_assoc _ _ _

theorem exceptionHistoryRun_cache_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    Pr[fun result => result.2.2.1 = true |
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] ≤
      cacheHistoryWeight key state + expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
        (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) computation state.1 := by
  apply le_trans ?_ (expected_exceptionHistoryRun_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state hvalid hinputs hbound)
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hflag
  simp only [cacheHistoryWeight, hflag, ite_true, le_refl]

end SphincsSecurity.Concrete.RetainedResidual
