import SphincsSecurity.Proof.Residual.RetainedResidualExceptionHistory
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree)

theorem exceptionHistoryRun_unstopped {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (hbefore : MonitoredAccounting state.1) (hbank : MonitoredBankComplete key required state.1)
    (hsize : CacheSizeBound state.1.1.memory)
    (hsigned : SigningDigestsCached key.parameter state.1.1.memory.external.cache key.root state.1.1.memory.log)
    (halive : state.1.2.stopped = false) (hbudget : budget ≤ 2 ^ 127)
    (result : Option Result × ExceptionHistoryState inputs)
    (hresult : exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required
      (proposalStop (fun _ _ _ _ => false)) computation state result ≠ 0)
    (hlive : result.1 ≠ none) (hcost : result.2.1.1.memory.external.hashCalls ≤ budget)
    (hlog : result.2.1.1.memory.log.length ≤ signatureLimit) (hclean : result.2.2 = (false, false)) :
    result.2.1.2.stopped = false := by
  let stop : CertificateStopRule := proposalStop (fun _ _ _ _ => false)
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [exceptionHistoryRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact halive
  | query_bind input next ih =>
      have hwhole := exceptionHistoryRun_support key inputs hencoding words publicReplies selections rows budget required stop
        (OracleSpec.query input >>= next) state result hresult
      rw [exceptionHistoryRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact False.elim (hlive rfl)
      | some answer =>
          have hafter := exceptionHistoryRun_clean key inputs hencoding words publicReplies selections rows budget required stop
            (next answer) after result hresult hclean
          obtain ⟨hnativeStep, hupdate⟩ := exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stop
            input state (some answer, after) hstep
          rw [hupdate] at hafter
          simp only [exceptionHistoryUpdate, Prod.mk.injEq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hafter
          have hin := (requestInputs_subset key input next).trans hinputs
          have hnextInputs := (sourceInputs_next_subset key input next answer).trans hinputs
          have hvalid' := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stop
            input state.1 hvalid (some answer, after.1) hnativeStep
          have haccount' := (monitoredStep_accounting key inputs hencoding words publicReplies selections rows budget required stop
            input state.1 hvalid hin hbefore (some answer, after.1) hnativeStep).1
          have hnativeNext := exceptionHistoryRun_support key inputs hencoding words publicReplies selections rows budget required stop
            (next answer) after result hresult
          have hcost' := ((monitoredRun_accounting key inputs hencoding words publicReplies selections rows budget required stop
            (next answer) after.1 hvalid' hnextInputs haccount' (result.1, result.2.1) hnativeNext).2.1).trans hcost
          have hactive := monitoredRun_query_active key inputs hencoding words publicReplies selections rows budget required stop
            input next state.1 hvalid hinputs hbefore hbank hsize hsigned (result.1, result.2.1) hwhole hcost hlog hbudget halive hafter.1.1.2
          have hstop := monitoredStep_stopped_iff_prefix key inputs hencoding words publicReplies selections rows budget required
            input state.1 hvalid hin hbefore hbank hsize hsigned hactive (some answer, after.1) hnativeStep
            (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hcost' hbudget hafter.1.2
          have halive' : after.1.2.stopped = false := by
            cases heq : after.1.2.stopped with
            | false => rfl
            | true => exact False.elim (hafter.2.2 (hstop.mp heq))
          exact ih answer after hvalid' hnextInputs haccount'
            (monitoredStep_bank_complete key inputs hencoding words publicReplies selections rows budget required stop
              input state.1 hvalid.1 hbank (some answer, after.1) hnativeStep)
            (monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stop
              input state.1 hvalid hin hsize (some answer, after.1) hnativeStep)
            (monitoredStep_digestsCached key inputs hencoding words publicReplies selections rows budget required stop
              input state.1 hvalid hin hsigned (some answer, after.1) hnativeStep)
            halive' hresult

end SphincsSecurity.Concrete.RetainedResidual
