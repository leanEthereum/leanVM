import SphincsSecurity.Proof.Residual.RetainedResidualProposalTailStep
import SphincsSecurity.Proof.Residual.RetainedResidualExceptionGame
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def prefixHistoryWeight {inputs : Finset HashInput} (state : ExceptionHistoryState inputs) : ENNReal :=
  if state.2.2 then 1 else proposalPrefixWeight state.1.2.proposals state.1.2.log.length

section Kernel

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem expected_exceptionHistoryStep_prefixWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1) (hinputs : requestInputs key input ⊆ inputs)
    (hcap : state.1.2.log.length ≤ signatureLimit) :
    (∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
  rw [exceptionHistoryStep, tsum_probOutput_map_mul]
  cases hflag : state.2.2 with
  | true =>
      simp only [prefixHistoryWeight, exceptionHistoryUpdate, hflag, Bool.true_or, ite_true, mul_one]
      exact tsum_probOutput_le_one
  | false =>
      conv_rhs => simp only [prefixHistoryWeight, hflag, Bool.false_eq_true, if_false]
      apply le_trans ?_ (expected_monitoredStep_prefixWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state.1 hvalid hinputs)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        apply mul_le_mul' le_rfl
        have hcap' := monitoredStep_log_cap key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 hcap result hr
        simp only [prefixHistoryWeight, exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_true_eq]
        split
        · exact proposalPrefixWeight_bad _ _ hcap' (by assumption)
        · exact le_rfl

theorem expected_exceptionHistoryRun_prefixWeight_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hcap : state.1.2.log.length ≤ signatureLimit) :
    (∑' result, Pr[= result | exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionHistoryRun_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ (expected_exceptionHistoryStep_prefixWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid ((requestInputs_subset key input next).trans hinputs) hcap)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        have hn := (exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stopAfter input state result hr).1
        have hv := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 hvalid _ hn
        have hc := monitoredStep_log_cap key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 hcap _ hn
        apply mul_le_mul' le_rfl
        rcases result with ⟨answer, after⟩
        cases answer with
        | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, le_refl]
        | some answer => exact ih answer after hv ((sourceInputs_next_subset key input next answer).trans hinputs) hc

theorem exceptionHistoryRun_prefix_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hcap : state.1.2.log.length ≤ signatureLimit) :
    Pr[fun result => result.2.2.2 = true |
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] ≤
      prefixHistoryWeight state := by
  apply le_trans ?_ (expected_exceptionHistoryRun_prefixWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state hvalid hinputs hcap)
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hflag
  simp only [prefixHistoryWeight, hflag, ite_true, le_refl]

end Kernel

attribute [local irreducible] gameInputs

theorem initialExceptionHistorySource_prefix_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves) (budget : Nat) :
    Pr[fun result => result.2.2.2 = true | initialExceptionHistorySource key adversary encoding dummy exposed high budget] ≤ (2 ^ 700 : ENNReal)⁻¹ := by
  apply le_trans (exceptionHistoryRun_prefix_le key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false)) _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) (Nat.zero_le _))
  exact proposalPrefixWeight_initial_le

theorem exceptionHistorySourceGame_prefix_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) :
    Pr[fun result => result.2.2.2 = true | exceptionHistorySourceGame dummy adversary budget] ≤ (2 ^ 700 : ENNReal)⁻¹ := by
  unfold exceptionHistorySourceGame
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro encoding _
  apply probEvent_bind_le_of_forall_le
  intro high _
  apply probEvent_bind_le_of_forall_le
  intro exposed _
  unfold initialExceptionHistoryPrior
  apply probEvent_bind_le_of_forall_le
  intro labels _
  exact initialExceptionHistorySource_prefix_le _ adversary encoding dummy exposed high budget

theorem forgeAdvantage_le_native_bound_add_cache_history (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        (Pr[fun result => result.2.2.1 = true | exceptionHistorySourceGame dummy adversary budget] + (2 ^ 700 : ENNReal)⁻¹) :=
  (forgeAdvantage_le_native_bound_add_histories dummy hdummy adversary budget hcost hbudget).trans
    (add_le_add le_rfl (add_le_add le_rfl (exceptionHistorySourceGame_prefix_le dummy adversary budget)))

end SphincsSecurity.Concrete.RetainedResidual
