import SphincsSecurity.Proof.Residual.RetainedResidualNativePayment
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem expectedMonitoredPayment_counter_lower (counter : MonitoredState inputs → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state, MonitoredValid inputs state → requestInputs key input ⊆ inputs →
      counter state + charge input (monitorView state) ≤
        ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] * counter result.2)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state) (hinputs : sourceInputs key computation ⊆ inputs) :
    counter state + expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge computation state ≤
      ∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] * counter result.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [monitoredRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul]
      let payment (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) : ENNReal :=
        result.1.elim 0 (fun answer => expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2)
      calc
        _ = (counter state + charge input (monitorView state)) +
            ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] * payment result :=
          (add_assoc _ _ _).symm
        _ ≤ ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (counter result.2 + payment result) := by
          simp only [mul_add, ENNReal.tsum_add]
          exact add_le_add (hstep input state hvalid ((requestInputs_subset key input next).trans hinputs)) le_rfl
        _ ≤ _ := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hv := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid result hr
            apply mul_le_mul' le_rfl
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [payment, Option.elim_none, tsum_probOutput_pure_mul, add_zero, le_refl]
            | some answer => exact ih answer after hv ((sourceInputs_next_subset key input next answer).trans hinputs)

theorem expectedMonitoredPayment_mul
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal) (rate : ENNReal)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState inputs) :
    expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
      (fun input current => charge input current * rate) computation state =
      expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge computation state * rate := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact (zero_mul _).symm
  | query_bind input next ih =>
      change charge input (monitorView state) * rate +
        (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
          result.1.elim 0 (fun answer => expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
            (fun input current => charge input current * rate) (next answer) result.2)) =
        (charge input (monitorView state) +
          ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            result.1.elim 0 (fun answer => expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2)) * rate
      rw [add_mul, ← ENNReal.tsum_mul_right]
      apply congrArg₂ (· + ·) rfl
      apply tsum_congr
      rintro ⟨answer, after⟩
      cases answer with
      | none => simp only [Option.elim_none, mul_zero, zero_mul]
      | some answer => simp only [Option.elim_some, ih, mul_assoc]

theorem expectedMonitoredPayment_le_budget {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state) (hinputs : sourceInputs key computation ⊆ inputs)
    (q : Nat) (hq : ∀ result, monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0 →
      result.2.1.memory.external.hashCalls ≤ q) :
    expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter (nativeMessageCharge key) computation state ≤ q := by
  apply le_trans (le_add_self.trans (expectedMonitoredPayment_counter_lower key inputs hencoding words publicReplies selections rows budget required stopAfter
    (fun current => (current.1.memory.external.hashCalls : ENNReal)) (nativeMessageCharge key)
    (expected_monitoredStep_hashCalls_lower key inputs hencoding words publicReplies selections rows budget required stopAfter) computation state hvalid hinputs))
  calc
    _ ≤ ∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] = 0
      · simp only [hr, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hq result hr))
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.RetainedResidual
