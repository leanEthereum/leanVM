import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredErasure
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def expectedMonitoredCharge {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) : MonitoredState inputs → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    certificateMonitorCharge key budget required input (monitorView state) +
      ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        result.1.elim 0 (fun answer => next answer result.2)) computation

theorem expectedMonitoredCharge_pure {Result : Type} (value : Result) (state : MonitoredState inputs) :
    expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter (pure value) state = 0 := rfl

theorem expectedMonitoredCharge_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) :
    expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      certificateMonitorCharge key budget required input (monitorView state) +
        ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
          result.1.elim 0 (fun answer =>
            expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2) := rfl

theorem expected_monitoredRun_potential_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      certificateMonitorPotential key budget required (monitorView result.2)) ≤
      certificateMonitorPotential key budget required (monitorView state) +
        expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [monitoredRun_pure, tsum_probOutput_pure_mul, expectedMonitoredCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul, expectedMonitoredCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (certificateMonitorPotential key budget required (monitorView result.2) + result.1.elim 0 (fun answer =>
              expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hafter := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid result hr
            apply mul_le_mul' le_rfl
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, add_zero, le_refl]
            | some answer =>
                exact ih answer after hafter ((sourceInputs_next_subset key input next answer).trans hinputs)
        _ = (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            certificateMonitorPotential key budget required (monitorView result.2)) +
            ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
              result.1.elim 0 (fun answer =>
                expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2) := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ _ := by
          rw [← add_assoc]
          exact add_le_add (expected_monitoredStep_potential_le key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state ((requestInputs_subset key input next).trans hinputs) hvalid.1 hvalid.2) le_rfl

theorem expected_monitoredRun_count_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      certificateBankCount result.2.2.bank) ≤
      certificateMonitorPotential key budget required (monitorView state) +
        expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter computation state := by
  apply le_trans ?_ (expected_monitoredRun_potential_le key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state hvalid hinputs)
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem expected_monitoredRun_count_le_charge {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : State inputs) (spent : Nat) (stopped : Bool)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hinputs : sourceInputs key computation ⊆ inputs)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → state.memory.external.cache input = none) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.bank) ≤
      expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped) := by
  have h := expected_monitoredRun_count_le key inputs hencoding words publicReplies selections rows budget required stopAfter computation
    (state, initialCertificateMonitor spent stopped) ⟨ha, hcovered⟩ hinputs
  simpa only [monitorView, certificateMonitorPotential_initial key budget spent required state.memory.external.cache stopped hnone, zero_add] using h

end SphincsSecurity.Concrete.RetainedResidual
