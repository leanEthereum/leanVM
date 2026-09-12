import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredCoverage
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_bind_const {Other : Type} (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (ha : ∀ coordinate, (state.1.candidates coordinate).Nonempty) (after : SPMF Other) :
    (monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun _ => after) = after := by
  have h := lazyRun_bind_const (environment key.parameter inputs hencoding words publicReplies selections rows)
    (adversaryImpl inputs key.parameter key.root words selections input) state.1 ha after
  rw [← monitoredStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state,
    bind_map_left] at h
  exact h

theorem tsum_monitoredStep_eq_one (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (ha : ∀ coordinate, (state.1.candidates coordinate).Nonempty) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (monitoredStep_bind_const key inputs hencoding words publicReplies selections rows budget required stopAfter input state ha (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram
  certificateMonitorCharge certificateMonitorMass certificateMonitorUpdate monitorView monitoredSigningResult

theorem stopped_world_message_charges_zero (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (hinputs : requestInputs key (.inl input) ⊆ inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state.1))
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state.1 result ≠ 0)
    (hnone : result.1 = none) :
    freshWorldTargetHashCost key.parameter state.1.memory.external.cache input = 0 ∧
      hashQueryCharge (FtsProbeSimulation.messageHashCharge key.parameter) state.1.memory.external.cache input = 0 := by
  cases input with
  | inl input => exact ⟨rfl, rfl⟩
  | inr input =>
      by_cases hm : MessageHashInput key.parameter input
      · rw [lazyRun_externalProgram] at hresult
        have h := map_nonzero _ cacheResult result hresult
        rw [lazyByteRun_world_message_rom key.parameter inputs hencoding words publicReplies selections rows
          state.1.memory.routing (.inr input) hinputs (fun hash heq => by cases heq; exact hm) state.1 hcovered,
          map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at h
        obtain ⟨answer, _, h⟩ := h
        simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
        have hs := congrArg Prod.fst h
        simp only [cacheResult, hnone, Prod.map_fst] at hs
        contradiction
      · simp only [freshWorldTargetHashCost, hm, false_and, if_false, hashQueryCharge, Sum.elim_inr,
          FtsProbeSimulation.messageHashCharge, and_self]

theorem monitoredStep_creation_counters (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    result.2.2.creationCost = state.2.creationCost + certificateMonitorCharge key budget required input (monitorView state) ∧
    result.2.2.creationMass = state.2.creationMass + certificateMonitorMass key budget input (monitorView state) := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      by_cases hn : raw.1 = none
      · have hz := (stopped_world_message_charges_zero key inputs hencoding words publicReplies selections rows input state hinputs hvalid.2 raw hraw hn).1
        have hc : certificateMonitorCharge key budget required (.inl input) (monitorView state) = 0 := by
          unfold certificateMonitorCharge targetCreationMultiplier monitorView
          simp only [hz, Nat.cast_zero, zero_mul, ite_self]
        have hm : certificateMonitorMass key budget (.inl input) (monitorView state) = 0 := by
          unfold certificateMonitorMass targetCreationMultiplier monitorView
          simp only [hz, Nat.cast_zero, ite_self]
        simp only [monitoredWorldResult, hn, Option.elim_none, hc, hm, add_zero, and_self]
      · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hn
        simp only [monitoredWorldResult, ha, Option.elim_some]
        rw [certificateMonitorUpdate_creationCost, certificateMonitorUpdate_creationMass]
        simp only [monitorView, and_self]
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
      obtain ⟨record, hr⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
        state.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state.1 hvalid.1 hvalid.2 raw hraw
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      simp only [monitoredSigningResult]
      rw [certificateMonitorUpdate_creationCost, certificateMonitorUpdate_creationMass]
      simp only [monitorView, and_self]

theorem expected_monitoredStep_creationCost (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      result.2.2.creationCost) = state.2.creationCost + certificateMonitorCharge key budget required input (monitorView state) := by
  calc
    _ = ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        (state.2.creationCost + certificateMonitorCharge key budget required input (monitorView state)) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(monitoredStep_creation_counters key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state hvalid hinputs result hr).1]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_monitoredStep_eq_one key inputs hencoding words publicReplies selections rows
        budget required stopAfter input state hvalid.1, one_mul]

noncomputable def expectedMonitoredPayment
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) : MonitoredState inputs → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    charge input (monitorView state) +
      ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        result.1.elim 0 (fun answer => next answer result.2)) computation

theorem expected_monitoredRun_accumulator (counter : CertificateMonitor → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state, MonitoredValid inputs state → requestInputs key input ⊆ inputs →
      (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        counter result.2.2) = counter state.2 + charge input (monitorView state))
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      counter result.2.2) = counter state.2 +
        expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [monitoredRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul]
      change _ = counter state.2 + (charge input (monitorView state) +
        ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
          result.1.elim 0 (fun answer =>
            expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2))
      calc
        _ = ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (counter result.2.2 + result.1.elim 0 (fun answer =>
              expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2)) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hafter := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
              input state hvalid result hr
            apply congrArg (_ * ·)
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, add_zero]
            | some answer => exact ih answer after hafter ((sourceInputs_next_subset key input next answer).trans hinputs)
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [hstep input state hvalid ((requestInputs_subset key input next).trans hinputs), add_assoc]

theorem expectedMonitoredPayment_mono
    (first second : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hle : ∀ input state, first input state ≤ second input state)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState inputs) :
    expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter first computation state ≤
      expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter second computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      apply add_le_add (hle input (monitorView state))
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, after⟩
      apply mul_le_mul' le_rfl
      cases answer with
      | none => exact le_rfl
      | some answer => exact ih answer after

theorem expected_monitoredRun_creationCost {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      result.2.2.creationCost) = state.2.creationCost +
        expectedMonitoredCharge key inputs hencoding words publicReplies selections rows budget required stopAfter computation state :=
  expected_monitoredRun_accumulator key inputs hencoding words publicReplies selections rows budget required stopAfter
    CertificateMonitor.creationCost (certificateMonitorCharge key budget required)
    (expected_monitoredStep_creationCost key inputs hencoding words publicReplies selections rows budget required stopAfter)
    computation state hvalid hinputs

theorem expected_monitoredRun_count_le_creationCost {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : State inputs) (spent : Nat) (stopped : Bool)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hinputs : sourceInputs key computation ⊆ inputs)
    (hnone : ∀ input, MessageHashInput key.parameter input → state.memory.external.cache input = none) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.bank) ≤
      ∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped)] * result.2.2.creationCost := by
  rw [expected_monitoredRun_creationCost key inputs hencoding words publicReplies selections rows budget required stopAfter computation
    (state, initialCertificateMonitor spent stopped) ⟨ha, hcovered⟩ hinputs]
  simp only [initialCertificateMonitor, zero_add]
  exact expected_monitoredRun_count_le_charge key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state spent stopped ha hcovered hinputs hnone

end SphincsSecurity.Concrete.RetainedResidual
