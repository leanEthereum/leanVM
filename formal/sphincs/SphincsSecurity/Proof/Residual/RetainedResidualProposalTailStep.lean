import SphincsSecurity.Proof.Residual.RetainedResidualExceptionHistory
import SphincsSecurity.Proof.Fts.ProposalPrefixExponential
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

private theorem update_log_cap (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat) (record : ProposalExecutionRecord input)
    (hcap : state.2.log.length ≤ signatureLimit) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).log.length ≤ signatureLimit := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [certificateMonitorUpdate, if_pos hactive]
    have hvalid := hactive.2.2.1
    cases input <;>
      simp only [proposalRecordLogState, signingLogFragment, List.append_nil, List.length_append, List.length_singleton, ValidSigningStep] at hvalid ⊢ <;> omega
  · simpa only [certificateMonitorUpdate, if_neg hactive] using hcap

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_log_cap (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hcap : state.2.log.length ≤ signatureLimit)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    result.2.2.log.length ≤ signatureLimit := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, _, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      cases hr : raw.1 with
      | none => simpa only [monitoredWorldResult, hr, Option.elim_none] using hcap
      | some answer =>
          simp only [monitoredWorldResult, hr, Option.elim_some]
          exact update_log_cap key budget required stopAfter (.inl input) (monitorView state) 0 _ hcap
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, _, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      cases hr : raw.1 with
      | none => simpa only [monitoredSigningResult, hr] using hcap
      | some record =>
          simp only [monitoredSigningResult, hr]
          exact update_log_cap key budget required stopAfter (.inr message) (monitorView state) annotation.1 _ hcap

private theorem world_weight (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (raw : Option (OracleWorld.Range input) × State inputs) :
    proposalPrefixWeight (monitoredWorldResult key budget required stopAfter input state raw).2.2.proposals
      (monitoredWorldResult key budget required stopAfter input state raw).2.2.log.length =
      proposalPrefixWeight state.2.proposals state.2.log.length := by
  cases hr : raw.1 with
  | none => simp only [monitoredWorldResult, hr, Option.elim_none]
  | some answer =>
      simp only [monitoredWorldResult, hr, Option.elim_some, certificateMonitorUpdate]
      split <;> simp only [proposalRecordLogState, signingLogFragment, List.append_nil, Nat.add_zero, monitorView]

private theorem signing_weight (message : Message) (annotation : Nat × Index) (state : MonitoredState inputs)
    (record : SigningRecord) (after : State inputs) :
    proposalPrefixWeight (monitoredSigningResult key budget required stopAfter message annotation state (some record, after)).2.2.proposals
      (monitoredSigningResult key budget required stopAfter message annotation state (some record, after)).2.2.log.length =
      if CertificateMonitorActive key budget (.inr message) (monitorView state) then
        proposalPrefixWeight (state.2.proposals + annotation.1) (state.2.log.length + 1)
      else proposalPrefixWeight state.2.proposals state.2.log.length := by
  simp only [monitoredSigningResult, certificateMonitorUpdate]
  split <;> simp only [proposalRecordLogState, signingLogFragment, List.length_append, List.length_singleton, monitorView]

theorem expected_monitoredStep_prefixWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      proposalPrefixWeight result.2.2.proposals result.2.2.log.length) ≤ proposalPrefixWeight state.2.proposals state.2.log.length := by
  cases input with
  | inl input =>
      rw [monitoredStep, tsum_probOutput_map_mul]
      simp only [world_weight, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr message =>
      rw [monitoredStep, tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_map_mul]
      let law := lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.1.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1
      have hraw (annotation : Nat × Index) :
          (∑' raw, Pr[= raw | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (simulateQ (embed inputs state.1.memory.routing)
              (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1] *
            proposalPrefixWeight (monitoredSigningResult key budget required stopAfter message annotation state raw).2.2.proposals
              (monitoredSigningResult key budget required stopAfter message annotation state raw).2.2.log.length) ≤
          if CertificateMonitorActive key budget (.inr message) (monitorView state) then
            proposalPrefixWeight (state.2.proposals + annotation.1) (state.2.log.length + 1)
          else proposalPrefixWeight state.2.proposals state.2.log.length := by
        apply le_trans ?_ (mul_le_of_le_one_left' (show (∑' raw, Pr[= raw | law]) ≤ 1 from tsum_probOutput_le_one))
        rw [← ENNReal.tsum_mul_right]
        apply ENNReal.tsum_le_tsum
        intro raw
        by_cases hr : Pr[= raw | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (simulateQ (embed inputs state.1.memory.routing)
              (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1] = 0
        · simp only [law, hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          obtain ⟨record, heq⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
            state.1.memory.routing key.root message
            (by simpa only [publicDigestLoop_eq] using digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs)
            state.1 hvalid.1 hvalid.2 raw hr
          have hpair : raw = (some record, raw.2) := Prod.ext heq rfl
          rw [hpair, signing_weight]
      apply le_trans (ENNReal.tsum_le_tsum fun annotation => mul_le_mul' le_rfl (hraw annotation))
      by_cases hactive : CertificateMonitorActive key budget (.inr message) (monitorView state)
      · simp only [if_pos hactive, SPMF.probOutput_liftM]
        rw [signingAnnotation, if_pos hactive, ← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
        simp_rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
        exact (expected_proposalPrefixWeight state.2.proposals state.2.log.length hactive.2.2.1).le
      · simp only [if_neg hactive, ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.RetainedResidual
