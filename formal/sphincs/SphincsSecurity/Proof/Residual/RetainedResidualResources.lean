import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualBoundaryCost
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredErasure
import SphincsSecurity.Proof.Residual.RetainedResidualWorkCost
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

def MonitorResources (monitor : CertificateMonitor) (memory : Memory) : Prop :=
  monitor.spent ≤ memory.external.hashCalls ∧ monitor.creationMass ≤ (memory.external.hashCalls : ENNReal) ∧
    monitor.messageCalls ≤ memory.messageCalls.length

theorem monitorResources_mono (monitor : CertificateMonitor) (before after : Memory)
    (h : MonitorResources monitor before) (hhash : before.external.hashCalls ≤ after.external.hashCalls)
    (hmessage : before.messageCalls.length ≤ after.messageCalls.length) : MonitorResources monitor after :=
  ⟨h.1.trans hhash, h.2.1.trans (Nat.cast_le.mpr hhash), h.2.2.trans hmessage⟩

theorem monitorResources_update (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) {inputs : Finset HashInput} (state : MonitoredState inputs)
    (length : Nat) (record : ProposalExecutionRecord input) (after : Memory)
    (hresources : MonitorResources state.2 state.1.memory)
    (hhash : after.external.hashCalls = state.1.memory.external.hashCalls + record.trace.hashCalls)
    (hmessage : after.messageCalls = state.1.memory.messageCalls ++ record.trace.messageCalls)
    (hmass : targetCreationMultiplier key state.1.memory.external.cache input ≤ record.trace.hashCalls) :
    MonitorResources (certificateMonitorUpdate key budget required stopAfter input (monitorView state) length record) after := by
  by_cases ha : CertificateMonitorActive key budget input (monitorView state)
  · rw [certificateMonitorUpdate, if_pos ha]
    simp only [MonitorResources, monitorView]
    rw [hhash, hmessage, List.length_append, Nat.cast_add]
    exact ⟨Nat.add_le_add_right hresources.1 _, add_le_add hresources.2.1 hmass, Nat.add_le_add_right hresources.2.2 _⟩
  · rw [certificateMonitorUpdate_inactive _ _ _ _ _ _ _ _ ha]
    change MonitorResources state.2 after
    apply monitorResources_mono _ _ _ hresources
    · rw [hhash]; exact Nat.le_add_right _ _
    · rw [hmessage, List.length_append]; exact Nat.le_add_right _ _

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram
  certificateMonitorUpdate monitorView monitoredSigningResult

theorem monitoredStep_resources (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) (hresources : MonitorResources state.2 state.1.memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    MonitorResources result.2.2 result.2.1.memory := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      rw [lazyRun_externalProgram] at hraw
      have hh := lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
        input hinputs state.1 hvalid.1 raw hraw
      have hm := lazyByteRun_world_messageTrace key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
        input hinputs state.1 hvalid.1 raw hraw
      cases hr : raw.1 with
      | none =>
          simp only [monitoredWorldResult, hr, Option.elim_none]
          change MonitorResources state.2 raw.2.memory
          apply monitorResources_mono _ _ _ hresources
          · rw [hh]; exact Nat.le_add_right _ _
          · rw [hm, hr, Option.elim_none, List.append_nil]
      | some answer =>
          simp only [monitoredWorldResult, hr, Option.elim_some]
          apply monitorResources_update key budget required stopAfter (.inl input) state 0 _ raw.2.memory hresources
          · change raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + (signingBoundaryTrace key.parameter input answer).hashCalls
            rw [signingBoundaryTrace_hashCalls_eq]
            cases input <;> exact hh
          · change raw.2.memory.messageCalls = state.1.memory.messageCalls ++ (signingBoundaryTrace key.parameter input answer).messageCalls
            simpa only [hr, Option.elim_some] using hm
          · simp only [proposalOfWorldResult, signingBoundaryTrace_hashCalls_eq, targetCreationMultiplier]
            cases input with
            | inl sample => exact le_rfl
            | inr input =>
                simp only [freshWorldTargetHashCost]
                split_ifs <;> norm_num
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
      obtain ⟨record, hr, hm⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state.1 hvalid.1 hvalid.2 raw hraw
      obtain ⟨other, ho, hmin⟩ := lazyRun_jointSigningProgram_hashCalls_min key inputs hencoding words publicReplies selections rows
        state.1.memory.routing message hin state.1 hvalid.1 hvalid.2 raw hraw
      have heq : other = record := Option.some.inj (ho.symm.trans hr)
      subst other
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      simp only [monitoredSigningResult]
      apply monitorResources_update key budget required stopAfter (.inr message) state annotation.1 _
        (raw.2.memory.recordSigning message record) hresources
      · rw [hm]; rfl
      · rw [hm]; rfl
      · change targetCreationMultiplier key state.1.memory.external.cache (.inr message) ≤ record.2.hashCalls
        have hp := mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)))
          (freshDigestSelectionProbability_le_one key message state.1.memory.external.cache)
        calc
          _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by simpa only [targetCreationMultiplier, mul_one] using hp
          _ ≤ (28504 : Nat) := by norm_num [ftsTreeHeight]
          _ ≤ record.2.hashCalls := Nat.cast_le.mpr hmin

theorem monitoredRun_resources {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) (hresources : MonitorResources state.2 state.1.memory)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    MonitorResources result.2.2 result.2.1.memory := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hresources
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      have hafter := monitoredStep_resources key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid ((requestInputs_subset key input next).trans hinputs) hresources (answer, after) hstep
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hafter
      | some answer =>
          exact ih answer after
            (monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid (some answer, after) hstep)
            ((sourceInputs_next_subset key input next answer).trans hinputs) hafter result hresult

end SphincsSecurity.Concrete.RetainedResidual
