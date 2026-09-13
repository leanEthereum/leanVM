import SphincsSecurity.Proof.Residual.RetainedResidualBankCompleteness
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest
set_option backward.isDefEq.respectTransparency false

def MonitoredAccounting {inputs : Finset HashInput} (state : MonitoredState inputs) : Prop :=
  state.2.stopped = false → state.2.spent = state.1.memory.external.hashCalls

private theorem update_spent_eq {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hbefore : MonitoredAccounting state) (length : Nat)
    (record : ProposalExecutionRecord input) (after : Memory)
    (hhash : after.external.hashCalls = state.1.memory.external.hashCalls + record.trace.hashCalls)
    (halive : (certificateMonitorUpdate key budget required stopAfter input (monitorView state) length record).stopped = false) :
    (certificateMonitorUpdate key budget required stopAfter input (monitorView state) length record).spent = after.external.hashCalls := by
  by_cases hactive : CertificateMonitorActive key budget input (monitorView state)
  · rw [certificateMonitorUpdate, if_pos hactive]
    change state.2.spent + record.trace.hashCalls = after.external.hashCalls
    rw [hbefore hactive.1, hhash]
  · rw [certificateMonitorUpdate_inactive _ _ _ _ _ _ _ _ hactive] at halive
    cases halive

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_accounting (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbefore : MonitoredAccounting state)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    MonitoredAccounting result.2 ∧
      state.1.memory.external.hashCalls + signingMacroHashCost input ≤ result.2.1.memory.external.hashCalls ∧
      result.2.1.memory.log.length = state.1.memory.log.length + if input.isRight then 1 else 0 := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hlog := lazyRun_externalProgram_log key inputs hencoding words publicReplies selections rows _ state.1 hvalid.1 raw hraw
      rw [lazyRun_externalProgram] at hraw
      have hhash := lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
        input hinputs state.1 hvalid.1 raw hraw
      have hcost : state.1.memory.external.hashCalls + signingMacroHashCost (.inl input) ≤ raw.2.memory.external.hashCalls := by
        rw [hhash]
        cases input <;> exact le_refl _
      refine ⟨?_, hcost, ?_⟩
      · cases hr : raw.1 with
        | none => intro halive; simp only [monitoredWorldResult, hr, Option.elim_none] at halive; cases halive
        | some answer =>
            intro halive
            simp only [monitoredWorldResult, hr, Option.elim_some] at halive ⊢
            apply update_spent_eq key budget required stopAfter (.inl input) state hbefore 0
              (proposalOfWorldResult key.parameter input (answer, raw.2.memory.external.cache)) raw.2.memory ?_ halive
            change raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + (signingBoundaryTrace key.parameter input answer).hashCalls
            rw [signingBoundaryTrace_hashCalls_eq]
            cases input <;> exact hhash
      · change raw.2.memory.log.length = state.1.memory.log.length + 0
        rw [hlog, Nat.add_zero]
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
      refine ⟨?_, ?_, ?_⟩
      · intro halive
        apply update_spent_eq key budget required stopAfter (.inr message) state hbefore annotation.1
          (proposalOfSigningRecord message record raw.2.memory.external.cache (record.1.2.elim annotation.2 Prod.fst))
          (raw.2.memory.recordSigning message record) ?_ halive
        rw [hm]; rfl
      · change state.1.memory.external.hashCalls + 1024 ≤ raw.2.memory.external.hashCalls
        rw [hm]
        change state.1.memory.external.hashCalls + 1024 ≤ state.1.memory.external.hashCalls + record.2.hashCalls
        omega
      · rw [hm]
        simp only [Memory.recordSigning, Memory.applyBoundary, List.length_append, List.length_singleton, Sum.isRight, if_true]

theorem monitoredRun_accounting {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbefore : MonitoredAccounting state)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    MonitoredAccounting result.2 ∧ state.1.memory.external.hashCalls ≤ result.2.1.memory.external.hashCalls ∧
      state.1.memory.log.length ≤ result.2.1.memory.log.length := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact ⟨hbefore, le_refl _, le_refl _⟩
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      obtain ⟨haccount, hcost, hlog⟩ := monitoredStep_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid ((requestInputs_subset key input next).trans hinputs) hbefore (answer, after) hstep
      have hcost' : state.1.memory.external.hashCalls ≤ after.1.memory.external.hashCalls := (Nat.le_add_right _ _).trans hcost
      have hlog' : state.1.memory.log.length ≤ after.1.memory.log.length := by rw [hlog]; exact Nat.le_add_right _ _
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact ⟨haccount, hcost', hlog'⟩
      | some answer =>
          obtain ⟨haccount', hcost'', hlog''⟩ := ih answer after
            (monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid (some answer, after) hstep)
            ((sourceInputs_next_subset key input next answer).trans hinputs) haccount hresult
          exact ⟨haccount', hcost'.trans hcost'', hlog'.trans hlog''⟩

theorem monitoredRun_query_conditions {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key (OracleSpec.query input >>= next) ⊆ inputs)
    (hbefore : MonitoredAccounting state) (hbank : MonitoredBankComplete key required state)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (OracleSpec.query input >>= next) state result ≠ 0)
    (hcost : result.2.1.memory.external.hashCalls ≤ budget) (hlog : result.2.1.memory.log.length ≤ signatureLimit)
    (halive : state.2.stopped = false) :
    ValidSigningStep state.2.log input ∧ signingMacroHashCost input ≤ budget - state.2.spent := by
  rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
  obtain ⟨haccount, hstepCost, hstepLog⟩ := monitoredStep_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state hvalid ((requestInputs_subset key input next).trans hinputs) hbefore (answer, after) hstep
  have hfuture : after.1.memory.external.hashCalls ≤ result.2.1.memory.external.hashCalls ∧
      after.1.memory.log.length ≤ result.2.1.memory.log.length := by
    cases answer with
    | none =>
        simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
        subst result
        exact ⟨le_refl _, le_refl _⟩
    | some answer =>
        exact (monitoredRun_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
          (next answer) after
          (monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid (some answer, after) hstep)
          ((sourceInputs_next_subset key input next answer).trans hinputs) haccount result hresult).2
  have havailable := hstepCost.trans (hfuture.1.trans hcost)
  have hcap := hfuture.2.trans hlog
  rw [hstepLog] at hcap
  constructor
  · rw [(hbank halive).1]
    cases input <;> simp only [ValidSigningStep, Sum.isRight, Bool.false_eq_true, if_false, if_true, Nat.add_zero] at hcap ⊢ <;> omega
  · rw [hbefore halive]
    omega

end SphincsSecurity.Concrete.RetainedResidual
