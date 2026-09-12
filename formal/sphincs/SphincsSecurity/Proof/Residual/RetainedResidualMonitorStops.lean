import SphincsSecurity.Proof.Residual.RetainedResidualMonitorReadiness
import SphincsSecurity.Proof.Residual.RetainedResidualProposalInvariant
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_record (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0)
    (hlive : result.1 ≠ none) :
    ∃ (length : Nat) (record : ProposalExecutionRecord input), result.1 = some record.output ∧
      result.2.2 = certificateMonitorUpdate key budget required stopAfter input (monitorView state) length record ∧
      record.cache = result.2.1.memory.external.cache ∧
      result.2.1.memory.log = (proposalRecordLogState input state.1.memory.log record).2 ∧
      result.2.1.memory.external.hashCalls = state.1.memory.external.hashCalls + record.trace.hashCalls := by
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
      cases hr : raw.1 with
      | none => exact False.elim (hlive hr)
      | some answer =>
          refine ⟨0, proposalOfWorldResult key.parameter input (answer, raw.2.memory.external.cache), ?_, ?_, rfl, ?_, ?_⟩
          · exact hr
          · simp only [monitoredWorldResult, hr, Option.elim_some]
          · simpa only [monitoredWorldResult, proposalRecordLogState, signingLogFragment, List.append_nil] using hlog
          · change raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + (signingBoundaryTrace key.parameter input answer).hashCalls
            rw [signingBoundaryTrace_hashCalls_eq]
            cases input <;> exact hhash
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
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      refine ⟨annotation.1, proposalOfSigningRecord message record raw.2.memory.external.cache
        (record.1.2.elim annotation.2 Prod.fst), rfl, rfl, rfl, ?_, ?_⟩
      · change raw.2.memory.log ++ [⟨message, record.1.1⟩] = state.1.memory.log ++ [⟨message, record.1.1⟩]
        rw [hm]; rfl
      · change raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + record.2.hashCalls
        rw [hm]; rfl

theorem monitoredStep_active_accounting (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbefore : MonitoredAccounting state) (hbank : MonitoredBankComplete key required state)
    (hactive : CertificateMonitorActive key budget input (monitorView state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0)
    (hlive : result.1 ≠ none) :
    result.2.2.spent = result.2.1.memory.external.hashCalls ∧ result.2.2.log = result.2.1.memory.log := by
  obtain ⟨length, record, _, hmonitor, _, hlog, hhash⟩ :=
    monitoredStep_record key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid hinputs result hresult hlive
  rw [hmonitor, certificateMonitorUpdate, if_pos hactive]
  constructor
  · change state.2.spent + record.trace.hashCalls = result.2.1.memory.external.hashCalls
    rw [hbefore hactive.1, hhash]
  · change (proposalRecordLogState input state.2.log record).2 = result.2.1.memory.log
    rw [(hbank hactive.1).1, hlog]

theorem monitoredStep_ready_after (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbefore : MonitoredAccounting state) (hbank : MonitoredBankComplete key required state)
    (hsize : CacheSizeBound state.1.memory)
    (hsigned : SigningDigestsCached key.parameter state.1.memory.external.cache key.root state.1.memory.log)
    (hactive : CertificateMonitorActive key budget input (monitorView state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0)
    (hlive : result.1 ≠ none) (hcost : result.2.1.memory.external.hashCalls ≤ budget) (hbudget : budget ≤ 2 ^ 127)
    (hclean : ¬ CertificateCacheExceptional key result.2.1.memory.external.cache) :
    CertificateMonitorReady key budget (monitorView result.2) := by
  obtain ⟨hspent, hlog⟩ := monitoredStep_active_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state hvalid hinputs hbefore hbank hactive result hresult hlive
  have hsize' := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state hvalid hinputs hsize result hresult
  have hsigned' := monitoredStep_digestsCached key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state hvalid hinputs hsigned result hresult
  change SigningDigestsCached key.parameter result.2.1.memory.external.cache key.root result.2.2.log ∧
    ProposalCacheBound key result.2.1.memory.external.cache result.2.2.spent ∧ result.2.2.spent ≤ budget
  rw [hspent, hlog]
  exact ⟨hsigned', proposalCacheBound_of_no_cache_exception key _ (Finite.of_enncard_le hsize') _
    (hcost.trans hbudget) hsize' hclean, hcost⟩

private theorem update_stopped_eq (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state)
    (hready : CertificateMonitorReady key budget
      (record.cache, certificateMonitorUpdate key budget required stopAfter input state length record)) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).stopped = stopAfter input state length record := by
  unfold certificateMonitorUpdate at hready ⊢
  rw [if_pos hactive] at hready ⊢
  simp only [CertificateMonitorReady] at hready ⊢
  simp only [hready, and_self, not_true_eq_false, decide_false, Bool.or_false]

omit stopAfter in
theorem monitoredStep_stopped_iff_prefix (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbefore : MonitoredAccounting state) (hbank : MonitoredBankComplete key required state)
    (hsize : CacheSizeBound state.1.memory)
    (hsigned : SigningDigestsCached key.parameter state.1.memory.external.cache key.root state.1.memory.log)
    (hactive : CertificateMonitorActive key budget input (monitorView state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required (proposalStop (fun _ _ _ _ => false))
      input state result ≠ 0)
    (hlive : result.1 ≠ none) (hcost : result.2.1.memory.external.hashCalls ≤ budget) (hbudget : budget ≤ 2 ^ 127)
    (hclean : ¬ CertificateCacheExceptional key result.2.1.memory.external.cache) :
    result.2.2.stopped = true ↔ ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length := by
  let stop : CertificateStopRule := proposalStop (fun _ _ _ _ => false)
  have hready := monitoredStep_ready_after key inputs hencoding words publicReplies selections rows budget required stop input state
    hvalid hinputs hbefore hbank hsize hsigned hactive result hresult hlive hcost hbudget hclean
  obtain ⟨length, record, _, hmonitor, hcache, _, _⟩ :=
    monitoredStep_record key inputs hencoding words publicReplies selections rows budget required stop input state hvalid hinputs result hresult hlive
  have hready' : CertificateMonitorReady key budget
      (record.cache, certificateMonitorUpdate key budget required stop input (monitorView state) length record) := by
    rw [hcache, ← hmonitor]
    exact hready
  have hstop := update_stopped_eq key budget required stop input (monitorView state) length record hactive hready'
  have hprefix := proposalPrefixStop_eq_after_exception key budget required stop input (monitorView state) length record hactive
  rw [← hmonitor] at hstop hprefix
  simp only [hstop, stop, proposalStop, Bool.or_false, hprefix, decide_eq_true_eq]

end SphincsSecurity.Concrete.RetainedResidual
