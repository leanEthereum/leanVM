import SphincsSecurity.Proof.Fts.CertificateBankCompleteness
import SphincsSecurity.Proof.Residual.RetainedResidualOriginalBudget
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest
set_option backward.isDefEq.respectTransparency false

def MonitoredBankComplete {inputs : Finset HashInput} (key : SecretKey) (required : Finset FtsTree)
    (state : MonitoredState inputs) : Prop :=
  state.2.stopped = false → state.2.log = state.1.memory.log ∧ CertificateBankComplete key required (monitorView state)

private theorem update_active_of_alive (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (halive : (certificateMonitorUpdate key budget required stopAfter input state length record).stopped = false) :
    CertificateMonitorActive key budget input state := by
  by_contra h
  rw [certificateMonitorUpdate_inactive key budget required stopAfter input state length record h] at halive
  contradiction

private theorem update_log_of_alive (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (halive : (certificateMonitorUpdate key budget required stopAfter input state length record).stopped = false) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).log =
      (proposalRecordLogState input state.2.log record).2 := by
  rw [certificateMonitorUpdate, if_pos (update_active_of_alive key budget required stopAfter input state length record halive)]

theorem monitoredWorldResult_bank_complete {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (before : MonitoredState inputs) (hbefore : MonitoredBankComplete key required before)
    (result : Option (OracleWorld.Range input) × State inputs) (hlog : result.2.memory.log = before.1.memory.log) :
    MonitoredBankComplete key required (monitoredWorldResult key budget required stopAfter input before result).2 := by
  rcases result with ⟨answer, after⟩
  change after.memory.log = before.1.memory.log at hlog
  cases answer with
  | none => intro halive; cases halive
  | some answer =>
      intro halive
      have hactive := update_active_of_alive key budget required stopAfter (.inl input) (monitorView before) 0
        (proposalOfWorldResult key.parameter input (answer, after.memory.external.cache)) halive
      have hlogBefore := (hbefore hactive.1).1
      constructor
      · have h := update_log_of_alive key budget required stopAfter (.inl input) (monitorView before) 0
          (proposalOfWorldResult key.parameter input (answer, after.memory.external.cache)) halive
        simpa only [proposalRecordLogState, signingLogFragment, List.append_nil, monitorView,
          monitoredWorldResult, Option.elim_some, hlogBefore, hlog] using h
      · exact certificateMonitorUpdate_bank_complete key budget required stopAfter (.inl input) (monitorView before) 0
          (proposalOfWorldResult key.parameter input (answer, after.memory.external.cache)) halive

theorem monitoredSigningResult_bank_complete {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message) (annotation : Nat × Index)
    (before : MonitoredState inputs) (hbefore : MonitoredBankComplete key required before)
    (result : Option SigningRecord × State inputs) (hlog : result.2.memory.log = before.1.memory.log) :
    MonitoredBankComplete key required (monitoredSigningResult key budget required stopAfter message annotation before result).2 := by
  rcases result with ⟨record, after⟩
  change after.memory.log = before.1.memory.log at hlog
  cases record with
  | none => intro halive; cases halive
  | some record =>
      intro halive
      have hactive := update_active_of_alive key budget required stopAfter (.inr message) (monitorView before) annotation.1
        (proposalOfSigningRecord message record after.memory.external.cache (record.1.2.elim annotation.2 Prod.fst)) halive
      have hlogBefore := (hbefore hactive.1).1
      constructor
      · have h := update_log_of_alive key budget required stopAfter (.inr message) (monitorView before) annotation.1
          (proposalOfSigningRecord message record after.memory.external.cache (record.1.2.elim annotation.2 Prod.fst)) halive
        simpa only [proposalRecordLogState, signingLogFragment, proposalOfSigningRecord, monitorView,
          monitoredSigningResult, Memory.recordSigning, hlogBefore, hlog] using h
      · exact certificateMonitorUpdate_bank_complete key budget required stopAfter (.inr message) (monitorView before) annotation.1
          (proposalOfSigningRecord message record after.memory.external.cache (record.1.2.elim annotation.2 Prod.fst)) halive

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_embed_log {Result : Type} (routing : Routing)
    (computation : OracleComp (ResidualByteFrontend.World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) computation) state result ≠ 0) : result.2.memory.log = state.memory.log := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact congrArg (fun history => history.2.1)
    (observedRun_embed_history key.parameter inputs hencoding words publicReplies selections rows routing actual seed computation state result hresult)

theorem lazyRun_externalProgram_log {Result : Type} (computation : OracleComp OracleWorld Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections computation) state result ≠ 0) : result.2.memory.log = state.memory.log := by
  rw [externalProgram, lazyRun_routing_bind] at hresult
  exact lazyRun_embed_log key inputs hencoding words publicReplies selections rows _ _ state ha result hresult

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_bank_complete (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (ha : ∀ coordinate, (state.1.candidates coordinate).Nonempty) (hbefore : MonitoredBankComplete key required state)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    MonitoredBankComplete key required result.2 := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact monitoredWorldResult_bank_complete key budget required stopAfter input state hbefore raw
        (lazyRun_externalProgram_log key inputs hencoding words publicReplies selections rows _ state.1 ha raw hraw)
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact monitoredSigningResult_bank_complete key budget required stopAfter message annotation state hbefore raw
        (lazyRun_embed_log key inputs hencoding words publicReplies selections rows _ _ state.1 ha raw hraw)

theorem monitoredRun_bank_complete {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state) (hbefore : MonitoredBankComplete key required state)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    MonitoredBankComplete key required result.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [monitoredRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbefore
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hafter, hresult⟩ := hresult
      have hbank := monitoredStep_bank_complete key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid.1 hbefore (answer, after) hafter
      have hvalid' := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid (answer, after) hafter
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hbank
      | some answer => exact ih answer after hvalid' hbank hresult

theorem monitoredBankComplete_initial (exposed : InitialPublicLabels words) (spent : Nat) (stopped : Bool) :
    MonitoredBankComplete key required (initialState inputs words exposed, initialCertificateMonitor spent stopped) := by
  intro _
  exact ⟨rfl, initialCertificateMonitor_bank_complete key spent required _ stopped (fun _ _ => rfl)⟩

theorem initialMonitoredSource_bank_complete (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (stopped : Bool)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped result ≠ 0) :
    MonitoredBankComplete key required result.2 := by
  exact monitoredRun_bank_complete key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget required stopAfter _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (monitoredBankComplete_initial key _ _ required exposed 1212415 stopped) result hresult

theorem initialMonitoredSource_certificate_count (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (stopped : Bool)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped result ≠ 0)
    (halive : result.2.2.stopped = false) (input : HashInput)
    (hcertificate : TargetCertificateAt key required (result.2.1.memory.external.cache, result.2.1.memory.log) input) :
    1 ≤ certificateBankCount result.2.2.bank := by
  obtain ⟨hlog, hbank⟩ := initialMonitoredSource_bank_complete key budget required stopAfter adversary encoding dummy exposed high stopped result hresult halive
  apply one_le_certificateBankCount _ input
  apply hbank input
  change TargetCertificateAt key required (result.2.1.memory.external.cache, result.2.2.log) input
  rwa [hlog]

end SphincsSecurity.Concrete.RetainedResidual
