import SphincsSecurity.Proof.Forced.FtsGuessExceptionWeights
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult proposalStop)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete signDigestLoop
  certificateCacheExceptionWeight

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

/-! ### Step records and macro costs -/

theorem monitoredStep_update (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      result ≠ 0) :
    ∃ (length : Nat) (record : ProposalExecutionRecord input),
      result.2.2 = certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input (monitorView state) length record ∧
        record.cache = result.2.1.1 ∧ record.trace = result.1.1.2 ∧ record.output = result.1.1.1 := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ⟨0, proposalOfWorldResult parameter input (raw.1, raw.2.1), rfl, rfl, rfl, rfl⟩
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ⟨annotation.1, proposalOfSigningRecord message raw.1 raw.2.1 (raw.1.1.2.elim annotation.2 Prod.fst), rfl, rfl, rfl, rfl⟩

theorem monitoredStep_macro (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      result ≠ 0) : signingMacroHashCost input ≤ result.1.1.2.hashCalls := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      cases input with
      | inl sample => exact Nat.zero_le _
      | inr hash =>
          change 1 ≤ (signingBoundaryTrace parameter (.inr hash) raw.1).hashCalls
          simp only [signingBoundaryTrace, SigningBoundaryTrace.hashCalls_of, le_refl]
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
      obtain ⟨source, hsource, htrace, _⟩ := forcedSigning_source parameter root otsSecret labels inputs hencoding selections rows dummy slot
        message state hvalid (hsign message rfl) raw hraw
      have hmin := publicSigningWork_hashCalls_min' parameter root (monitorKey parameter root) rfl rfl (known otsSecret labels)
        (referenceFamilyWords selections dummy) selections message state.1.1 source hsource
      change 1024 ≤ raw.1.2.hashCalls
      rw [htrace]
      exact (show 1024 ≤ 28504 by decide).trans hmin

/-! ### Consistency of an unstopped monitor with its cache -/

def Consistent (state : MonitoredState) : Prop :=
  QueryCache.enncard state.1.1 ≤ state.2.spent ∧ SigningDigestsCached parameter state.1.1 root state.2.log

private theorem update_stopped_eq (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) (hactive : CertificateMonitorActive (monitorKey parameter root) budget input state)
    (hready : CertificateMonitorReady (monitorKey parameter root) budget
      (record.cache, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record)) :
    (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).stopped =
      stopAfter input state length record := by
  unfold certificateMonitorUpdate at hready ⊢
  rw [if_pos hactive] at hready ⊢
  simp only [CertificateMonitorReady] at hready ⊢
  simp only [hready, and_self, not_true_eq_false, decide_false, Bool.or_false]

private theorem update_log_of_active (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) (hactive : CertificateMonitorActive (monitorKey parameter root) budget input state) :
    (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).log =
      state.2.log ++ signingLogFragment input record.output := by
  rw [certificateMonitorUpdate, if_pos hactive]
  rfl

theorem exceptionStep_unstopped (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState) (hvalid : Valid state.1)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hcons : Consistent parameter root state.1) (halive : state.1.2.stopped = false) (hbudget : budget ≤ 2 ^ 127)
    (result : AdversaryStep input × ExceptionState)
    (hresult : exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) input state result ≠ 0)
    (hcost : state.1.2.spent + result.1.1.2.hashCalls ≤ budget)
    (hlog : state.1.2.log.length + (signingLogFragment input result.1.1.1).length ≤ signatureLimit)
    (hclean : state.2 = (false, false)) (hcleanAfter : result.2.2 = (false, false)) :
    result.2.1.2.stopped = false ∧ Consistent parameter root result.2.1 := by
  obtain ⟨hmon, hupdate⟩ := exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) input state result hresult
  rw [hupdate, hclean] at hcleanAfter
  simp only [exceptionUpdate, Prod.mk.injEq, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hcleanAfter
  obtain ⟨⟨hbefore, hafter⟩, hprefix⟩ := hcleanAfter
  have haccount := monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) input state.1 hvalid hworld hsign (result.1, result.2.1) hmon
  have hmacro := monitoredStep_macro parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) input state.1 hvalid hsign (result.1, result.2.1) hmon
  change signingMacroHashCost input ≤ result.1.1.2.hashCalls at hmacro
  obtain ⟨length, record, hmonitor, hcache, htrace, houtput⟩ := monitoredStep_update parameter root otsSecret labels inputs hencoding selections
    rows dummy slot budget required (proposalStop (fun _ _ _ _ => false)) input state.1 (result.1, result.2.1) hmon
  change result.2.1.2 = _ at hmonitor
  change record.cache = result.2.1.1.1 at hcache
  change record.trace = result.1.1.2 at htrace
  change record.output = result.1.1.1 at houtput
  have hspentLe : state.1.2.spent ≤ budget := by omega
  have hactive : CertificateMonitorActive (monitorKey parameter root) budget input (monitorView state.1) := by
    refine ⟨halive, ⟨hcons.2, ?_, hspentLe⟩, ?_, ?_⟩
    · exact proposalCacheBound_of_no_cache_exception (monitorKey parameter root) state.1.1.1 (Finite.of_enncard_le hcons.1) state.1.2.spent
        (by omega) hcons.1 hbefore
    · cases input with
      | inl input =>
          change state.1.2.log.length ≤ signatureLimit
          simpa only [signingLogFragment, List.length_nil, Nat.add_zero] using hlog
      | inr message =>
          change state.1.2.log.length < signatureLimit
          simp only [signingLogFragment, List.length_singleton] at hlog
          omega
    · change signingMacroHashCost input ≤ budget - state.1.2.spent
      omega
  have hnewSpent : (certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop (fun _ _ _ _ => false)) input
      (monitorView state.1) length record).spent = state.1.2.spent + result.1.1.2.hashCalls := by
    rw [certificateMonitorUpdate_spent (monitorKey parameter root) budget required _ input (monitorView state.1) length record hactive, htrace]
    rfl
  have hnewLog : (certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop (fun _ _ _ _ => false)) input
      (monitorView state.1) length record).log = state.1.2.log ++ signingLogFragment input result.1.1.1 := by
    rw [update_log_of_active parameter root budget required _ input (monitorView state.1) length record hactive, houtput]
    rfl
  have hready : CertificateMonitorReady (monitorKey parameter root) budget
      (record.cache, certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop (fun _ _ _ _ => false)) input
        (monitorView state.1) length record) := by
    refine ⟨?_, ?_, ?_⟩
    · change SigningDigestsCached parameter record.cache root (certificateMonitorUpdate (monitorKey parameter root) budget required
        (proposalStop (fun _ _ _ _ => false)) input (monitorView state.1) length record).log
      rw [hnewLog, hcache]
      exact haccount.digests state.1.2.log hcons.2
    · change ProposalCacheBound (monitorKey parameter root) record.cache (certificateMonitorUpdate (monitorKey parameter root) budget required
        (proposalStop (fun _ _ _ _ => false)) input (monitorView state.1) length record).spent
      rw [hnewSpent, hcache]
      have hcard : QueryCache.enncard result.2.1.1.1 ≤ ((state.1.2.spent + result.1.1.2.hashCalls : Nat) : ENNReal) := by
        rw [Nat.cast_add]
        exact haccount.enncard.trans (add_le_add hcons.1 le_rfl)
      exact proposalCacheBound_of_no_cache_exception (monitorKey parameter root) _ (Finite.of_enncard_le hcard) _ (by omega) hcard hafter
    · change (certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop (fun _ _ _ _ => false)) input
        (monitorView state.1) length record).spent ≤ budget
      rw [hnewSpent]
      exact hcost
  have hstop := update_stopped_eq parameter root budget required (proposalStop (fun _ _ _ _ => false)) input (monitorView state.1) length record
    hactive hready
  have hprefixStop := proposalPrefixStop_eq_after_exception (monitorKey parameter root) budget required (proposalStop (fun _ _ _ _ => false))
    input (monitorView state.1) length record hactive
  rw [← hmonitor] at hstop hprefixStop
  have hunstopped : result.2.1.2.stopped = false := by
    rw [hstop]
    simp only [proposalStop, Bool.or_false, hprefixStop, decide_eq_false_iff_not]
    exact hprefix
  refine ⟨hunstopped, ?_, ?_⟩
  · rw [haccount.spent hunstopped]
    change QueryCache.enncard result.2.1.1.1 ≤ ((state.1.2.spent + result.1.1.2.hashCalls : Nat) : ENNReal)
    rw [Nat.cast_add]
    exact haccount.enncard.trans (add_le_add hcons.1 le_rfl)
  · rw [haccount.log hunstopped]
    exact haccount.digests state.1.2.log hcons.2

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

include hauxiliary in
theorem exceptionRun_unstopped (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ExceptionState) (hvalid : Valid state.1)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state.1) (hcons : Consistent parameter root state.1)
    (halive : state.1.2.stopped = false) (hbudget : budget ≤ 2 ^ 127) (result : AdversaryTrace × ExceptionState)
    (hresult : exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) computation state result ≠ 0)
    (hcost : state.1.2.spent + result.1.1.2.hashCalls ≤ budget) (hlog : state.1.2.log.length + result.1.1.1.2.length ≤ signatureLimit)
    (hclean : result.2.2 = (false, false)) : result.2.1.2.stopped = false ∧ Consistent parameter root result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [exceptionRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact ⟨halive, hcons⟩
  | query_bind input next ih =>
      have hcleanState := exceptionRun_clean parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (liftM ((OracleWorld + SigningSpec).query input) >>= next) state result hresult hclean
      rw [exceptionRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hcleanStep := exceptionRun_clean parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (next step.1.1.1) step.2 tail htail hclean
      have hmon := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) input state step hstep).1
      simp only [combineStep, SigningBoundaryTrace.hashCalls_mul, List.length_append] at hcost hlog
      have hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs :=
        fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state.1 hvalid hcovered
      have hsign := covered_step_digest parameter root otsSecret inputs input next state.1 hvalid hcovered
      obtain ⟨hstepAlive, hstepCons⟩ := exceptionStep_unstopped parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required input state hvalid hworld hsign hcons halive hbudget step hstep (by omega) (by omega) hcleanState hcleanStep
      have haccount := monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) input state.1 hvalid hworld hsign (step.1, step.2.1) hmon
      have hspent := haccount.spent hstepAlive
      have hlogStep := haccount.log hstepAlive
      change step.2.1.2.spent = state.1.2.spent + step.1.1.2.hashCalls at hspent
      change step.2.1.2.log = state.1.2.log ++ signingLogFragment input step.1.1.1 at hlogStep
      exact ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop (fun _ _ _ _ => false)) input state.1 hvalid _ hmon)
        (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop (fun _ _ _ _ => false)) hauxiliary input next state.1 hvalid hcovered _ hmon)
        hstepCons hstepAlive tail htail (by rw [hspent]; omega) (by rw [hlogStep, List.length_append]; omega) hclean

theorem exceptionWorldRun_unstopped {Result : Type} (computation : OracleComp OracleWorld Result) (state : ExceptionState)
    (hvalid : Valid state.1) (hinputs : hashInputs computation ⊆ inputs) (hcons : Consistent parameter root state.1)
    (halive : state.1.2.stopped = false) (hbudget : budget ≤ 2 ^ 127) (result : ((Result × SigningBoundaryTrace) × Trace) × ExceptionState)
    (hresult : exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) computation state result ≠ 0)
    (hcost : state.1.2.spent + result.1.1.2.hashCalls ≤ budget) (hlog : state.1.2.log.length ≤ signatureLimit)
    (hclean : result.2.2 = (false, false)) : result.2.1.2.stopped = false ∧ Consistent parameter root result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [exceptionWorldRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact ⟨halive, hcons⟩
  | query_bind input next ih =>
      have hcleanState := exceptionWorldRun_clean parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (liftM (OracleWorld.query input) >>= next) state result hresult hclean
      rw [exceptionWorldRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hcleanStep := exceptionWorldRun_clean parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (next step.1.1.1) step.2 tail htail hclean
      have hmon := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (.inl input) state step hstep).1
      simp only [SigningBoundaryTrace.hashCalls_mul] at hcost
      have hworld : ∀ world, (.inl input : (OracleWorld + SigningSpec).Domain) = .inl world →
          hashInputs (liftM (OracleWorld.query world)) ⊆ inputs :=
        fun world heq => by cases heq; exact (hashInputs_world_query input next).trans hinputs
      have hsign : ∀ message, (.inl input : (OracleWorld + SigningSpec).Domain) = .inr message →
          hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs := fun message heq => by cases heq
      obtain ⟨hstepAlive, hstepCons⟩ := exceptionStep_unstopped parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required (.inl input) state hvalid hworld hsign hcons halive hbudget step hstep (by omega)
        (by simpa only [signingLogFragment, List.length_nil, Nat.add_zero] using hlog) hcleanState hcleanStep
      have haccount := monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop (fun _ _ _ _ => false)) (.inl input) state.1 hvalid hworld hsign (step.1, step.2.1) hmon
      have hspent := haccount.spent hstepAlive
      have hlogStep := haccount.log hstepAlive
      change step.2.1.2.spent = state.1.2.spent + step.1.1.2.hashCalls at hspent
      change step.2.1.2.log = state.1.2.log ++ signingLogFragment (.inl input) step.1.1.1 at hlogStep
      exact ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop (fun _ _ _ _ => false)) (.inl input) state.1 hvalid _ hmon)
        ((hashInputs_world_next input next step.1.1.1).trans hinputs) hstepCons hstepAlive tail htail (by rw [hspent]; omega)
        (by rw [hlogStep]; simpa only [signingLogFragment, List.append_nil] using hlog) hclean

include hauxiliary in
theorem exceptionCompletedRun_unstopped (adversary : Adversary) (state : ExceptionState) (hvalid : Valid state.1)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.1) (hcons : Consistent parameter root state.1)
    (halive : state.1.2.stopped = false) (hbudget : budget ≤ 2 ^ 127) (result : Completed × ExceptionState)
    (hresult : exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop (fun _ _ _ _ => false)) adversary state result ≠ 0)
    (hcost : state.1.2.spent + completedWork result.1 ≤ budget) (hlog : state.1.2.log.length + result.1.1.1.1.2.length ≤ signatureLimit)
    (hclean : result.2.2 = (false, false)) : result.2.1.2.stopped = false := by
  rw [exceptionCompletedRun, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨before, hbefore, hresult⟩ := hresult
  obtain ⟨checked, hchecked, rfl⟩ := map_nonzero_source' _ _ _ hresult
  have hcleanBefore := exceptionWorldRun_clean parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) _ before.2 checked hchecked hclean
  simp only [completedWork] at hcost
  obtain ⟨hbeforeAlive, hbeforeCons⟩ := exceptionRun_unstopped parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
    required hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered hcons halive hbudget before hbefore (by omega) hlog hcleanBefore
  have hforced := exceptionRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) (adversary.main ⟨root, parameter⟩) state before hbefore
  have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) (adversary.main ⟨root, parameter⟩) state.1 hvalid _ hforced
  have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) hauxiliary (adversary.main ⟨root, parameter⟩) state.1 hvalid hcovered _ hforced
  have haccount := monitoredRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (proposalStop (fun _ _ _ _ => false)) hauxiliary (adversary.main ⟨root, parameter⟩) state.1 hvalid hcovered _ hforced
  have hspent := haccount.spent hbeforeAlive
  have hlogBefore := haccount.log hbeforeAlive
  change before.2.1.2.spent = state.1.2.spent + before.1.1.2.hashCalls at hspent
  change before.2.1.2.log = state.1.2.log ++ before.1.1.1.2 at hlogBefore
  exact (exceptionWorldRun_unstopped parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    (verifyComputation parameter root before.1.1.1.1) before.2 hvalid'
    (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2.1 hvalid' hfinal) hbeforeCons hbeforeAlive hbudget checked hchecked
    (by rw [hspent]; omega) (by rw [hlogBefore, List.length_append]; omega) hclean).1

end SphincsSecurity.Concrete.FtsGuessHash
