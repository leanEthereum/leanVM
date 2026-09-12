import SphincsSecurity.Proof.Forced.FtsGuessExceptionBounds
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers messageHashCharge)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult nativeMessageCharge signingAnnotation)
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

/-! ### The cache-exception weight along runs -/

noncomputable def cacheHistoryWeight (state : ExceptionState) : ENNReal :=
  if state.2.1 then 1 else certificateCacheExceptionWeight (monitorKey parameter root) state.1.1.1

theorem expected_exceptionStep_cacheWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState) (hvalid : Valid state.1)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hsized : Sized state.1) :
    (∑' result, Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * cacheHistoryWeight parameter root result.2) ≤
      cacheHistoryWeight parameter root state +
        nativeMessageCharge (monitorKey parameter root) input (monitorView state.1) * certificateCacheExceptionRate := by
  rw [exceptionStep, tsum_probOutput_map_mul]
  cases hflag : state.2.1 with
  | true =>
      simp only [cacheHistoryWeight, exceptionUpdate, hflag, Bool.true_or, ite_true, mul_one]
      exact tsum_probOutput_le_one.trans le_self_add
  | false =>
      conv_rhs => simp only [cacheHistoryWeight, hflag, Bool.false_eq_true, if_false]
      by_cases hbefore : CertificateCacheExceptional (monitorKey parameter root) state.1.1.1
      · simp only [cacheHistoryWeight, exceptionUpdate, hflag, Bool.false_or, decide_eq_true hbefore, Bool.true_or, ite_true, mul_one]
        exact tsum_probOutput_le_one.trans ((certificateCacheExceptionWeight_bad (monitorKey parameter root) _ hsized.finite hbefore).trans
          le_self_add)
      · apply le_trans ?_ (expected_monitoredStep_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter input state.1 hvalid hworld hsign hsized.finite)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter input state.1] = 0
        · simp only [hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          apply mul_le_mul' le_rfl
          have hafter := monitoredStep_sized parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            input state.1 hvalid hworld hsign hsized result hr
          simp only [cacheHistoryWeight, exceptionUpdate, hflag, Bool.false_or, decide_eq_false hbefore, Bool.false_or, decide_eq_true_eq]
          split
          · exact certificateCacheExceptionWeight_bad (monitorKey parameter root) _ hafter.finite (by assumption)
          · exact le_rfl

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

include hauxiliary in
theorem expected_exceptionRun_cacheWeight_le (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ExceptionState)
    (hvalid : Valid state.1) (hcovered : CoveredRun parameter root otsSecret inputs computation state.1) (hsized : Sized state.1) :
    (∑' result, Pr[= result | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] * cacheHistoryWeight parameter root result.2) ≤
      cacheHistoryWeight parameter root state +
        expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate) computation
          state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [exceptionRun_query_bind, tsum_probOutput_bind_mul, expectedMonitoredPayment_query_bind]
      have hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs :=
        fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state.1 hvalid hcovered
      have hsign := covered_step_digest parameter root otsSecret inputs input next state.1 hvalid hcovered
      let payment (result : AdversaryStep input × MonitoredState) : ENNReal :=
        expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate)
          (next result.1.1.1) result.2
      have herasure : (∑' result, Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter input state] * payment (result.1, result.2.1)) =
          ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter input state.1] * payment result := by
        have h := congrArg (fun law : SPMF (AdversaryStep input × MonitoredState) => ∑' result, Pr[= result | law] * payment result)
          (exceptionStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state)
        rw [tsum_probOutput_map_mul] at h
        exact h
      calc
        _ ≤ ∑' result, Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] * (cacheHistoryWeight parameter root result.2 + payment (result.1, result.2.1)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hn := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
              input state result hr).1
            apply mul_le_mul' le_rfl
            rw [tsum_probOutput_map_mul]
            exact ih result.1.1.1 result.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
                state.1 hvalid _ hn)
              (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
                input next state.1 hvalid hcovered _ hn)
              (monitoredStep_sized parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
                state.1 hvalid hworld hsign hsized _ hn)
        _ ≤ (cacheHistoryWeight parameter root state +
              nativeMessageCharge (monitorKey parameter root) input (monitorView state.1) * certificateCacheExceptionRate) +
            ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state.1] * payment result := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [herasure]
          exact add_le_add (expected_exceptionStep_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
            budget required stopAfter input state hvalid hworld hsign hsized) le_rfl
        _ = _ := add_assoc _ _ _

theorem expected_exceptionWorldRun_cacheWeight_le {Result : Type} (computation : OracleComp OracleWorld Result) (state : ExceptionState)
    (hvalid : Valid state.1) (hinputs : hashInputs computation ⊆ inputs) (hsized : Sized state.1) :
    (∑' result, Pr[= result | exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * cacheHistoryWeight parameter root result.2) ≤
      cacheHistoryWeight parameter root state +
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate) computation
          state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionWorldRun_pure, tsum_probOutput_pure_mul, expectedWorldPayment, construct_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [exceptionWorldRun_query_bind, tsum_probOutput_bind_mul, expectedWorldPayment_query_bind]
      have hworld : ∀ world, (.inl input : (OracleWorld + SigningSpec).Domain) = .inl world →
          hashInputs (liftM (OracleWorld.query world)) ⊆ inputs :=
        fun world heq => by cases heq; exact (hashInputs_world_query input next).trans hinputs
      have hsign : ∀ message, (.inl input : (OracleWorld + SigningSpec).Domain) = .inr message →
          hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs := fun message heq => by cases heq
      let payment (result : AdversaryStep (.inl input) × MonitoredState) : ENNReal :=
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate)
          (next result.1.1.1) result.2
      have herasure : (∑' result, Pr[= result | exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter input state] * payment (result.1, result.2.1)) =
          ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter input state.1] * payment result := by
        have h := congrArg (fun law : SPMF (AdversaryStep (.inl input) × MonitoredState) => ∑' result, Pr[= result | law] * payment result)
          (exceptionWorldStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
            state)
        rw [tsum_probOutput_map_mul] at h
        exact h
      calc
        _ ≤ ∑' result, Pr[= result | exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] * (cacheHistoryWeight parameter root result.2 + payment (result.1, result.2.1)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hn := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
              (.inl input) state result hr).1
            apply mul_le_mul' le_rfl
            rw [tsum_probOutput_map_mul]
            exact ih result.1.1.1 result.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input)
                state.1 hvalid _ hn)
              ((hashInputs_world_next input next result.1.1.1).trans hinputs)
              (monitoredStep_sized parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input)
                state.1 hvalid hworld hsign hsized _ hn)
        _ ≤ (cacheHistoryWeight parameter root state +
              nativeMessageCharge (monitorKey parameter root) (.inl input) (monitorView state.1) * certificateCacheExceptionRate) +
            ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state.1] * payment result := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [herasure]
          exact add_le_add (expected_exceptionStep_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
            budget required stopAfter (.inl input) state hvalid hworld hsign hsized) le_rfl
        _ = _ := add_assoc _ _ _

include hauxiliary in
theorem exceptionRun_sized (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ExceptionState) (hvalid : Valid state.1)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state.1) (hsized : Sized state.1)
    (result : AdversaryTrace × ExceptionState)
    (hresult : exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) : Sized result.2.1 := by
  obtain ⟨bound, hbound⟩ := hsized
  refine ⟨bound + result.1.1.2.hashCalls, ?_⟩
  rw [Nat.cast_add]
  have haccount := monitoredRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    hauxiliary computation state.1 hvalid hcovered (result.1, result.2.1)
    (exceptionRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state
      result hresult)
  exact haccount.enncard.trans (add_le_add hbound le_rfl)

include hauxiliary in
theorem expected_exceptionCompletedRun_cacheWeight_le (adversary : Adversary) (state : ExceptionState) (hvalid : Valid state.1)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.1) (hsized : Sized state.1) :
    (∑' result, Pr[= result | exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] * cacheHistoryWeight parameter root result.2) ≤
      cacheHistoryWeight parameter root state +
        (expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (nativeMessageCharge (monitorKey parameter root)) (adversary.main ⟨root, parameter⟩) state.1 +
        ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state.1] *
          expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (nativeMessageCharge (monitorKey parameter root)) (verifyComputation parameter root before.1.1.1.1) before.2) *
        certificateCacheExceptionRate := by
  rw [exceptionCompletedRun, tsum_probOutput_bind_mul]
  let worldPayment (before : AdversaryTrace × MonitoredState) : ENNReal :=
    expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate)
      (verifyComputation parameter root before.1.1.1.1) before.2
  have herasure : (∑' before, Pr[= before | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      stopAfter (adversary.main ⟨root, parameter⟩) state] * worldPayment (before.1, before.2.1)) =
      ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state.1] * worldPayment before := by
    have h := congrArg (fun law : SPMF (AdversaryTrace × MonitoredState) => ∑' before, Pr[= before | law] * worldPayment before)
      (exceptionRun_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state)
    rw [tsum_probOutput_map_mul] at h
    exact h
  calc
    _ ≤ ∑' before, Pr[= before | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state] * (cacheHistoryWeight parameter root before.2 + worldPayment (before.1, before.2.1)) := by
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hb : Pr[= before | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hb
        have hforced := exceptionRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state before hb
        have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state.1 hvalid _ hforced
        have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          hauxiliary (adversary.main ⟨root, parameter⟩) state.1 hvalid hcovered _ hforced
        apply mul_le_mul' le_rfl
        rw [tsum_probOutput_map_mul]
        exact expected_exceptionWorldRun_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (verifyComputation parameter root before.1.1.1.1) before.2 hvalid'
          (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2.1 hvalid' hfinal)
          (exceptionRun_sized parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
            (adversary.main ⟨root, parameter⟩) state hvalid hcovered hsized before hb)
    _ ≤ (cacheHistoryWeight parameter root state +
          expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (fun input current => nativeMessageCharge (monitorKey parameter root) input current * certificateCacheExceptionRate)
            (adversary.main ⟨root, parameter⟩) state.1) +
        ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state.1] * worldPayment before := by
      simp only [mul_add, ENNReal.tsum_add]
      rw [herasure]
      exact add_le_add (expected_exceptionRun_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered hsized) le_rfl
    _ = _ := by
      rw [add_assoc, add_mul, expectedMonitoredPayment_mul, ← ENNReal.tsum_mul_right]
      congr 2
      apply tsum_congr
      intro before
      rw [mul_assoc]
      apply congrArg (_ * ·)
      exact expectedWorldPayment_mul parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter _ _ _ _

include hauxiliary in
theorem exceptionCompletedRun_cache_le (adversary : Adversary) (state : ExceptionState) (hvalid : Valid state.1)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.1) (hsized : Sized state.1) :
    Pr[fun result => result.2.2.1 = true | exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        budget required stopAfter adversary state] ≤
      cacheHistoryWeight parameter root state +
        (∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter adversary state.1] * (completedWork result.1 : ENNReal)) * certificateCacheExceptionRate := by
  refine le_trans ?_ ((expected_exceptionCompletedRun_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
    budget required stopAfter hauxiliary adversary state hvalid hcovered hsized).trans (add_le_add le_rfl (mul_le_mul'
      (expectedCompletedPayment_le_work parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        hauxiliary adversary state.1 hvalid hcovered) le_rfl)))
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hflag
  simp only [cacheHistoryWeight, hflag, ite_true, le_refl]

/-! ### The proposal-prefix weight along runs -/

noncomputable def prefixHistoryWeight (state : ExceptionState) : ENNReal :=
  if state.2.2 then 1 else proposalPrefixWeight state.1.2.proposals state.1.2.log.length

private theorem update_log_cap (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) (hcap : state.2.log.length ≤ signatureLimit) :
    (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).log.length ≤ signatureLimit := by
  by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget input state
  · rw [certificateMonitorUpdate, if_pos hactive]
    have hvalid := hactive.2.2.1
    cases input <;>
      simp only [proposalRecordLogState, signingLogFragment, List.append_nil, List.length_append, List.length_singleton,
        ValidSigningStep] at hvalid ⊢ <;> omega
  · simpa only [certificateMonitorUpdate, if_neg hactive] using hcap

theorem monitoredStep_log_cap (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hcap : state.2.log.length ≤ signatureLimit)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      result ≠ 0) : result.2.2.log.length ≤ signatureLimit := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact update_log_cap parameter root budget required stopAfter (.inl input) (monitorView state) 0 _ hcap
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact update_log_cap parameter root budget required stopAfter (.inr message) (monitorView state) annotation.1 _ hcap

private theorem world_weight (input : OracleWorld.Domain) (state : MonitoredState) (raw : OracleWorld.Range input × CachedState) :
    proposalPrefixWeight
        (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0
          (proposalOfWorldResult parameter input (raw.1, raw.2.1))).proposals
        (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0
          (proposalOfWorldResult parameter input (raw.1, raw.2.1))).log.length =
      proposalPrefixWeight state.2.proposals state.2.log.length := by
  simp only [certificateMonitorUpdate]
  split <;> simp only [proposalRecordLogState, signingLogFragment, List.append_nil, Nat.add_zero, monitorView]

private theorem signing_weight (message : Message) (annotation : Nat × Index) (state : MonitoredState)
    (raw : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) :
    proposalPrefixWeight (signResult parameter root budget required stopAfter message annotation state raw).2.2.proposals
        (signResult parameter root budget required stopAfter message annotation state raw).2.2.log.length =
      if CertificateMonitorActive (monitorKey parameter root) budget (.inr message) (monitorView state) then
        proposalPrefixWeight (state.2.proposals + annotation.1) (state.2.log.length + 1)
      else proposalPrefixWeight state.2.proposals state.2.log.length := by
  simp only [signResult, certificateMonitorUpdate]
  split <;> simp only [proposalRecordLogState, signingLogFragment, List.length_append, List.length_singleton, monitorView]

theorem expected_monitoredStep_prefixWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) :
    (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * proposalPrefixWeight result.2.2.proposals result.2.2.log.length) ≤
      proposalPrefixWeight state.2.proposals state.2.log.length := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep, tsum_probOutput_map_mul]
      simp only [world_weight, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_map_mul, signing_weight, ENNReal.tsum_mul_right]
      by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget (.inr message) (monitorView state)
      · simp only [if_pos hactive]
        calc
          _ ≤ ∑' annotation, Pr[= annotation | (liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _)] *
              proposalPrefixWeight (state.2.proposals + annotation.1) (state.2.log.length + 1) :=
            ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)
          _ = proposalPrefixWeight state.2.proposals state.2.log.length := by
            simp only [SPMF.probOutput_liftM]
            rw [signingAnnotation, if_pos hactive, ← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
            simp_rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
            simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
            exact expected_proposalPrefixWeight state.2.proposals state.2.log.length hactive.2.2.1
      · simp only [if_neg hactive, ENNReal.tsum_mul_right]
        exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans (mul_le_of_le_one_left' tsum_probOutput_le_one)

theorem expected_exceptionStep_prefixWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState)
    (hcap : state.1.2.log.length ≤ signatureLimit) :
    (∑' result, Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
  rw [exceptionStep, tsum_probOutput_map_mul]
  cases hflag : state.2.2 with
  | true =>
      simp only [prefixHistoryWeight, exceptionUpdate, hflag, Bool.true_or, ite_true, mul_one]
      exact tsum_probOutput_le_one
  | false =>
      conv_rhs => simp only [prefixHistoryWeight, hflag, Bool.false_eq_true, if_false]
      apply le_trans ?_ (expected_monitoredStep_prefixWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter input state.1)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state.1] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        apply mul_le_mul' le_rfl
        have hcap' := monitoredStep_log_cap parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state.1 hcap result hr
        simp only [prefixHistoryWeight, exceptionUpdate, hflag, Bool.false_or, decide_eq_true_eq]
        split
        · exact proposalPrefixWeight_bad _ _ hcap' (by assumption)
        · exact le_rfl

theorem expected_exceptionRun_prefixWeight_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionState) (hcap : state.1.2.log.length ≤ signatureLimit) :
    (∑' result, Pr[= result | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] * prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionRun_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [exceptionRun_query_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ (expected_exceptionStep_prefixWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter input state hcap)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        have hn := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state result hr).1
        have hc := monitoredStep_log_cap parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state.1 hcap _ hn
        apply mul_le_mul' le_rfl
        rw [tsum_probOutput_map_mul]
        exact ih result.1.1.1 result.2 hc

theorem expected_exceptionWorldRun_prefixWeight_le {Result : Type} (computation : OracleComp OracleWorld Result) (state : ExceptionState)
    (hcap : state.1.2.log.length ≤ signatureLimit) :
    (∑' result, Pr[= result | exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionWorldRun_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [exceptionWorldRun_query_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ (expected_exceptionStep_prefixWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter (.inl input) state hcap)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] = 0
      · simp only [hr, zero_mul]
        exact zero_le
      · rw [SPMF.probOutput_eq_apply] at hr
        have hn := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (.inl input) state result hr).1
        have hc := monitoredStep_log_cap parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (.inl input) state.1 hcap _ hn
        apply mul_le_mul' le_rfl
        rw [tsum_probOutput_map_mul]
        exact ih result.1.1.1 result.2 hc

theorem exceptionRun_log_cap (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ExceptionState)
    (hcap : state.1.2.log.length ≤ signatureLimit) (result : AdversaryTrace × ExceptionState)
    (hresult : exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) : result.2.1.2.log.length ≤ signatureLimit := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [exceptionRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hcap
  | query_bind input next ih =>
      rw [exceptionRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hn := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
        state step hstep).1
      exact ih step.1.1.1 step.2
        (monitoredStep_log_cap parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.1
          hcap _ hn) tail htail

theorem exceptionCompletedRun_prefix_le (adversary : Adversary) (state : ExceptionState) (hcap : state.1.2.log.length ≤ signatureLimit) :
    Pr[fun result => result.2.2.2 = true | exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter adversary state] ≤ prefixHistoryWeight state := by
  have hweight : (∑' result, Pr[= result | exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
      required stopAfter adversary state] * prefixHistoryWeight result.2) ≤ prefixHistoryWeight state := by
    rw [exceptionCompletedRun, tsum_probOutput_bind_mul]
    apply le_trans ?_ (expected_exceptionRun_prefixWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
      required stopAfter (adversary.main ⟨root, parameter⟩) state hcap)
    apply ENNReal.tsum_le_tsum
    intro before
    by_cases hb : Pr[= before | exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state] = 0
    · simp only [hb, zero_mul, le_refl]
    · rw [SPMF.probOutput_eq_apply] at hb
      apply mul_le_mul' le_rfl
      rw [tsum_probOutput_map_mul]
      exact expected_exceptionWorldRun_prefixWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter _ before.2
        (exceptionRun_log_cap parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state hcap before hb)
  refine le_trans ?_ hweight
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hflag
  simp only [prefixHistoryWeight, hflag, ite_true, le_refl]

end SphincsSecurity.Concrete.FtsGuessHash
