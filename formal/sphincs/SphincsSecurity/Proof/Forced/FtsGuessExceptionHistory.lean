import SphincsSecurity.Proof.Forced.FtsGuessMonitoredAccounting
import SphincsSecurity.Proof.Residual.RetainedResidualCacheKernels
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

/-! ### Exception flags -/

abbrev ExceptionState := MonitoredState × (Bool × Bool)

noncomputable def exceptionUpdate (before after : MonitoredState) (history : Bool × Bool) : Bool × Bool :=
  (history.1 || decide (CertificateCacheExceptional (monitorKey parameter root) before.1.1) ||
    decide (CertificateCacheExceptional (monitorKey parameter root) after.1.1),
   history.2 || decide (ProposalPrefixExceptional after.2.proposals after.2.log.length))

noncomputable def exceptionStep (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState) :
    SPMF (AdversaryStep input × ExceptionState) :=
  (fun result => (result.1, (result.2, exceptionUpdate parameter root state.1 result.2 state.2))) <$>
    monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.1

theorem exceptionStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState) :
    (fun result => (result.1, result.2.1)) <$>
        exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state =
      monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.1 := by
  simp only [exceptionStep, Functor.map_map]
  exact id_map _

theorem exceptionStep_support (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionState)
    (result : AdversaryStep input × ExceptionState)
    (hresult : exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      result ≠ 0) :
    monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.1
      (result.1, result.2.1) ≠ 0 ∧ result.2.2 = exceptionUpdate parameter root state.1 result.2.1 state.2 := by
  obtain ⟨raw, hraw, heq⟩ := map_nonzero_source' _ _ _ hresult
  cases heq
  exact ⟨hraw, rfl⟩

noncomputable def exceptionRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ExceptionState → SPMF ((((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × ExceptionState) :=
  OracleComp.construct (fun value state => pure ((((value, []), 1), 1), state))
    (fun input _ next state =>
      exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$> next step.1.1.1 step.2) computation

theorem exceptionRun_pure {Result : Type} (value : Result) (state : ExceptionState) :
    exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (pure value) state =
      pure ((((value, []), 1), 1), state) := rfl

theorem exceptionRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) (state : ExceptionState) :
    exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$>
          exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next step.1.1.1) step.2) := by
  rw [exceptionRun, OracleComp.construct_query_bind]
  rfl

theorem exceptionRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ExceptionState) :
    (fun result => (result.1, result.2.1)) <$>
        exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state =
      monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [exceptionRun_pure, monitoredRun_pure, map_pure]
  | query_bind input next ih =>
      rw [exceptionRun_query_bind, map_bind, monitoredRun_query_bind,
        ← exceptionStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state,
        bind_map_left]
      apply congrArg (_ >>= ·)
      funext step
      rw [Functor.map_map, ← ih step.1.1.1 step.2, Functor.map_map]

theorem exceptionRun_forced {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ExceptionState)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × ExceptionState)
    (hresult : exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state.1
      (result.1, result.2.1) ≠ 0 := by
  have h := map_nonzero_of _ (fun result => (result.1, result.2.1)) result hresult
  rwa [exceptionRun_erasure] at h

theorem exceptionRun_clean {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ExceptionState)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × ExceptionState)
    (hresult : exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) (hclean : result.2.2 = (false, false)) : state.2 = (false, false) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [exceptionRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hclean
  | query_bind input next ih =>
      rw [exceptionRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hafter : step.2.2 = (false, false) := ih step.1.1.1 step.2 tail htail hclean
      have hupdate := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state step hstep).2
      rw [hupdate] at hafter
      simp only [exceptionUpdate, Prod.mk.injEq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hafter
      exact Prod.ext hafter.1.1.1 hafter.2.1

/-! ### Exception flags along the verifier -/

noncomputable def exceptionWorldStep (input : OracleWorld.Domain) (state : ExceptionState) :
    SPMF (AdversaryStep (.inl input) × ExceptionState) :=
  exceptionStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input) state

noncomputable def exceptionWorldRun {Result : Type} (computation : OracleComp OracleWorld Result) :
    ExceptionState → SPMF (((Result × SigningBoundaryTrace) × Trace) × ExceptionState) :=
  OracleComp.construct (fun value state => pure (((value, 1), 1), state))
    (fun input _ next state =>
      exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (((tail.1.1.1, step.1.1.2 * tail.1.1.2), step.1.2 * tail.1.2), tail.2)) <$> next step.1.1.1 step.2) computation

theorem exceptionWorldRun_pure {Result : Type} (value : Result) (state : ExceptionState) :
    exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (pure value) state =
      pure (((value, 1), 1), state) := rfl

theorem exceptionWorldRun_query_bind {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (state : ExceptionState) :
    exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM (OracleWorld.query input) >>= next) state =
      (exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
        fun step => (fun tail => (((tail.1.1.1, step.1.1.2 * tail.1.1.2), step.1.2 * tail.1.2), tail.2)) <$>
          exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next step.1.1.1) step.2) := by
  rw [exceptionWorldRun, OracleComp.construct_query_bind]
  rfl

theorem exceptionWorldStep_erasure (input : OracleWorld.Domain) (state : ExceptionState) :
    (fun result => (result.1, result.2.1)) <$>
        exceptionWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state =
      monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.1 :=
  exceptionStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input) state

theorem exceptionWorldRun_erasure {Result : Type} (computation : OracleComp OracleWorld Result) (state : ExceptionState) :
    (fun result => (result.1, result.2.1)) <$>
        exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state =
      monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [exceptionWorldRun_pure, monitoredWorldRun_pure, map_pure]
  | query_bind input next ih =>
      rw [exceptionWorldRun_query_bind, map_bind, monitoredWorldRun_query_bind,
        ← exceptionWorldStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
          state, bind_map_left]
      apply congrArg (_ >>= ·)
      funext step
      rw [Functor.map_map, ← ih step.1.1.1 step.2, Functor.map_map]

theorem exceptionWorldRun_clean {Result : Type} (computation : OracleComp OracleWorld Result) (state : ExceptionState)
    (result : ((Result × SigningBoundaryTrace) × Trace) × ExceptionState)
    (hresult : exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) (hclean : result.2.2 = (false, false)) : state.2 = (false, false) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [exceptionWorldRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hclean
  | query_bind input next ih =>
      rw [exceptionWorldRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hafter : step.2.2 = (false, false) := ih step.1.1.1 step.2 tail htail hclean
      have hupdate := (exceptionStep_support parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (.inl input) state step hstep).2
      rw [hupdate] at hafter
      simp only [exceptionUpdate, Prod.mk.injEq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hafter
      exact Prod.ext hafter.1.1.1 hafter.2.1

noncomputable def exceptionCompletedRun (adversary : Adversary) (state : ExceptionState) : SPMF (Completed × ExceptionState) :=
  exceptionRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (adversary.main ⟨root, parameter⟩) state >>= fun before =>
    (fun checked => ((before.1, checked.1), checked.2)) <$>
      exceptionWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (verifyComputation parameter root before.1.1.1.1) before.2

theorem exceptionCompletedRun_erasure (adversary : Adversary) (state : ExceptionState) :
    (fun result => (result.1, result.2.1)) <$>
        exceptionCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary state =
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary
        state.1 := by
  rw [exceptionCompletedRun, monitoredCompletedRun_eq, map_bind, ← exceptionRun_erasure, bind_map_left]
  apply congrArg (_ >>= ·)
  funext before
  rw [Functor.map_map, ← exceptionWorldRun_erasure, Functor.map_map]

/-! ### Finite caches -/

def Sized (state : MonitoredState) : Prop := ∃ bound : Nat, QueryCache.enncard state.1.1 ≤ bound

theorem Sized.finite {state : MonitoredState} (hsized : Sized state) : Finite state.1.1 := by
  obtain ⟨bound, hbound⟩ := hsized
  exact Finite.of_enncard_le hbound

theorem monitoredStep_sized (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hsized : Sized state) (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) : Sized result.2 := by
  obtain ⟨bound, hbound⟩ := hsized
  refine ⟨bound + result.1.1.2.hashCalls, ?_⟩
  rw [Nat.cast_add]
  exact (monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
    hvalid hworld hsign result hresult).enncard.trans (add_le_add hbound le_rfl)

/-! ### The cache-exception weight along one step -/

theorem tsum_probOutput_evalDist {Result : Type} (computation : ProbComp Result) (weight : Result → ENNReal) :
    (∑' result, Pr[= result | 𝒟[computation]] * weight result) = ∑' result, Pr[= result | computation] * weight result := rfl

theorem expected_forcedSigning_cacheWeight_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (hfinite : Finite state.1.1) :
    (∑' result, Pr[= result | forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state] *
      certificateCacheExceptionWeight (monitorKey parameter root) result.2.1) ≤
      certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
        digestAttemptExpectation digestAttemptLimit (monitorKey parameter root) message state.1.1 * certificateCacheExceptionRate := by
  rw [forcedSigning, cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1
    hvalid hinputs (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy),
    tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  have hwork := RetainedResidual.expected_publicSigningWork_cacheWeight_le (monitorKey parameter root) (referenceFamilyWords selections dummy)
    selections (known otsSecret labels) message state.1.1 hfinite
  have hlaw : (∑' result, Pr[= result | 𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root
        (known otsSecret labels) (referenceFamilyWords selections dummy) selections message)).run state.1.1]] *
      certificateCacheExceptionWeight (monitorKey parameter root) result.2) ≤
      certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
        digestAttemptExpectation digestAttemptLimit (monitorKey parameter root) message state.1.1 * certificateCacheExceptionRate := by
    have hparameter : (monitorKey parameter root).parameter = parameter := rfl
    have hroot : (monitorKey parameter root).root = root := rfl
    rw [hparameter, hroot] at hwork
    rw [simulateQ_map, StateT.run_map, evalDist_map, tsum_probOutput_map_mul, tsum_probOutput_evalDist]
    exact hwork
  calc
    _ ≤ ∑' secrets, Pr[= secrets | complete state.1.2.allowed] *
        (certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
          digestAttemptExpectation digestAttemptLimit (monitorKey parameter root) message state.1.1 * certificateCacheExceptionRate) :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl hlaw
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_worldStep_cacheWeight_le (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (hfinite : Finite state.1.1) :
    (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels input) state.1] * certificateCacheExceptionWeight (monitorKey parameter root) result.2.1) ≤
      certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
        nativeMessageCharge (monitorKey parameter root) (.inl input) (monitorView state) * certificateCacheExceptionRate := by
  have hpointwise (hmono : ∀ result, cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels input) state.1 result ≠ 0 →
      certificateCacheExceptionWeight (monitorKey parameter root) result.2.1 ≤ certificateCacheExceptionWeight (monitorKey parameter root) state.1.1) :
      (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels input) state.1] * certificateCacheExceptionWeight (monitorKey parameter root) result.2.1) ≤
        certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 := by
    calc
      _ ≤ ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
          (worldProgram parameter labels input) state.1] * certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (worldProgram parameter labels input) state.1] = 0
        · simp only [hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          exact mul_le_mul' le_rfl (hmono result hr)
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
  cases input with
  | inl sample =>
      refine (hpointwise fun result hr => ?_).trans le_self_add
      rw [cachedForcedRun_world_unif'] at hr
      obtain ⟨answer, _, rfl⟩ := map_nonzero_source' _ _ _ hr
      exact le_rfl
  | inr hash =>
      have hin : hash ∈ inputs := hinputs (by simpa only [bind_pure] using mem_hashInputs_hash_bind hash pure)
      by_cases hmessage : MessageHashInput parameter hash
      · rw [cachedForcedRun_world_message' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash hin hmessage state.1,
          tsum_probOutput_map_mul]
        have h := expected_certificateCacheExceptionWeight_rom (monitorKey parameter root) (.inr hash) state.1.1 hfinite
        rw [tsum_probOutput_evalDist]
        exact h
      · refine (hpointwise fun result hr => ?_).trans le_self_add
        have hsupport := cachedForcedRun_world_hash_support' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash
          state.1 result hr
        have hafter : Finite result.2.1 := by
          have hbound : QueryCache.enncard state.1.1 ≤ (({input | state.1.1 input ≠ none}.ncard : Nat) : ENNReal) :=
            hfinite.cachedInputs_ncard_toENNReal_eq_enncard.symm.le
          exact Finite.of_enncard_le (q := {input | state.1.1 input ≠ none}.ncard + 1)
            (hsupport.2.2.trans (by rw [Nat.cast_add, Nat.cast_one]; exact add_le_add hbound le_rfl))
        exact certificateCacheExceptionWeight_messageAnswers_le (monitorKey parameter root) state.1.1 result.2.1 hafter
          (messageAnswers_eq_of_cache_of_ne parameter state.1.1 result.2.1 hash hmessage hsupport.1).symm
          (QueryCache.enncard_mono hsupport.2.1)

theorem expected_monitoredStep_cacheWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hfinite : Finite state.1.1) :
    (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * certificateCacheExceptionWeight (monitorKey parameter root) result.2.1.1) ≤
      certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
        nativeMessageCharge (monitorKey parameter root) input (monitorView state) * certificateCacheExceptionRate := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep, tsum_probOutput_map_mul]
      exact expected_worldStep_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot input state
        (hworld input rfl) hfinite
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_map_mul]
      calc
        _ ≤ ∑' annotation, Pr[= annotation | (liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _)] *
            (certificateCacheExceptionWeight (monitorKey parameter root) state.1.1 +
              digestAttemptExpectation digestAttemptLimit (monitorKey parameter root) message state.1.1 * certificateCacheExceptionRate) := by
          apply ENNReal.tsum_le_tsum
          intro annotation
          apply mul_le_mul' le_rfl
          exact expected_forcedSigning_cacheWeight_le parameter root otsSecret labels inputs hencoding selections rows dummy slot message state
            hvalid (hsign message rfl) hfinite
        _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.FtsGuessHash
