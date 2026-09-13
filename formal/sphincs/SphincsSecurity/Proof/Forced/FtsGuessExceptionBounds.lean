import SphincsSecurity.Proof.Forced.FtsGuessExceptionHistory
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

/-! ### Runs are probability laws -/

theorem monitoredRun_bind_const {Result Other : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState)
    (hvalid : Valid state) (after : SPMF Other) :
    (monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state >>=
      fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [monitoredRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, bind_assoc]
      rw [RetainedObservation.bind_congr _ _ (fun _ => after) (fun step hstep => by
        rw [bind_map_left]
        exact ih step.1.1.1 step.2 (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter input state hvalid step hstep))]
      exact monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state hvalid after

theorem tsum_monitoredRun_eq_one {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState)
    (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (monitoredRun_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation
      state hvalid (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

theorem tsum_monitoredWorldRun_eq_one {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState)
    (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      stopAfter computation state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (monitoredWorldRun_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state hvalid (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

/-! ### Message charges are paid by hash calls -/

theorem nativeMessageCharge_le_worldStep (input : OracleWorld.Domain) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) :
    nativeMessageCharge (monitorKey parameter root) (.inl input) (monitorView state) ≤
      ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels input) state.1] * ((signingBoundaryTrace parameter input result.1).hashCalls : ENNReal) := by
  cases input with
  | inl sample =>
      simp only [nativeMessageCharge, hashQueryCharge, Sum.elim_inl]
      exact zero_le
  | inr hash =>
      have hone : ∀ result : OracleWorld.Range (.inr hash) × CachedState,
          ((signingBoundaryTrace parameter (.inr hash) result.1).hashCalls : ENNReal) = 1 := by
        intro result
        simp only [signingBoundaryTrace, SigningBoundaryTrace.hashCalls_of, Nat.cast_one]
      simp only [hone, mul_one]
      rw [tsum_cachedForcedRun_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels (.inr hash)) state.1 hvalid]
      simp only [nativeMessageCharge, hashQueryCharge, Sum.elim_inr, messageHashCharge, monitorView]
      split_ifs <;> norm_num

theorem nativeMessageCharge_le_forcedSigning (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    nativeMessageCharge (monitorKey parameter root) (.inr message) (monitorView state) ≤
      ∑' result, Pr[= result | forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state] *
        (result.1.2.hashCalls : ENNReal) := by
  have hwork := RetainedResidual.expected_publicSigningWork_messageCalls (monitorKey parameter root) (known otsSecret labels)
    (referenceFamilyWords selections dummy) selections message state.1.1
  have hparameter : (monitorKey parameter root).parameter = parameter := rfl
  have hroot : (monitorKey parameter root).root = root := rfl
  rw [hparameter, hroot] at hwork
  rw [forcedSigning, cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1
    hvalid hinputs (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy),
    tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, completePublicSigningRecord_trace]
  rw [simulateQ_map, StateT.run_map, evalDist_map, tsum_probOutput_map_mul, tsum_probOutput_evalDist, ENNReal.tsum_mul_right]
  have hmass : (∑' secrets, Pr[= secrets | complete state.1.2.allowed]) = 1 := by
    rw [complete_of_nonempty _ hvalid]
    simp only [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.tsum_coe]
  rw [hmass, one_mul]
  change digestAttemptExpectation digestAttemptLimit (monitorKey parameter root) message state.1.1 ≤ _
  rw [← hwork]
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact Nat.cast_le.mpr (List.length_filterMap_le _ _)

theorem nativeMessageCharge_le_monitoredStep (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    nativeMessageCharge (monitorKey parameter root) input (monitorView state) ≤
      ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * (result.1.1.2.hashCalls : ENNReal) := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep, tsum_probOutput_map_mul]
      exact nativeMessageCharge_le_worldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot input state hvalid
        (hworld input rfl)
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_map_mul]
      have hstep := nativeMessageCharge_le_forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state
        hvalid (hsign message rfl)
      calc
        _ = ∑' annotation, Pr[= annotation | (liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _)] *
            nativeMessageCharge (monitorKey parameter root) (.inr message) (monitorView state) := by
          rw [ENNReal.tsum_mul_right]
          simp only [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.tsum_coe, one_mul]
        _ ≤ _ := ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl hstep

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

include hauxiliary in
theorem expectedMonitoredPayment_le_hashCalls (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState)
    (hvalid : Valid state) (hcovered : CoveredRun parameter root otsSecret inputs computation state) :
    expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (nativeMessageCharge (monitorKey parameter root)) computation state ≤
      ∑' result, Pr[= result | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] * (result.1.1.2.hashCalls : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedMonitoredPayment, construct_pure, zero_le]
  | query_bind input next ih =>
      rw [expectedMonitoredPayment_query_bind, monitoredRun_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ (∑' step, Pr[= step | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] * (step.1.1.2.hashCalls : ENNReal)) +
            ∑' step, Pr[= step | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
              ∑' tail, Pr[= tail | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
                stopAfter (next step.1.1.1) step.2] * (tail.1.1.2.hashCalls : ENNReal) := by
          apply add_le_add (nativeMessageCharge_le_monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
            required stopAfter input state hvalid
            (fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state hvalid hcovered)
            (covered_step_digest parameter root otsSecret inputs input next state hvalid hcovered))
          apply ENNReal.tsum_le_tsum
          intro step
          by_cases hs : Pr[= step | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hs, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hs
            exact mul_le_mul' le_rfl (ih step.1.1.1 step.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
                state hvalid step hs)
              (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
                input next state hvalid hcovered step hs))
        _ = _ := by
          rw [← ENNReal.tsum_add]
          apply tsum_congr
          intro step
          by_cases hs : Pr[= step | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hs, zero_mul, add_zero]
          · rw [SPMF.probOutput_eq_apply] at hs
            have hvalid' := monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state hvalid step hs
            rw [tsum_probOutput_map_mul, ← mul_add]
            apply congrArg (_ * ·)
            simp only [combineStep, SigningBoundaryTrace.hashCalls_mul, Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
              tsum_monitoredRun_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next step.1.1.1) step.2 hvalid', one_mul]

theorem expectedWorldPayment_le_hashCalls {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState)
    (hvalid : Valid state) (hinputs : hashInputs computation ⊆ inputs) :
    expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (nativeMessageCharge (monitorKey parameter root)) computation state ≤
      ∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * (result.1.1.2.hashCalls : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedWorldPayment, construct_pure, zero_le]
  | query_bind input next ih =>
      rw [expectedWorldPayment_query_bind, monitoredWorldRun_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ (∑' step, Pr[= step | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] * (step.1.1.2.hashCalls : ENNReal)) +
            ∑' step, Pr[= step | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
              ∑' tail, Pr[= tail | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
                stopAfter (next step.1.1.1) step.2] * (tail.1.1.2.hashCalls : ENNReal) := by
          refine add_le_add ?_ ?_
          · rw [← monitoredStep_inl]
            exact nativeMessageCharge_le_monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter (.inl input) state hvalid (fun world heq => by cases heq; exact (hashInputs_world_query input next).trans hinputs)
              (fun message heq => by cases heq)
          · apply ENNReal.tsum_le_tsum
            intro step
            by_cases hs : Pr[= step | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
                required stopAfter input state] = 0
            · simp only [hs, zero_mul, le_refl]
            · rw [SPMF.probOutput_eq_apply] at hs
              exact mul_le_mul' le_rfl (ih step.1.1.1 step.2
                (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                  (.inl input) state hvalid step hs) ((hashInputs_world_next input next step.1.1.1).trans hinputs))
        _ = _ := by
          rw [← ENNReal.tsum_add]
          apply tsum_congr
          intro step
          by_cases hs : Pr[= step | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] = 0
          · simp only [hs, zero_mul, add_zero]
          · rw [SPMF.probOutput_eq_apply] at hs
            have hvalid' := monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter (.inl input) state hvalid step hs
            rw [tsum_probOutput_map_mul, ← mul_add]
            apply congrArg (_ * ·)
            simp only [SigningBoundaryTrace.hashCalls_mul, Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
              tsum_monitoredWorldRun_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next step.1.1.1) step.2 hvalid', one_mul]

theorem expectedMonitoredPayment_mul (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal) (rate : ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) :
    expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (fun input current => charge input current * rate) computation state =
      expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
        computation state * rate := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact (zero_mul _).symm
  | query_bind input next ih =>
      rw [expectedMonitoredPayment_query_bind, expectedMonitoredPayment_query_bind, add_mul, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro result
      rw [ih result.1.1.1 result.2, mul_assoc]

include hauxiliary in
theorem expectedCompletedPayment_le_work (adversary : Adversary) (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state) :
    expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (nativeMessageCharge (monitorKey parameter root)) (adversary.main ⟨root, parameter⟩) state +
      ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state] *
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (nativeMessageCharge (monitorKey parameter root)) (verifyComputation parameter root before.1.1.1.1) before.2 ≤
      ∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] * (completedWork result.1 : ENNReal) := by
  rw [monitoredCompletedRun_eq, tsum_probOutput_bind_mul]
  calc
    _ ≤ (∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] * (before.1.1.2.hashCalls : ENNReal)) +
        ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] *
          ∑' checked, Pr[= checked | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter (verifyComputation parameter root before.1.1.1.1) before.2] * (checked.1.1.2.hashCalls : ENNReal) := by
      apply add_le_add (expectedMonitoredPayment_le_hashCalls parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered)
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hb : Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hb
        have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state hvalid before hb
        have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered before hb
        exact mul_le_mul' le_rfl (expectedWorldPayment_le_hashCalls parameter root otsSecret labels inputs hencoding selections rows dummy slot
          budget required stopAfter (verifyComputation parameter root before.1.1.1.1) before.2 hvalid'
          (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2 hvalid' hfinal))
    _ = _ := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro before
      by_cases hb : Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul, add_zero]
      · rw [SPMF.probOutput_eq_apply] at hb
        have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state hvalid before hb
        rw [tsum_probOutput_map_mul, ← mul_add]
        apply congrArg (_ * ·)
        simp only [completedWork, Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_monitoredWorldRun_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (verifyComputation parameter root before.1.1.1.1) before.2 hvalid', one_mul]

end SphincsSecurity.Concrete.FtsGuessHash
