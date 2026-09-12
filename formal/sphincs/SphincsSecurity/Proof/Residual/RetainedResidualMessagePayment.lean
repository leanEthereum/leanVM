import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMessagePayment
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredPayment
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
open FtsProbeSimulation (MessageHashInput messageHashCharge)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop publicSignPlan
set_option backward.isDefEq.respectTransparency false

private theorem expected_evalDist {Result : Type} (computation : ProbComp Result) (weight : Result → ENNReal) :
    (∑' result, Pr[= result | 𝒟[computation]] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl

theorem digestWork_messageCalls (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (selected : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) :
    (digestWork known words selections selected).1.2.messageCalls = selected.2.messageCalls := by
  rcases selected with ⟨selected, trace⟩
  cases selected <;> simp only [digestWork, SigningBoundaryTrace.messageCalls_mul,
    SigningBoundaryTrace.messageCalls_pow_none, List.append_nil]

theorem expected_publicSigningWork_messageCalls (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (message : Message) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl
        (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] *
      result.1.1.2.messageCalls.length) = digestAttemptExpectation digestAttemptLimit key message cache := by
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, tsum_probOutput_map_mul]
  simp only [digestWork_messageCalls]
  rw [publicDigestLoop_eq, simulateQ_boundaryComputation]
  exact (expectedBoundaryMessageCalls_eq_queryCharge key.parameter (signDigestLoop digestAttemptLimit key message) cache).trans
    (expectedQueryCharge_signDigestLoop_message digestAttemptLimit key message cache)

theorem targetCreationMultiplier_sign_le_digestAttempts (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    targetCreationMultiplier key cache (.inr message) ≤ digestAttemptExpectation digestAttemptLimit key message cache := by
  have h := probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)
  have hs := mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal))) h
  have hc : (((2 ^ ftsTreeHeight : Nat) : ENNReal) *
      (digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)) =
      digestAttemptExpectation digestAttemptLimit key message cache := by
    rw [mul_left_comm, ENNReal.mul_inv_cancel (by norm_num [ftsTreeHeight]) (by finiteness), mul_one]
  rw [hc] at hs
  exact hs

private theorem expected_signing_cache_messageCalls {inputs : Finset HashInput}
    (native : SPMF (Option SigningRecord × State inputs))
    (candidates : CanonicalCoordinate → Finset Digest)
    (ha : ∀ coordinate, (candidates coordinate).Nonempty)
    (work : ProbComp ((PublicSigningRecord × Nat) × QueryCache HashSpec)) (expected : ENNReal)
    (hwork : (∑' result, Pr[= result | work] * result.1.1.2.messageCalls.length) = expected)
    (hkernel : cacheResult <$> native =
      (UniformTableCompletion.complete candidates >>= fun actual =>
        (fun result => (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1.1), result.2)) <$>
          𝒟[work])) :
    (∑' result, Pr[= result | native] * result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal))) = expected := by
  have h := congrArg (fun law : SPMF (Option SigningRecord × QueryCache HashSpec) =>
    ∑' result, Pr[= result | law] * result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal))) hkernel
  rw [tsum_probOutput_map_mul, tsum_probOutput_bind_mul] at h
  simp only [tsum_probOutput_map_mul, Option.elim_some, completePublicSigningRecord_trace, expected_evalDist, cacheResult] at h
  have hm : (∑' actual, Pr[= actual | UniformTableCompletion.complete candidates]) = 1 := by
    rw [UniformTableCompletion.complete_of_nonempty candidates ha]
    simp only [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.tsum_coe]
  rw [hwork, ENNReal.tsum_mul_right, hm, one_mul] at h
  exact h

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram

theorem expected_lazySigning_messageCalls (message : Message) (state : State inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state] *
      result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal))) =
      digestAttemptExpectation digestAttemptLimit key message state.memory.external.cache := by
  have hin := digestInputs_of_request key inputs words selections message state.memory.routing.known hinputs
  exact expected_signing_cache_messageCalls _ state.candidates ha _ _
    (expected_publicSigningWork_messageCalls key state.memory.routing.known words selections message state.memory.external.cache)
    (lazyRun_jointSigningProgram_cache key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
      key.root message (by simpa only [publicDigestLoop_eq] using hin) state ha hcovered)

noncomputable def monitoredMessageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    match input with
    | .inl world => hashQueryCharge (messageHashCharge key.parameter) state.1 world
    | .inr message => digestAttemptExpectation digestAttemptLimit key message state.1
  else 0

theorem certificateMonitorMass_le_monitoredMessageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    certificateMonitorMass key budget input state ≤ monitoredMessageCharge key budget input state := by
  by_cases ha : CertificateMonitorActive key budget input state
  · rw [certificateMonitorMass, monitoredMessageCharge.eq_def, if_pos ha, if_pos ha]
    cases input with
    | inl world =>
        exact (targetCreationMultiplier_le_expected_messageCalls key (.inl world) state.1).trans_eq
          (expected_originalProposalRecord_world_messageCalls key world state.1)
    | inr message => exact targetCreationMultiplier_sign_le_digestAttempts key message state.1
  · simp only [certificateMonitorMass, monitoredMessageCharge.eq_def, if_neg ha, le_refl]

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

attribute [local irreducible] certificateMonitorUpdate certificateMonitorCharge certificateMonitorMass
  monitorView monitoredSigningResult monitoredMessageCharge

theorem monitoredStep_world_messageCalls (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (hinputs : requestInputs key (.inl input) ⊆ inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state.1))
    (result : Option (OracleWorld.Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter (.inl input) state result ≠ 0) :
    (result.2.2.messageCalls : ENNReal) = state.2.messageCalls + monitoredMessageCharge key budget (.inl input) (monitorView state) := by
  rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  by_cases hn : raw.1 = none
  · have hz := (stopped_world_message_charges_zero key inputs hencoding words publicReplies selections rows input state hinputs hcovered raw hraw hn).2
    have hc : monitoredMessageCharge key budget (.inl input) (monitorView state) = 0 := by
      unfold monitoredMessageCharge monitorView
      simp only [hz, ite_self]
    simp only [monitoredWorldResult, hn, Option.elim_none, hc, add_zero]
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hn
    simp only [monitoredWorldResult, ha, Option.elim_some]
    by_cases hactive : CertificateMonitorActive key budget (.inl input) (monitorView state)
    · rw [certificateMonitorUpdate_messageCalls _ _ _ _ _ _ _ _ hactive, Nat.cast_add]
      simp only [proposalOfWorldResult, signingBoundaryTrace_messageCalls key.parameter input answer state.1.memory.external.cache,
        monitoredMessageCharge.eq_def, if_pos hactive]
      simp only [monitorView]
    · rw [certificateMonitorUpdate_inactive _ _ _ _ _ _ _ _ hactive]
      simp only [monitoredMessageCharge.eq_def, if_neg hactive, add_zero]
      simp only [monitorView]

theorem monitoredSigningResult_messageCalls (message : Message) (annotation : Nat × Index)
    (state : MonitoredState inputs) (raw : Option SigningRecord × State inputs) :
    ((monitoredSigningResult key budget required stopAfter message annotation state raw).2.2.messageCalls : ENNReal) =
      state.2.messageCalls + if CertificateMonitorActive key budget (.inr message) (monitorView state) then
        raw.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal)) else 0 := by
  rcases raw with ⟨answer, after⟩
  cases answer with
  | none => simp only [monitoredSigningResult, Option.elim_none, ite_self, add_zero]
  | some record =>
      simp only [monitoredSigningResult, Option.elim_some]
      by_cases ha : CertificateMonitorActive key budget (.inr message) (monitorView state)
      · rw [certificateMonitorUpdate_messageCalls _ _ _ _ _ _ _ _ ha, Nat.cast_add, if_pos ha]
        simp only [monitorView, proposalOfSigningRecord]
      · rw [certificateMonitorUpdate_inactive _ _ _ _ _ _ _ _ ha, if_neg ha, add_zero]
        simp only [monitorView]

private theorem tsum_eq_one_of_bind_const {Result : Type} (law : SPMF Result)
    (h : (law >>= fun _ => (pure () : SPMF Unit)) = pure ()) :
    (∑' result, Pr[= result | law]) = 1 := by
  have hh := congrArg (fun law : SPMF Unit => Pr[= () | law]) h
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using hh

private theorem expected_signing_step_messageCalls (message : Message) (state : MonitoredState inputs)
    (law : SPMF (Option SigningRecord × State inputs)) (hm : (∑' result, Pr[= result | law]) = 1)
    (hmessage : (∑' result, Pr[= result | law] * result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal))) =
      digestAttemptExpectation digestAttemptLimit key message state.1.memory.external.cache) :
    (∑' result, Pr[= result |
      ((liftM (signingAnnotation key budget message (monitorView state)) : SPMF _) >>= fun annotation =>
        monitoredSigningResult key budget required stopAfter message annotation state <$> law)] * result.2.2.messageCalls) =
      state.2.messageCalls + monitoredMessageCharge key budget (.inr message) (monitorView state) := by
  have hmannotation : (∑' annotation, Pr[= annotation | (liftM (signingAnnotation key budget message (monitorView state)) : SPMF _)]) = 1 := by
    simp only [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.tsum_coe]
  have hc : monitoredMessageCharge key budget (.inr message) (monitorView state) =
      if CertificateMonitorActive key budget (.inr message) (monitorView state) then
        digestAttemptExpectation digestAttemptLimit key message state.1.memory.external.cache else 0 := by
    unfold monitoredMessageCharge monitorView
    rfl
  rw [hc, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, monitoredSigningResult_messageCalls]
  by_cases ha : CertificateMonitorActive key budget (.inr message) (monitorView state)
  · simp only [if_pos ha, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hm, one_mul, hmessage, hmannotation]
  · simp only [if_neg ha, add_zero, ENNReal.tsum_mul_right, hm, hmannotation, one_mul]

theorem expected_monitoredStep_messageCalls (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      result.2.2.messageCalls) = state.2.messageCalls + monitoredMessageCharge key budget input (monitorView state) := by
  cases input with
  | inl input =>
      calc
        _ = ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter (.inl input) state] *
            ((state.2.messageCalls : ENNReal) + monitoredMessageCharge key budget (.inl input) (monitorView state)) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter (.inl input) state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            rw [monitoredStep_world_messageCalls key inputs hencoding words publicReplies selections rows budget required stopAfter
              input state hinputs hvalid.2 result hr]
        _ = _ := by
          rw [ENNReal.tsum_mul_right, tsum_monitoredStep_eq_one key inputs hencoding words publicReplies selections rows
            budget required stopAfter (.inl input) state hvalid.1, one_mul]
  | inr message =>
      rw [monitoredStep]
      apply expected_signing_step_messageCalls key inputs budget required stopAfter message state
      · apply tsum_eq_one_of_bind_const
        exact lazyRun_bind_const (environment key.parameter inputs hencoding words publicReplies selections rows)
          (simulateQ (embed inputs state.1.memory.routing)
            (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message))
          state.1 hvalid.1 (pure ())
      · exact expected_lazySigning_messageCalls key inputs hencoding words publicReplies selections rows message state.1 hinputs hvalid.1 hvalid.2

theorem expected_monitoredStep_creationMass (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      result.2.2.creationMass) = state.2.creationMass + certificateMonitorMass key budget input (monitorView state) := by
  calc
    _ = ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        (state.2.creationMass + certificateMonitorMass key budget input (monitorView state)) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(monitoredStep_creation_counters key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state hvalid hinputs result hr).2]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_monitoredStep_eq_one key inputs hencoding words publicReplies selections rows
        budget required stopAfter input state hvalid.1, one_mul]

theorem expected_monitoredRun_creationMass_le_messageCalls {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : State inputs) (spent : Nat) (stopped : Bool)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped)] * result.2.2.creationMass) ≤
      ∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation
        (state, initialCertificateMonitor spent stopped)] * result.2.2.messageCalls := by
  rw [expected_monitoredRun_accumulator key inputs hencoding words publicReplies selections rows budget required stopAfter
      CertificateMonitor.creationMass (certificateMonitorMass key budget)
      (expected_monitoredStep_creationMass key inputs hencoding words publicReplies selections rows budget required stopAfter)
      computation (state, initialCertificateMonitor spent stopped) ⟨ha, hcovered⟩ hinputs,
    expected_monitoredRun_accumulator key inputs hencoding words publicReplies selections rows budget required stopAfter
      (fun monitor => (monitor.messageCalls : ENNReal)) (monitoredMessageCharge key budget)
      (expected_monitoredStep_messageCalls key inputs hencoding words publicReplies selections rows budget required stopAfter)
      computation (state, initialCertificateMonitor spent stopped) ⟨ha, hcovered⟩ hinputs]
  simp only [initialCertificateMonitor, Nat.cast_zero, zero_add]
  exact expectedMonitoredPayment_mono key inputs hencoding words publicReplies selections rows budget required stopAfter
    _ _ (certificateMonitorMass_le_monitoredMessageCharge key budget) computation _

end SphincsSecurity.Concrete.RetainedResidual
