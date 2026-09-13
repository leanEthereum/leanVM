import SphincsSecurity.Proof.Residual.RetainedResidualCacheKernels
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop lazyRun environment ResidualByteFrontend.jointSigningProgram
set_option backward.isDefEq.respectTransparency false

private theorem expected_add_le {Result : Type} (law : SPMF Result) (base charge : ENNReal)
    (increment total : Result → ENNReal) (hmass : (∑' result, Pr[= result | law]) = 1)
    (hcharge : (∑' result, Pr[= result | law] * increment result) = charge)
    (hpoint : ∀ result, law result ≠ 0 → base + increment result ≤ total result) :
    base + charge ≤ ∑' result, Pr[= result | law] * total result := by
  calc
    _ = ∑' result, Pr[= result | law] * (base + increment result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, hcharge, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : law result = 0
      · simp only [SPMF.probOutput_eq_apply, hr, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (hpoint result hr)

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazySigning_messageCalls_hashCalls (message : Message) (state : State inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option SigningRecord × State inputs)
    (hr : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state result ≠ 0) :
    (state.memory.external.hashCalls : ENNReal) + result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal)) ≤
      (result.2.memory.external.hashCalls : ENNReal) := by
  have hin := digestInputs_of_request key inputs words selections message state.memory.routing.known hinputs
  obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state ha hcovered result hr
  rw [hrecord, Option.elim_some, hmemory]
  change (state.memory.external.hashCalls : ENNReal) + record.2.messageCalls.length ≤
    ((state.memory.external.hashCalls + record.2.hashCalls : Nat) : ENNReal)
  rw [Nat.cast_add]
  exact add_le_add le_rfl (Nat.cast_le.mpr (List.length_filterMap_le _ _))

private theorem tsum_lazyRun_eq_one {Result : Type} (computation : OracleComp (World inputs) Result)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows) computation state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (lazyRun_bind_const (environment key.parameter inputs hencoding words publicReplies selections rows) computation state ha (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

theorem expected_lazySigning_hashCalls_lower (message : Message) (state : State inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (state.memory.external.hashCalls : ENNReal) + digestAttemptExpectation digestAttemptLimit key message state.memory.external.cache ≤
      ∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state] *
        (result.2.memory.external.hashCalls : ENNReal) := by
  exact expected_add_le _ _ _ (fun result => result.1.elim 0 (fun record => (record.2.messageCalls.length : ENNReal))) _
    (tsum_lazyRun_eq_one key inputs hencoding words publicReplies selections rows _ state ha)
    (expected_lazySigning_messageCalls key inputs hencoding words publicReplies selections rows message state hinputs ha hcovered)
    (lazySigning_messageCalls_hashCalls key inputs hencoding words publicReplies selections rows message state hinputs ha hcovered)

theorem expected_lazyWorld_hashCalls_lower (world : OracleWorld.Domain) (state : State inputs)
    (hinputs : hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (state.memory.external.hashCalls : ENNReal) + hashQueryCharge (FtsProbeSimulation.messageHashCharge key.parameter) state.memory.external.cache world ≤
      ∑' result, Pr[= result | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
        (liftM (OracleWorld.query world)) state] * (result.2.memory.external.hashCalls : ENNReal) := by
  have hm : (∑' result, Pr[= result | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
      (liftM (OracleWorld.query world)) state]) = 1 :=
    tsum_lazyRun_eq_one key inputs hencoding words publicReplies selections rows _ state ha
  refine expected_add_le _ _ _ (fun _ => hashQueryCharge (FtsProbeSimulation.messageHashCharge key.parameter) state.memory.external.cache world) _ hm ?_ ?_
  · rw [ENNReal.tsum_mul_right, hm, one_mul]
  · intro result hr
    rw [lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows state.memory.routing world hinputs state ha result hr, Nat.cast_add]
    apply add_le_add le_rfl
    cases world <;> simp [hashQueryCharge, FtsProbeSimulation.messageHashCharge]
    split <;> norm_num

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

private theorem expected_signing_annotation_hashCalls (message : Message) (state : MonitoredState inputs)
    (native : SPMF (Option SigningRecord × State inputs)) :
    (∑' result, Pr[= result | ((liftM (signingAnnotation key budget message (monitorView state)) : SPMF _) >>= fun annotation =>
      monitoredSigningResult key budget required stopAfter message annotation state <$> native)] *
        (result.2.1.memory.external.hashCalls : ENNReal)) =
      ∑' result, Pr[= result | native] * (result.2.memory.external.hashCalls : ENNReal) := by
  have hprojection (annotation : Nat × Index) (raw : Option SigningRecord × State inputs) :
      (monitoredSigningResult key budget required stopAfter message annotation state raw).2.1.memory.external.hashCalls = raw.2.memory.external.hashCalls := by
    rcases raw with ⟨answer, after⟩
    cases answer <;> rfl
  rw [tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, hprojection, ENNReal.tsum_mul_right]
  simp only [SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.tsum_coe, one_mul]

theorem expected_monitoredStep_hashCalls_lower (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs) :
    (state.1.memory.external.hashCalls : ENNReal) + nativeMessageCharge key input (monitorView state) ≤
      ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        (result.2.1.memory.external.hashCalls : ENNReal) := by
  cases input with
  | inl world =>
      rw [monitoredStep, tsum_probOutput_map_mul, lazyRun_externalProgram]
      exact expected_lazyWorld_hashCalls_lower key inputs hencoding words publicReplies selections rows world state.1 hinputs hvalid.1
  | inr message =>
      exact (expected_lazySigning_hashCalls_lower key inputs hencoding words publicReplies selections rows message state.1 hinputs hvalid.1 hvalid.2).trans_eq
        (expected_signing_annotation_hashCalls key inputs budget required stopAfter message state _).symm

end SphincsSecurity.Concrete.RetainedResidual
