import SphincsSecurity.Proof.Fts.CertificateCacheExceptionKernels
import SphincsSecurity.Proof.Residual.RetainedResidualCacheAccounting
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
open FtsProbeSimulation (messageAnswers MessageHashInput messageHashCharge)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_cache_subset (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    QueryCache.toSet state.memory.external.cache ⊆
      QueryCache.toSet (checkedHashResult key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache := by
  rintro ⟨other, reply⟩ hreply
  change state.memory.external.cache other = some reply at hreply
  change (checkedHashResult key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache other = some reply
  by_cases hne : other ≠ input.val
  · rw [checkedHashResult_cache_of_ne key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state hcovered other hne]
    exact hreply
  · obtain rfl := not_ne_iff.mp hne
    have hp := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => result.2.memory.cache input.val)
      (hashResult_project key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
    have hr := congrArg (fun result : Option HashOutput × ExternalMemory => result.2.cache input.val)
      (ResidualByteFrontend.hashQueryResult_project key.parameter inputs words routing.disclosed routing.known
        (freshPrefix key.parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
        actual seed input (project state) hcovered
        (freshPrefix_local key.parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input))
    change (hashResult key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache input.val = _
    apply hp.trans
    apply hr.trans
    simp only [ResidualByteFrontend.publicCachedReply, project, hreply, Option.elim_some,
      ResidualByteFrontend.delivered, storeReply, Function.update_self]

theorem expected_lazyWorld_cacheWeight_le (routing : Routing) (input : OracleWorld.Domain)
    (state : State inputs) (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : CacheSizeBound state.memory) :
    (∑' result, Pr[= result | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] * certificateCacheExceptionWeight key result.2.memory.external.cache) ≤
      certificateCacheExceptionWeight key state.memory.external.cache +
        hashQueryCharge (fun cache hash => messageHashCharge key.parameter cache hash * certificateCacheExceptionRate) state.memory.external.cache input := by
  by_cases hm : ∀ hash, input = .inr hash → MessageHashInput key.parameter hash
  · have heq := congrArg (fun law : SPMF (Option (OracleWorld.Range input) × QueryCache HashSpec) =>
        ∑' result, Pr[= result | law] * certificateCacheExceptionWeight key result.2)
      (lazyByteRun_world_message_rom key.parameter inputs hencoding words publicReplies selections rows routing input hinputs hm state hcovered)
    simp only [tsum_probOutput_map_mul, cacheResult, Prod.map_snd, id_eq] at heq
    rw [heq]
    exact expected_certificateCacheExceptionWeight_rom key input state.memory.external.cache (Finite.of_enncard_le hbound)
  · cases input with
    | inl sample => exact False.elim (hm (by intro hash heq; cases heq))
    | inr input =>
        have hmessage : ¬MessageHashInput key.parameter input := fun h => hm (by intro hash heq; cases heq; exact h)
        have hin : input ∈ inputs := hinputs (by simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
        simp only [hashQueryCharge, Sum.elim_inr, messageHashCharge, if_neg hmessage, zero_mul, add_zero]
        calc
          _ ≤ ∑' result, Pr[= result | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows routing
              (liftM (OracleWorld.query (.inr input))) state] * certificateCacheExceptionWeight key state.memory.external.cache := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hs : lazyByteRun key.parameter inputs hencoding words publicReplies selections rows routing
                (liftM (OracleWorld.query (.inr input))) state result = 0
            · simp only [SPMF.probOutput_eq_apply, hs, zero_mul, le_refl]
            · apply mul_le_mul' le_rfl
              have hb := lazyByteRun_world_cacheSizeBound key inputs hencoding words publicReplies selections rows routing
                (.inr input) hinputs state ha hcovered hbound result hs
              apply certificateCacheExceptionWeight_messageAnswers_le key _ _ (Finite.of_enncard_le hb)
                (lazyByteRun_hash_nonmessage key.parameter inputs hencoding words publicReplies selections rows routing
                  input hin state ha hcovered hmessage result hs).symm
              obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result key.parameter inputs hencoding words publicReplies selections rows routing
                input hin state ha result hs
              have hle := checkedHashResult_cache_subset key inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hcovered
              unfold QueryCache.enncard
              exact_mod_cast Set.encard_le_encard hle
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_publicSigningWork_cacheWeight_le (known : Labels) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl
        (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] *
      certificateCacheExceptionWeight key result.2) ≤
      certificateCacheExceptionWeight key cache + digestAttemptExpectation digestAttemptLimit key message cache * certificateCacheExceptionRate := by
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, tsum_probOutput_map_mul,
    publicDigestLoop_eq, simulateQ_boundaryComputation]
  have h := expected_certificateCacheExceptionWeight_boundary key (signDigestLoop digestAttemptLimit key message) cache hfinite
  have hc := (expectedBoundaryMessageCalls_eq_queryCharge key.parameter (signDigestLoop digestAttemptLimit key message) cache).trans
    (expectedQueryCharge_signDigestLoop_message digestAttemptLimit key message cache)
  change (∑' result, Pr[= result | boundaryRun key.parameter (signDigestLoop digestAttemptLimit key message) cache] *
    (result.1.2.messageCalls.length : ENNReal)) = _ at hc
  rw [hc] at h
  exact h

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram

private theorem expected_evalDist {Result : Type} (computation : ProbComp Result) (weight : Result → ENNReal) :
    (∑' result, Pr[= result | 𝒟[computation]] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl

private theorem expected_signing_cache_weight {inputs : Finset HashInput}
    (native : SPMF (Option SigningRecord × State inputs)) (candidates : CanonicalCoordinate → Finset Digest)
    (work : ProbComp ((PublicSigningRecord × Nat) × QueryCache HashSpec)) (bound : ENNReal)
    (hwork : (∑' result, Pr[= result | work] * certificateCacheExceptionWeight key result.2) ≤ bound)
    (hkernel : cacheResult <$> native =
      (UniformTableCompletion.complete candidates >>= fun actual =>
        (fun result => (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1.1), result.2)) <$>
          𝒟[work])) :
    (∑' result, Pr[= result | native] * certificateCacheExceptionWeight key result.2.memory.external.cache) ≤ bound := by
  have heq := congrArg (fun law : SPMF (Option SigningRecord × QueryCache HashSpec) =>
    ∑' result, Pr[= result | law] * certificateCacheExceptionWeight key result.2) hkernel
  rw [tsum_probOutput_map_mul, tsum_probOutput_bind_mul] at heq
  simp only [tsum_probOutput_map_mul, cacheResult, expected_evalDist] at heq
  rw [heq]
  calc
    _ ≤ ∑' actual, Pr[= actual | UniformTableCompletion.complete candidates] * bound :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl hwork
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_lazySigning_cacheWeight_le (message : Message) (state : State inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hfinite : Finite state.memory.external.cache) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state] *
      certificateCacheExceptionWeight key result.2.memory.external.cache) ≤
      certificateCacheExceptionWeight key state.memory.external.cache +
        digestAttemptExpectation digestAttemptLimit key message state.memory.external.cache * certificateCacheExceptionRate := by
  have hin := digestInputs_of_request key inputs words selections message state.memory.routing.known hinputs
  exact expected_signing_cache_weight key _ state.candidates _ _
    (expected_publicSigningWork_cacheWeight_le key words selections state.memory.routing.known message state.memory.external.cache hfinite)
    (lazyRun_jointSigningProgram_cache key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
      key.root message (by simpa only [publicDigestLoop_eq] using hin) state ha hcovered)

noncomputable def nativeMessageCharge (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) : ENNReal :=
  match input with
  | .inl world => hashQueryCharge (messageHashCharge key.parameter) state.1 world
  | .inr message => digestAttemptExpectation digestAttemptLimit key message state.1

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredSigningResult_cache (message : Message) (annotation : Nat × Index)
    (state : MonitoredState inputs) (raw : Option SigningRecord × State inputs) :
    (monitoredSigningResult key budget required stopAfter message annotation state raw).2.1.memory.external.cache =
      raw.2.memory.external.cache := by
  rcases raw with ⟨answer, after⟩
  cases answer <;> rfl

private theorem expected_signing_annotation_cacheWeight (message : Message) (state : MonitoredState inputs)
    (native : SPMF (Option SigningRecord × State inputs)) (bound : ENNReal)
    (hbound : (∑' result, Pr[= result | native] * certificateCacheExceptionWeight key result.2.memory.external.cache) ≤ bound) :
    (∑' result, Pr[= result | ((liftM (signingAnnotation key budget message (monitorView state)) : SPMF _) >>= fun annotation =>
      monitoredSigningResult key budget required stopAfter message annotation state <$> native)] *
        certificateCacheExceptionWeight key result.2.1.memory.external.cache) ≤ bound := by
  rw [tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, monitoredSigningResult_cache]
  calc
    _ ≤ ∑' annotation, Pr[= annotation | (liftM (signingAnnotation key budget message (monitorView state)) : SPMF _)] * bound :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl hbound
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_monitoredStep_cacheWeight_le (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) (hbound : CacheSizeBound state.1.memory) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      certificateCacheExceptionWeight key result.2.1.memory.external.cache) ≤
      certificateCacheExceptionWeight key state.1.memory.external.cache +
        nativeMessageCharge key input (monitorView state) * certificateCacheExceptionRate := by
  cases input with
  | inl world =>
      rw [monitoredStep, tsum_probOutput_map_mul, lazyRun_externalProgram]
      have h := expected_lazyWorld_cacheWeight_le key inputs hencoding words publicReplies selections rows state.1.memory.routing
        world state.1 hinputs hvalid.1 hvalid.2 hbound
      cases world <;> simpa only [monitoredWorldResult, nativeMessageCharge, monitorView, hashQueryCharge, Sum.elim_inl,
        Sum.elim_inr, zero_mul] using h
  | inr message =>
      exact expected_signing_annotation_cacheWeight key inputs budget required stopAfter message state _ _
        (expected_lazySigning_cacheWeight_le key inputs hencoding words publicReplies selections rows
          message state.1 hinputs hvalid.1 hvalid.2 (Finite.of_enncard_le hbound))

end SphincsSecurity.Concrete.RetainedResidual
