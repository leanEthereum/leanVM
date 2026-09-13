import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestSigningCompletion
import SphincsSecurity.Proof.Residual.ResidualSigningProgram
import SphincsSecurity.Proof.Residual.RetainedResidualSigningKernel
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def completeWorkCache (actual : Labels) (result : Option (PublicSigningRecord × Nat) × QueryCache HashSpec) :
    Option SigningRecord × QueryCache HashSpec :=
  (result.1.map (fun work => completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1), result.2)

def eraseSigningTrace (result : Option SigningRecord × QueryCache HashSpec) :
    Option (Option Signature × Option FewTimeView) × QueryCache HashSpec := (result.1.map Prod.fst, result.2)

def digestCompletionValue (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (actual : Labels) (loop : DigestLoopRecord) : (Option Signature × Option FewTimeView) × QueryCache HashSpec :=
  ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf))
    (digestWork known words selections (loop.1, 1)).1).1, loop.2)

theorem digestCompletionValue_preservesMessages (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (actual : Labels) (loop : DigestLoopRecord) :
    DigestCompletionPreservesMessages key loop (digestCompletionValue known words selections actual loop) :=
  ⟨completePublicSigningRecord_digestWork_consistent known words selections _ loop 1, rfl⟩

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_jointSigningProgram_cache (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    cacheResult <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state =
      (UniformTableCompletion.complete state.candidates >>= fun actual =>
        (fun result => (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1.1), result.2)) <$>
          𝒟[(simulateQ romImpl (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message)).run
            state.memory.external.cache]) := by
  let work := ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message
  have hwork : hashInputs work ⊆ inputs := by
    simpa only [work, ResidualByteFrontend.hashInputs_publicSigningWork] using hinputs
  have hmwork := ResidualByteFrontend.publicSigningWork_messageOnly parameter root routing.known words selections message
  rw [ResidualByteFrontend.jointSigningProgram, simulateQ_bind, lazyRun_bind, map_bind]
  change (lazyByteRun parameter inputs hencoding words publicReplies selections rows routing work state >>= fun result =>
    cacheResult <$> result.1.elim (pure (none, result.2)) (fun value =>
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork value)) result.2)) = _
  calc
    _ = lazyByteRun parameter inputs hencoding words publicReplies selections rows routing work state >>= fun result =>
        UniformTableCompletion.complete state.candidates >>= fun actual => pure (completeWorkCache actual (cacheResult result)) := by
      apply RetainedObservation.bind_congr
      intro result hresult
      obtain ⟨⟨value, hvalue⟩, hcandidates⟩ := lazyByteRun_message_support parameter inputs hencoding words publicReplies selections rows
        routing work hwork hmwork state hcovered result hresult
      have ha' : ∀ coordinate, (result.2.candidates coordinate).Nonempty := by rw [hcandidates]; exact ha
      rw [hvalue, Option.elim_some, lazyRun_completeWork_cache parameter inputs hencoding words publicReplies selections rows routing value result.2 ha',
        hcandidates]
      simp only [completeWorkCache, cacheResult, hvalue, Option.map_some]
    _ = UniformTableCompletion.complete state.candidates >>= fun actual =>
        completeWorkCache actual <$> (cacheResult <$>
          lazyByteRun parameter inputs hencoding words publicReplies selections rows routing work state) := by
      rw [RetainedObservation.bind_comm]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    _ = _ := by
      rw [lazyByteRun_message_rom parameter inputs hencoding words publicReplies selections rows routing work hwork hmwork state hcovered]
      apply congrArg (fun next : Labels → SPMF (Option SigningRecord × QueryCache HashSpec) =>
        UniformTableCompletion.complete state.candidates >>= next)
      funext actual
      rw [Functor.map_map]
      congr 1

theorem lazyRun_jointSigningProgram_digestLaw (routing : Routing) (key : SecretKey) (hparameter : key.parameter = parameter)
    (message : Message) (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    eraseSigningTrace <$> (cacheResult <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter key.root routing.known words selections message)) state) =
      (UniformTableCompletion.complete state.candidates >>= fun actual =>
        Prod.map some id <$> 𝒟[digestCompletionValue routing.known words selections actual <$>
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.memory.external.cache]) := by
  have hloop : publicDigestLoop parameter key.root message digestAttemptLimit = signDigestLoop digestAttemptLimit key message := by
    rw [← hparameter, publicDigestLoop_eq]
  have hin : hashInputs (publicDigestLoop parameter key.root message digestAttemptLimit) ⊆ inputs := by rwa [hloop]
  rw [lazyRun_jointSigningProgram_cache parameter inputs hencoding words publicReplies selections rows routing key.root message hin state ha hcovered,
    map_bind]
  apply congrArg (fun next : Labels → SPMF (Option (Option Signature × Option FewTimeView) × QueryCache HashSpec) =>
    UniformTableCompletion.complete state.candidates >>= next)
  funext actual
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, evalDist_map, Functor.map_map,
    Functor.map_map, hloop, simulateQ_boundaryComputation]
  rw [← boundaryRun_forget parameter (signDigestLoop digestAttemptLimit key message) state.memory.external.cache,
    evalDist_map, evalDist_map, Functor.map_map, Functor.map_map]
  change (fun result => eraseSigningTrace
    (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf))
      (digestWork routing.known words selections result.1).1), result.2)) <$>
      𝒟[boundaryRun parameter (signDigestLoop digestAttemptLimit key message) state.memory.external.cache] = _
  congr 1
  funext result
  rcases result with ⟨⟨selected, trace⟩, cache⟩
  cases selected <;> rfl

theorem lazyRun_jointSigningProgram_some (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record := by
  have h := map_nonzero _ cacheResult result hresult
  rw [lazyRun_jointSigningProgram_cache parameter inputs hencoding words publicReplies selections rows routing root message
    hinputs state ha hcovered, RetainedObservation.bind_nonzero] at h
  obtain ⟨actual, _, h⟩ := h
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at h
  obtain ⟨work, _, h⟩ := h
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
  exact ⟨_, congrArg Prod.fst h⟩

end SphincsSecurity.Concrete.RetainedResidual
