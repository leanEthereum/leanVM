import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestSelectionWeight
import SphincsSecurity.Proof.Residual.RetainedResidualCompletion
import SphincsSecurity.Proof.Residual.RetainedResidualDigestLaw
import SphincsSecurity.Proof.Residual.RetainedResidualRows
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs publicSignPlan
set_option backward.isDefEq.respectTransparency false

def digestWork (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (selected : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) : PublicSigningRecord × Nat :=
  match selected.1 with
  | none => (((none, none), selected.2), 0)
  | some (randomness, index, leaves) =>
      let plan := publicSignPlan known words selections randomness index leaves
      (((plan.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ plan.2), plan.2)

theorem publicSigningWork_eq_digestWork (parameter : PublicParameter) (root : Digest) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    ResidualByteFrontend.publicSigningWork parameter root known words selections message =
      digestWork known words selections <$> boundaryComputation parameter (publicDigestLoop parameter root message digestAttemptLimit) := by
  rw [ResidualByteFrontend.publicSigningWork, map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨selected, trace⟩
  cases selected <;> rfl

theorem completePublicSigningRecord_digestWork_consistent (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (loop : DigestLoopRecord) (trace : SigningBoundaryTrace) :
    DigestCompletionConsistent loop
      ((completePublicSigningRecord ftsSecret (digestWork known words selections (loop.1, trace)).1).1, loop.2) := by
  rcases loop with ⟨selected, cache⟩
  cases selected with
  | none => simp [DigestCompletionConsistent, digestWork, completePublicSigningRecord, selectedLoopView?]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      constructor
      · rfl
      · intro signature hs
        simp only [digestWork, completePublicSigningRecord, Option.map_eq_some_iff] at hs
        obtain ⟨plan, hplan, rfl⟩ := hs
        have hr : plan.randomness = randomness := by
          unfold publicSignPlan at hplan
          obtain ⟨parts, _, rfl⟩ := Option.map_eq_some_iff.mp hplan
          rfl
        exact ⟨index, leaves, by simp only [PublicSigningPlan.finish, hr]⟩

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_completeWork_memory (routing : Routing) (work : PublicSigningRecord × Nat) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    forgetState <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state =
      (UniformTableCompletion.complete state.candidates >>= fun actual =>
        pure (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1),
          state.memory.accountWork work.2)) := by
  rw [← run_erasure _ _ state ha]
  simp only [map_bind, observedRun_completeWork_memory parameter inputs hencoding words publicReplies selections rows routing,
    ResidualTableCompletion.completeRows_bind_const]

theorem lazyRun_completeWork_cache (routing : Routing) (work : PublicSigningRecord × Nat) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    cacheResult <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state =
      (UniformTableCompletion.complete state.candidates >>= fun actual =>
        pure (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1),
          state.memory.external.cache)) := by
  have h := congrArg (fun law : SPMF (Option SigningRecord × Memory) =>
    (fun result => (result.1, result.2.external.cache)) <$> law)
      (lazyRun_completeWork_memory parameter inputs hencoding words publicReplies selections rows routing work state ha)
  unfold cacheResult
  simpa only [Functor.map_map, Function.comp_def, forgetState, cacheResult, map_bind, map_pure,
    Memory.accountWork, ResidualByteFrontend.accountWork] using h

theorem lazyRun_completeWork_support (routing : Routing) (work : PublicSigningRecord × Nat) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state result ≠ 0) :
    ∃ actual : Labels,
      result.1 = some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1) ∧
      result.2.memory = state.memory.accountWork work.2 := by
  have hmap : (forgetState <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state) (forgetState result) ≠ 0 :=
    map_nonzero _ forgetState result hresult
  rw [lazyRun_completeWork_memory parameter inputs hencoding words publicReplies selections rows routing work state ha] at hmap
  obtain ⟨actual, _, hfinish⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hmap
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hfinish
  exact ⟨actual, congrArg Prod.fst hfinish, congrArg Prod.snd hfinish⟩

end SphincsSecurity.Concrete.RetainedResidual
