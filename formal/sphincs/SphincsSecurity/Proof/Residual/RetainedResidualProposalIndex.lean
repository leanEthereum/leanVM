import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.OriginalProposalExecution
import SphincsSecurity.Proof.Residual.RetainedResidualSigningLaw
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  lazyRun environment signDigestLoop ResidualByteFrontend.jointSigningProgram
set_option backward.isDefEq.respectTransparency false

theorem completeSelectedIndex_fallback (view : Option FewTimeView) :
    𝒟[completeSelectedIndex view] =
      (fun fallback : Index => view.elim fallback Prod.fst) <$> (liftM (PMF.uniformOfFintype Index) : SPMF Index) := by
  cases view with
  | none =>
      simp only [completeSelectedIndex, Option.elim_none, id_map']
      apply SPMF.ext
      intro index
      change Pr[= index | ($ᵗ Index : ProbComp Index)] = _
      rw [probOutput_uniformSample, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  | some view =>
      simp only [completeSelectedIndex, Option.elim_some, evalDist_pure, map_eq_bind_pure_comp, Function.comp_def]
      exact (RetainedObservation.lift_bind_const _ _).symm

noncomputable def completeRecordIndex {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView) :
    SPMF (Result × Index) :=
  law >>= fun result => (fun index => (result, index)) <$> 𝒟[completeSelectedIndex (view result)]

theorem completeRecordIndex_record {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView) :
    Prod.fst <$> completeRecordIndex law view = law := by
  rw [completeRecordIndex, map_bind]
  simp only [Functor.map_map]
  calc
    _ = law >>= pure := by
      apply congrArg (law >>= ·)
      funext result
      rw [completeSelectedIndex_fallback, Functor.map_map, map_eq_bind_pure_comp]
      exact RetainedObservation.lift_bind_const _ _
    _ = _ := bind_pure law

theorem completeRecordIndex_index {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView) :
    Prod.snd <$> completeRecordIndex law view =
      ((view <$> law) >>= fun selected => 𝒟[completeSelectedIndex selected]) := by
  simp only [completeRecordIndex, map_bind, Functor.map_map, bind_map_left, id_map']

theorem completeRecordIndex_fallback {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView) :
    completeRecordIndex law view =
      ((liftM (PMF.uniformOfFintype Index) : SPMF Index) >>= fun fallback =>
        (fun result => (result, (view result).elim fallback Prod.fst)) <$> law) := by
  simp only [completeRecordIndex, completeSelectedIndex_fallback, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  exact RetainedObservation.bind_comm _ _ _

private theorem lift_probComp_evalDist {Result : Type} (computation : ProbComp Result) :
    (liftM (liftM computation : PMF Result) : SPMF Result) = 𝒟[computation] := by
  apply SPMF.ext
  intro result
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply]
  rfl

theorem originalProposalRecord_index_loop (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (liftM ((originalProposalRecord key (.inr message) cache).map (fun record => record.index)) : SPMF Index) =
      ((selectedLoopView? <$> 𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]) >>=
        fun selected => 𝒟[completeSelectedIndex selected]) := by
  rw [originalProposalRecord_index, completedSigningRecord_index, lift_probComp_evalDist,
    bind_map_left, ← evalDist_bind]
  apply SPMF.ext
  intro index
  exact probOutput_tracedSigningIndex_eq_loop (signingBoundaryTrace key.parameter) key message cache index

def nativeSigningView {inputs : Finset HashInput} (result : Option SigningRecord × State inputs) : Option FewTimeView :=
  result.1.bind (fun record => record.1.2)

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (message : Message) (state : State inputs)

theorem lazySigning_selectedView
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    nativeSigningView <$> lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state =
      selectedLoopView? <$> 𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.memory.external.cache] := by
  let observe : Option (Option Signature × Option FewTimeView) × QueryCache HashSpec → Option FewTimeView :=
    fun result => result.1.bind Prod.snd
  calc
    _ = observe <$> (eraseSigningTrace <$> (cacheResult <$> lazyRun
        (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state)) := by
      simp only [Functor.map_map]
      congr 1
      funext result
      rcases result with ⟨record, after⟩
      cases record <;> rfl
    _ = _ := by
      rw [lazyRun_jointSigningProgram_digestLaw key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key rfl message hinputs state ha hcovered, map_bind]
      calc
        _ = UniformTableCompletion.complete state.candidates >>= fun _ =>
            selectedLoopView? <$> 𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.memory.external.cache] := by
          apply congrArg (UniformTableCompletion.complete state.candidates >>= ·)
          funext actual
          rw [evalDist_map, Functor.map_map, Functor.map_map]
          congr 1
          funext loop
          exact (digestCompletionValue_preservesMessages key state.memory.routing.known words selections actual loop).1.1
        _ = _ := by
          rw [UniformTableCompletion.complete_of_nonempty state.candidates ha, RetainedObservation.lift_bind_const]

noncomputable def completedNativeSigning : SPMF ((Option SigningRecord × State inputs) × Index) :=
  completeRecordIndex
    (lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state)
    nativeSigningView

theorem completedNativeSigning_record :
    Prod.fst <$> completedNativeSigning key inputs hencoding words publicReplies selections rows message state =
      lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state :=
  completeRecordIndex_record _ _

theorem completedNativeSigning_index
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    Prod.snd <$> completedNativeSigning key inputs hencoding words publicReplies selections rows message state =
      (liftM ((originalProposalRecord key (.inr message) state.memory.external.cache).map (fun record => record.index)) : SPMF Index) := by
  rw [completedNativeSigning, completeRecordIndex_index,
    lazySigning_selectedView key inputs hencoding words publicReplies selections rows message state hinputs ha hcovered,
    originalProposalRecord_index_loop]

end SphincsSecurity.Concrete.RetainedResidual
