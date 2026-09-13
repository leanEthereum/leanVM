import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCandidates
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredErasure
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem jointDisclosureSequenceState_candidate {inputs : Finset HashInput}
    (environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory)
    (actual : Labels) {n : Nat} (coordinates : Fin n → CanonicalCoordinate) (state : State inputs)
    (coordinate : CanonicalCoordinate) (hne : ∀ index, coordinate ≠ coordinates index) :
    (jointDisclosureSequenceState environment actual coordinates state).candidates coordinate = state.candidates coordinate := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [jointDisclosureSequenceState, List.ofFn_succ, List.foldl_cons]
      change (jointDisclosureSequenceState environment actual (fun index => coordinates index.succ)
        (disclosedState environment state (coordinates 0) (actual (coordinates 0)))).candidates coordinate = _
      rw [ih (coordinates := fun index => coordinates index.succ) (hne := fun index => hne index.succ)]
      exact Function.update_of_ne (hne 0) _ _

theorem hiddenCandidateBound_disclose {inputs : Finset HashInput} (words : OtsReferenceWords) (routing : Routing)
    (view : FewTimeView) (secrets : FtsTree → Digest) (state : State inputs)
    (hbound : HiddenCandidateBound words routing.disclosed state) :
    HiddenCandidateBound words (routing.disclose view secrets).disclosed state := by
  intro coordinate hhidden
  apply hbound coordinate
  cases coordinate with
  | otsStart _ _ _ _ => exact hhidden
  | ftsStart index tree leaf => exact fun h => hhidden (Or.inl h)
  | graph position =>
      rw [InterleavedResidual.hidden_graph_disclosed words routing.disclosed (routing.disclose view secrets).disclosed position]
      exact hhidden

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (routing : Routing) (actions : inputs → ResidualByteAction.Action inputs)

theorem completedWork_hiddenCandidateBound (actual : Labels) (work : PublicSigningRecord × Nat)
    (state : State inputs) (hbound : HiddenCandidateBound words routing.disclosed state) :
    HiddenCandidateBound words
      (routing.afterSigning (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1)).disclosed
      (jointCompletedSigningState (environment parameter inputs words routing.disclosed routing.known actions) actual work.1
        { state with memory := accountWork state.memory work.2 }) := by
  obtain ⟨⟨⟨plan, view⟩, trace⟩, cost⟩ := work
  cases plan <;> cases view <;>
    simp only [jointCompletedSigningState, completePublicSigningRecord, Option.map_none, Option.map_some, Routing.afterSigning]
  all_goals try exact hbound
  rename_i plan view
  intro coordinate hhidden
  have hbefore := hiddenCandidateBound_disclose words routing view (fun tree => actual (.ftsStart view.1 tree (view.2 tree))) state hbound
    coordinate hhidden
  have hne : ∀ tree, coordinate ≠ .ftsStart view.1 tree (view.2 tree) := by
    intro tree heq
    subst coordinate
    exact hhidden (Or.inr ⟨rfl, rfl⟩)
  change 2 ^ digestBits ≤ _
  rw [jointDisclosureSequenceState_candidate _ actual _ _ coordinate hne,
    jointDisclosureSequenceState_memory]
  exact hbefore

end SphincsSecurity.Concrete.ResidualByteFrontend

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem observedRun_completeWork_hiddenCandidateBound (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (work : PublicSigningRecord × Nat) (state : State inputs)
    (hbound : HiddenCandidateBound words routing.disclosed (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ HiddenCandidateBound words (routing.afterSigning record).disclosed (project result.2) := by
  have hproject := map_nonzero _ projectResult result hresult
  rw [observedRun_embed, ResidualByteFrontend.observedRun_jointCompleteSigningWork] at hproject
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hproject
  refine ⟨completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1,
    congrArg Prod.fst hproject, ?_⟩
  rw [show project result.2 = _ from congrArg Prod.snd hproject]
  exact ResidualByteFrontend.completedWork_hiddenCandidateBound parameter inputs words routing _ actual work (project state) hbound

theorem lazyRun_completeWork_hiddenCandidateBound (routing : Routing) (work : PublicSigningRecord × Nat) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hbound : HiddenCandidateBound words routing.disclosed (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ HiddenCandidateBound words (routing.afterSigning record).disclosed (project result.2) := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact observedRun_completeWork_hiddenCandidateBound parameter inputs hencoding words publicReplies selections rows routing actual seed
    work state hbound result hresult

theorem lazyRun_jointSigningProgram_hiddenCandidateBound (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message) ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words routing.disclosed (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ HiddenCandidateBound words (routing.afterSigning record).disclosed (project result.2) := by
  rw [ResidualByteFrontend.jointSigningProgram, simulateQ_bind, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨middle, hmiddle, hresult⟩ := hresult
  rw [← lazyByteRun] at hmiddle
  obtain ⟨⟨work, hwork⟩, hcandidates⟩ := lazyByteRun_message_support parameter inputs hencoding words publicReplies selections rows
    routing _ hinputs (ResidualByteFrontend.publicSigningWork_messageOnly parameter root routing.known words selections message)
    state hcovered middle hmiddle
  have hmiddleBound := lazyByteRun_hiddenCandidateBound parameter inputs hencoding words publicReplies selections rows
    routing _ hinputs state ha hbound middle hmiddle
  have hmiddleNonempty : ∀ coordinate, (middle.2.candidates coordinate).Nonempty := by rw [hcandidates]; exact ha
  rw [hwork, Option.elim_some] at hresult
  exact lazyRun_completeWork_hiddenCandidateBound parameter inputs hencoding words publicReplies selections rows routing work middle.2
    hmiddleNonempty hmiddleBound result hresult

theorem lazyRun_embed_routing {Result : Type} (routing : Routing)
    (computation : OracleComp (ResidualByteFrontend.World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option Result × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) computation) state result ≠ 0) :
    result.2.memory.routing = state.memory.routing := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact congrArg Prod.fst (observedRun_embed_history parameter inputs hencoding words publicReplies selections rows routing actual seed
    computation state result hresult)

omit parameter hencoding in
theorem lazyRun_signingProgram_hiddenCandidateBound (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (result : Option (Option Signature) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) := by
  rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  have hwork := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key state.memory.routing.known words selections message).trans hinputs
  obtain ⟨record, hrecord, hafter⟩ := lazyRun_jointSigningProgram_hiddenCandidateBound key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message hwork state ha hcovered hbound raw hraw
  have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing _ state ha raw hraw
  simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  change HiddenCandidateBound words (raw.2.memory.routing.afterSigning record).disclosed (project raw.2)
  rw [hrouting]
  exact hafter

end SphincsSecurity.Concrete.RetainedResidual
