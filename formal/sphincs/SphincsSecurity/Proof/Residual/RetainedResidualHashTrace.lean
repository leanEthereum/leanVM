import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageByteTrace
import SphincsSecurity.Proof.Residual.RetainedResidualExecution
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def Memory.afterReply (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) : Memory :=
  answer.elim { memory with external := external }
    (fun answer => ({ memory with external := external } : Memory).observeMessage parameter input answer)

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem freshPrefix_message (routing : Routing) (input : inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input.val) :
    freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input = .read input := by
  have hdecode : decodePosition parameter input.val = none := by
    obtain ⟨payload, heq⟩ := hmessage
    rw [← heq]
    exact decodePosition_message parameter payload
  have hrow : knownEncodingRowAt parameter inputs hencoding routing.known input = none := by
    apply (knownEncodingRowAt_none parameter inputs hencoding routing.known input).mpr
    rintro ⟨row, hrow⟩
    apply ResidualByteFrontend.message_not_encoding parameter input.val hmessage row.1
    rw [← hrow]
    exact ⟨_, rfl⟩
  simp only [freshPrefix, route, hdecode, Option.elim_none, hrow]

noncomputable def executeResult (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) :
    Action inputs → Option HashOutput × State inputs
  | .known answer => (some answer, state)
  | .read input => (some (seed input), readState (environment parameter inputs hencoding words publicReplies selections rows) state input (seed input))
  | .probe input test =>
      match state.rows input with
      | some answer => (some answer, readState (environment parameter inputs hencoding words publicReplies selections rows) state input answer)
      | none => if test.keep actual (seed input) then
          (some (seed input), probeState (environment parameter inputs hencoding words publicReplies selections rows) state input test (seed input))
        else (none, stoppedState (environment parameter inputs hencoding words publicReplies selections rows) state input test)

theorem observedRun_execute (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) (action : Action inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.execute action)) state =
      pure (executeResult parameter inputs hencoding words publicReplies selections rows actual seed state action) := by
  cases action with
  | known answer => simp only [ResidualByteFrontend.execute, simulateQ_pure, observedRun, runWith_pure, executeResult]
  | read input =>
      simp only [ResidualByteFrontend.execute, simulateQ_spec_query, embed, observedRun, runWith, simulateQ_spec_query,
        observedImpl, OptionT.run_mk, StateT.run_mk, executeResult]
  | probe input test =>
      simp only [ResidualByteFrontend.execute, simulateQ_spec_query, embed, observedRun, runWith, simulateQ_spec_query,
        observedImpl, OptionT.run_mk, StateT.run_mk, executeResult]
      dsimp only [OracleSpec.Range, World, AdaptiveResidualLabels.World, OracleSpec.add_apply_inr, ResidualSpec]
      cases hrow : state.rows input with
      | some answer => rfl
      | none => by_cases hkeep : test.keep actual (seed input) <;> simp only [hkeep, if_true, if_false]

noncomputable def prepareState (routing : Routing) (input : inputs) (state : State inputs) : Action inputs × State inputs :=
  let prepared := ResidualByteFrontend.prepare parameter inputs words routing.disclosed routing.known
    (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows) input state.memory.external
  (prepared.1, { state with memory := afterControl parameter inputs state.memory (.prepare input) prepared.2 })

theorem observedRun_prepare_bind {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (next : Action inputs → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (embed inputs routing (.inl (.prepare input)) >>= next) state =
      let prepared := prepareState parameter inputs hencoding words publicReplies selections rows routing input state
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed (next prepared.1) prepared.2 := by
  rw [embed, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
    PMF.pure_map, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun, prepareState, project]

noncomputable def hashResult (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    Option HashOutput × State inputs :=
  let prepared := prepareState parameter inputs hencoding words publicReplies selections rows routing input state
  executeResult parameter inputs hencoding words publicReplies selections rows actual seed prepared.2 prepared.1

theorem observedRun_hashQuery (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.hashQuery input)) state =
      pure (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state) := by
  rw [ResidualByteFrontend.hashQuery, simulateQ_bind, simulateQ_spec_query, observedRun_prepare_bind, observedRun_execute]
  rfl

theorem hashResult_memory (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    let result := hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state
    result.2.memory = state.memory.afterReply parameter input.val result.1 result.2.memory.external := by
  dsimp only
  cases hcache : state.memory.external.cache input.val with
  | some answer =>
      simp only [hashResult, prepareState, ResidualByteFrontend.prepare, hcache, afterControl, executeResult,
        Memory.afterReply, Option.elim_some, observeMessage_external]
  | none =>
      have hlocal := freshPrefix_local parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input
      cases haction : freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input with
      | known answer =>
          have hnot : ¬FtsProbeSimulation.MessageHashInput parameter input.val := by
            intro hmessage
            have h := freshPrefix_message parameter inputs hencoding words publicReplies selections rows routing input hmessage
            rw [haction] at h
            cases h
          simp only [hashResult, prepareState, ResidualByteFrontend.prepare, hcache, haction, afterControl, executeResult,
            Memory.afterReply, Option.elim_some, Memory.observeMessage, if_neg hnot]
      | read row =>
          have heq : row = input := by simpa only [haction, Local] using hlocal
          subst row
          simp only [hashResult, prepareState, ResidualByteFrontend.prepare, hcache, haction, afterControl, executeResult,
            Memory.afterReply, Option.elim_some, readState, environment, observeMessage_external]
      | probe row test =>
          have heq : row = input := by simpa only [haction, Local] using hlocal
          subst row
          simp only [hashResult, prepareState, ResidualByteFrontend.prepare, hcache, haction, afterControl, executeResult]
          cases hrow : state.rows input with
          | some answer =>
              simp only [Memory.afterReply, Option.elim_some, readState, environment, observeMessage_external]
          | none =>
              by_cases hkeep : test.keep actual (seed input) <;>
                simp only [hkeep, if_true, if_false, Memory.afterReply, Option.elim_some, Option.elim_none, probeState, stoppedState,
                environment, observeMessage_external]

end SphincsSecurity.Concrete.RetainedResidual
