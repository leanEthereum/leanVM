import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.InterleavedResidualDisclosure
import SphincsSecurity.Proof.Ots.PrefixByteRun
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

structure Memory where
  external : ExternalMemory
  routing : Routing
  log : QueryLog SigningSpec
  records : List (Message × SigningRecord)
  messageCalls : List (HashInput × HashOutput)

inductive Control (inputs : Finset HashInput) where
  | byte (routing : Routing) (input : ResidualByteFrontend.Control inputs)
  | routing
  | transcript
  | record (message : Message) (result : SigningRecord)

abbrev ControlSpec (inputs : Finset HashInput) : OracleSpec (Control inputs)
  | .byte _ input => ResidualByteFrontend.ControlSpec inputs input
  | .routing => Routing
  | .transcript => QueryLog SigningSpec
  | .record _ _ => Unit

abbrev World (inputs : Finset HashInput) := AdaptiveResidualLabels.World (ControlSpec inputs) CanonicalCoordinate inputs
abbrev State (inputs : Finset HashInput) := AdaptiveResidualLabels.State CanonicalCoordinate inputs Memory

def project {inputs : Finset HashInput} (state : State inputs) : ResidualByteFrontend.State inputs :=
  ⟨state.candidates, state.rows, state.memory.external⟩

def projectResult {Result : Type} {inputs : Finset HashInput} (result : Option Result × State inputs) :
    Option Result × ResidualByteFrontend.State inputs := (result.1, project result.2)

noncomputable def Memory.observeMessage (parameter : PublicParameter) (memory : Memory)
    (input : HashInput) (answer : HashOutput) : Memory :=
  if FtsProbeSimulation.MessageHashInput parameter input then
    { memory with messageCalls := memory.messageCalls ++ [(input, answer)] }
  else memory

noncomputable def Memory.recordSigning (memory : Memory) (message : Message) (result : SigningRecord) : Memory :=
  { memory with
    routing := memory.routing.afterSigning result
    log := memory.log ++ [⟨message, result.1.1⟩]
    records := memory.records ++ [(message, result)] }

def embed (inputs : Finset HashInput) (routing : Routing) :
    QueryImpl (ResidualByteFrontend.World inputs) (OracleComp (World inputs))
  | .inl input => liftM ((World inputs).query (.inl (.byte routing input)))
  | .inr input => liftM ((World inputs).query (.inr input))

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

noncomputable def afterControl (memory : Memory) (input : ResidualByteFrontend.Control inputs)
    (external : ExternalMemory) : Memory :=
  let after := { memory with external := external }
  match input with
  | .prepare input => match memory.external.cache input.val with
    | some answer => after.observeMessage parameter input.val answer
    | none => after
  | _ => after

noncomputable def environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs Memory where
  auxiliary state input := match input with
    | .byte routing input =>
        ((ResidualByteFrontend.prefixEnvironment parameter inputs hencoding words routing.disclosed routing.known
          publicReplies selections rows).auxiliary (project state) input).map
            (fun result => (result.1, afterControl parameter inputs state.memory input result.2))
    | .routing => PMF.pure (some state.memory.routing, state.memory)
    | .transcript => PMF.pure (some state.memory.log, state.memory)
    | .record message result => PMF.pure (some (), state.memory.recordSigning message result)
  rowAnswer memory input answer :=
    ({ memory with external := storeReply memory.external input.val answer } : Memory).observeMessage parameter input.val answer
  probeAnswer memory input _ answer :=
    ({ memory with external := storeReply memory.external input.val answer } : Memory).observeMessage parameter input.val answer
  probeStop memory _ _ := memory
  disclosure memory _ _ := memory

omit hencoding words publicReplies selections rows in
theorem observeMessage_external (memory : Memory) (input : HashInput) (answer : HashOutput) :
    (memory.observeMessage parameter input answer).external = memory.external := by
  unfold Memory.observeMessage
  split <;> rfl

omit hencoding words publicReplies selections rows in
theorem afterControl_external (memory : Memory) (input : ResidualByteFrontend.Control inputs) (external : ExternalMemory) :
    (afterControl parameter inputs memory input external).external = external := by
  cases input with
  | prepare input =>
      simp only [afterControl]
      cases memory.external.cache input.val with
      | none => rfl
      | some answer => exact observeMessage_external parameter _ _ _
  | random _ => rfl
  | account _ => rfl
  | stop => rfl

theorem observedRun_embed_query (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : (ResidualByteFrontend.World inputs).Domain) (state : State inputs) :
    projectResult <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (embed inputs routing input) state =
      ((observedImpl (ResidualByteFrontend.prefixEnvironment parameter inputs hencoding words routing.disclosed routing.known
        publicReplies selections rows) actual seed input).run).run (project state) := by
  cases input with
  | inl input =>
      simp only [embed, observedRun, runWith, simulateQ_spec_query, observedImpl, environment,
        OptionT.run_mk, StateT.run_mk, ← PMF.monad_map_eq_map, liftM_map, bind_map_left, map_bind, map_pure]
      apply congrArg (_ >>= ·)
      funext result
      rcases result with ⟨answer, external⟩
      simp only [projectResult, project, afterControl_external]
  | inr input =>
      simp only [embed, observedRun, runWith, simulateQ_spec_query]
      cases input with
      | read input =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, map_pure, projectResult, project, readState,
            environment, ResidualByteFrontend.environment, observeMessage_external]
      | probe input test =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk]
          cases hrow : state.rows input with
          | some answer =>
              simp only [project, hrow, map_pure, projectResult, readState, environment,
                ResidualByteFrontend.environment, observeMessage_external]
          | none =>
              simp only [project, hrow]
              split <;> simp only [map_pure, projectResult, project, probeState, stoppedState, environment,
                ResidualByteFrontend.environment, observeMessage_external]
      | disclose coordinate =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, map_pure, projectResult, project, disclosedState,
            environment, ResidualByteFrontend.environment]

theorem observedRun_bind {A B : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (World inputs) A) (next : A → OracleComp (World inputs) B) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (computation >>= next) state =
      (observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed computation state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer =>
          observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed (next answer) result.2)) := by
  simp only [observedRun, runWith, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem observedRun_embed {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (ResidualByteFrontend.World inputs) Result) (state : State inputs) :
    projectResult <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) computation) state =
      observedRun (ResidualByteFrontend.prefixEnvironment parameter inputs hencoding words routing.disclosed routing.known
        publicReplies selections rows) actual seed computation (project state) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, observedRun, runWith_pure, map_pure, projectResult]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, observedRun_bind, map_bind]
      conv_rhs => rw [observedRun, runWith_query_bind]
      rw [← observedRun_embed_query parameter inputs hencoding words publicReplies selections rows routing actual seed input state]
      simp only [bind_map_left]
      apply congrArg (_ >>= ·)
      funext result
      rcases result with ⟨answer, after⟩
      cases answer with
      | none => simp only [Option.elim_none, map_pure, projectResult]
      | some answer => exact ih answer after

end SphincsSecurity.Concrete.RetainedResidual
