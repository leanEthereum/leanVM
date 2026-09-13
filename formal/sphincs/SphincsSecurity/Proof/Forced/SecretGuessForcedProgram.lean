import SphincsSecurity.Proof.Forced.SecretGuessForced
import SphincsSecurity.Proof.Forced.SecretGuessErasure
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value AuxIndex TargetIndex : Type} {auxSpec : OracleSpec AuxIndex}
  {targetSpec : OracleSpec TargetIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def plainAfterTrial (state : State Coordinate Value PUnit)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) : State Coordinate Value PUnit :=
  { allowed := restrict state.allowed coordinate candidate hit
    retired := if hit then insert coordinate state.retired else state.retired
    guesses := if hit = true ∧ coordinate ∉ state.retired then insert coordinate state.guesses else state.guesses
    probes := state.probes + 1
    memory := PUnit.unit }

def plainAfterDisclosure (state : State Coordinate Value PUnit)
    (coordinate : Coordinate) (value : Value) : State Coordinate Value PUnit :=
  { state with
    allowed := discloseTableValue state.allowed coordinate value
    retired := insert coordinate state.retired
    memory := PUnit.unit }

noncomputable def forcedProgram {Result : Type}
    (auxiliary : QueryImpl auxSpec (OracleComp targetSpec))
    (sampleBool : SPMF Bool → OracleComp targetSpec Bool)
    (sampleValue : SPMF Value → OracleComp targetSpec Value) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) :
    State Coordinate Value PUnit → OracleComp targetSpec (Result × State Coordinate Value PUnit) :=
  OracleComp.construct (fun value state => pure (value, state)) (fun input _ next state =>
    match input with
    | .inl input => auxiliary input >>= fun answer => next answer state
    | .inr (.inl (coordinate, candidate)) =>
        sampleBool (forcedTrial slot state coordinate candidate) >>= fun hit =>
          next hit (plainAfterTrial state coordinate candidate hit)
    | .inr (.inr coordinate) => sampleValue (cell (state.allowed coordinate)) >>= fun value =>
        next value (plainAfterDisclosure state coordinate value)) computation

theorem forcedProgram_pure {Result : Type} (auxiliary : QueryImpl auxSpec (OracleComp targetSpec))
    (sampleBool : SPMF Bool → OracleComp targetSpec Bool)
    (sampleValue : SPMF Value → OracleComp targetSpec Value) (slot : Nat)
    (value : Result) (state : State Coordinate Value PUnit) :
    forcedProgram auxiliary sampleBool sampleValue slot (pure value) state = pure (value, state) := rfl

theorem forcedProgram_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec (OracleComp targetSpec))
    (sampleBool : SPMF Bool → OracleComp targetSpec Bool)
    (sampleValue : SPMF Value → OracleComp targetSpec Value) (slot : Nat)
    (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value PUnit) :
    forcedProgram auxiliary sampleBool sampleValue slot
      (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      match input with
      | .inl input => auxiliary input >>= fun answer => forcedProgram auxiliary sampleBool sampleValue slot (next answer) state
      | .inr (.inl (coordinate, candidate)) =>
          sampleBool (forcedTrial slot state coordinate candidate) >>= fun hit =>
            forcedProgram auxiliary sampleBool sampleValue slot (next hit) (plainAfterTrial state coordinate candidate hit)
      | .inr (.inr coordinate) => sampleValue (cell (state.allowed coordinate)) >>= fun value =>
          forcedProgram auxiliary sampleBool sampleValue slot (next value) (plainAfterDisclosure state coordinate value) := by
  rw [forcedProgram, OracleComp.construct_query_bind]
  cases input with
  | inl input => rfl
  | inr input => cases input <;> rfl

theorem simulateQ_forcedProgram {Result : Type} (auxiliary : QueryImpl auxSpec ProbComp)
    (program : QueryImpl auxSpec (OracleComp targetSpec))
    (sampleBool : SPMF Bool → OracleComp targetSpec Bool)
    (sampleValue : SPMF Value → OracleComp targetSpec Value)
    (runtime : QueryImpl targetSpec SPMF)
    (hauxiliary : ∀ input, simulateQ runtime (program input) = 𝒟[auxiliary input])
    (hbool : ∀ law, simulateQ runtime (sampleBool law) = law)
    (hvalue : ∀ law, simulateQ runtime (sampleValue law) = law)
    (slot : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value PUnit) :
    simulateQ runtime (forcedProgram program sampleBool sampleValue slot computation state) =
      forcedRun (environment auxiliary) slot computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [forcedProgram_pure, simulateQ_pure, forcedRun, runWith_pure]
  | query_bind input next ih =>
      rw [forcedProgram_query_bind, forcedRun, runWith_query_bind]
      cases input with
      | inl input =>
          simp only [simulateQ_bind, hauxiliary, forcedImpl, lazyImpl, StateT.run_mk,
            environment, evalDist_map, Functor.map_map, bind_map_left]
          apply congrArg (𝒟[auxiliary input] >>= ·)
          funext answer
          exact ih answer state
      | inr input =>
          cases input with
          | inl probe =>
              rcases probe with ⟨coordinate, candidate⟩
              simp only [simulateQ_bind, hbool, forcedImpl, StateT.run_mk, bind_map_left]
              apply congrArg (forcedTrial slot state coordinate candidate >>= ·)
              funext hit
              exact ih hit (plainAfterTrial state coordinate candidate hit)
          | inr coordinate =>
              simp only [simulateQ_bind, hvalue, forcedImpl, lazyImpl, StateT.run_mk, bind_map_left]
              apply congrArg (cell (state.allowed coordinate) >>= ·)
              funext value
              exact ih value (plainAfterDisclosure state coordinate value)

end SphincsSecurity.Concrete.SecretGuessObservation
