import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualProbeCompletion
namespace SphincsSecurity.Concrete.AdaptiveResidualLabels

open _root_.OracleComp OracleSpec HiddenLabelObservation UniformTableCompletion RetainedObservation ResidualTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

inductive Request (Coordinate Cell : Type) where
  | read (cell : Cell)
  | probe (cell : Cell) (test : Probe Coordinate)
  | disclose (coordinate : Coordinate)

abbrev ResidualSpec (Coordinate Cell : Type) : OracleSpec (Request Coordinate Cell)
  | .read _ => HashOutput
  | .probe _ _ => HashOutput
  | .disclose _ => Digest

abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Cell : Type) :=
  auxSpec + ResidualSpec Coordinate Cell

structure State (Coordinate Cell Memory : Type) where
  candidates : Coordinate → Finset Digest
  rows : Cache Cell
  memory : Memory

structure Environment {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Cell Memory : Type) where
  auxiliary : State Coordinate Cell Memory → (input : auxSpec.Domain) → PMF (Option (auxSpec.Range input) × Memory)
  rowAnswer : Memory → Cell → HashOutput → Memory
  probeAnswer : Memory → Cell → Probe Coordinate → HashOutput → Memory
  probeStop : Memory → Cell → Probe Coordinate → Memory
  disclosure : Memory → Coordinate → Digest → Memory

variable {Coordinate Cell Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell]

def readState (environment : Environment auxSpec Coordinate Cell Memory) (state : State Coordinate Cell Memory)
    (input : Cell) (answer : HashOutput) : State Coordinate Cell Memory :=
  ⟨state.candidates, Function.update state.rows input (some answer), environment.rowAnswer state.memory input answer⟩

def probeState (environment : Environment auxSpec Coordinate Cell Memory) (state : State Coordinate Cell Memory)
    (input : Cell) (test : Probe Coordinate) (answer : HashOutput) : State Coordinate Cell Memory :=
  ⟨test.restrict state.candidates answer, Function.update state.rows input (some answer),
    environment.probeAnswer state.memory input test answer⟩

def stoppedState (environment : Environment auxSpec Coordinate Cell Memory) (state : State Coordinate Cell Memory)
    (input : Cell) (test : Probe Coordinate) : State Coordinate Cell Memory :=
  { state with memory := environment.probeStop state.memory input test }

def disclosedState (environment : Environment auxSpec Coordinate Cell Memory) (state : State Coordinate Cell Memory)
    (coordinate : Coordinate) (value : Digest) : State Coordinate Cell Memory :=
  ⟨discloseTableValue state.candidates coordinate value, state.rows,
    environment.disclosure state.memory coordinate value⟩

noncomputable def observedImpl (environment : Environment auxSpec Coordinate Cell Memory)
    (labels : Coordinate → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coordinate Cell) (OptionT (StateT (State Coordinate Cell Memory) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (environment.auxiliary state input) : SPMF _) >>= fun result =>
        pure (result.1, { state with memory := result.2 })
  | .inr (.read input) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table input), readState environment state input (table input))
  | .inr (.probe input test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows input with
      | some answer => pure (some answer, readState environment state input answer)
      | none => if test.keep labels (table input) then
          pure (some (table input), probeState environment state input test (table input))
        else pure (none, stoppedState environment state input test)
  | .inr (.disclose coordinate) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coordinate), disclosedState environment state coordinate (labels coordinate))

noncomputable def lazyImpl (environment : Environment auxSpec Coordinate Cell Memory) :
    QueryImpl (World auxSpec Coordinate Cell) (OptionT (StateT (State Coordinate Cell Memory) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (environment.auxiliary state input) : SPMF _) >>= fun result =>
        pure (result.1, { state with memory := result.2 })
  | .inr (.read input) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows input >>= fun answer => pure (some answer, readState environment state input answer)
  | .inr (.probe input test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows input with
      | some answer => pure (some answer, readState environment state input answer)
      | none => observe (lazyResponse state.candidates test)
          (pure (none, stoppedState environment state input test))
          (fun answer => pure (some answer, probeState environment state input test answer))
  | .inr (.disclose coordinate) => OptionT.mk <| StateT.mk fun state =>
      cell (state.candidates coordinate) >>= fun value =>
        pure (some value, disclosedState environment state coordinate value)

noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Cell) (OptionT (StateT (State Coordinate Cell Memory) SPMF)))
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory) :
    SPMF (Option Result × State Coordinate Cell Memory) :=
  (OptionT.run (simulateQ implementation computation)).run state

noncomputable def observedRun {Result : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (labels : Coordinate → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory) :=
  runWith (observedImpl environment labels table) computation state

noncomputable def lazyRun {Result : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory) :=
  runWith (lazyImpl environment) computation state

omit [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Cell) (OptionT (StateT (State Coordinate Cell Memory) SPMF)))
    (value : Result) (state : State Coordinate Cell Memory) : runWith implementation (pure value) state = pure (some value, state) := by
  simp only [runWith, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

omit [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Cell) (OptionT (StateT (State Coordinate Cell Memory) SPMF)))
    (input : (World auxSpec Coordinate Cell).Domain)
    (next : (World auxSpec Coordinate Cell).Range input → OracleComp (World auxSpec Coordinate Cell) Result)
    (state : State Coordinate Cell Memory) :
    runWith implementation (liftM ((World auxSpec Coordinate Cell).query input) >>= next) state =
      ((implementation input).run.run state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => runWith implementation (next answer) result.2)) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (implementation input).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl

def retain {Result : Type} (labels : Coordinate → Digest) (table : Cell → HashOutput)
    (result : Option Result × State Coordinate Cell Memory) :
    Option ((Coordinate → Digest) × (Cell → HashOutput) × Result) × State Coordinate Cell Memory :=
  (result.1.map (fun value => (labels, table, value)), result.2)

noncomputable def finish {Result : Type} (result : Option Result × State Coordinate Cell Memory) :
    SPMF (Option ((Coordinate → Digest) × (Cell → HashOutput) × Result) × State Coordinate Cell Memory) :=
  match result.1 with
  | none => pure (none, result.2)
  | some value => complete result.2.candidates >>= fun labels =>
      completeRows result.2.rows >>= fun table => pure (some (labels, table, value), result.2)

private theorem bind_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (next : A → SPMF B) :
    ((if p then left else right) >>= next) = if p then left >>= next else right >>= next := by
  split <;> rfl

private theorem map_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (f : A → B) :
    f <$> (if p then left else right) = if p then f <$> left else f <$> right := by
  split <;> rfl

theorem run_posterior {Result : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (complete state.candidates >>= fun labels => completeRows state.rows >>= fun table =>
      retain labels table <$> observedRun environment labels table computation state) =
        (lazyRun environment computation state >>= finish) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [observedRun, lazyRun, runWith_pure, map_pure, pure_bind, retain, Option.map_some, finish]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
            StateT.run_mk, bind_assoc, pure_bind, map_bind]
          conv_lhs => enter [2, labels]; rw [RetainedObservation.bind_comm]
          rw [RetainedObservation.bind_comm]
          apply congrArg ((liftM (environment.auxiliary state input) : SPMF _) >>= ·)
          funext result
          rcases result with ⟨answer, memory⟩
          cases answer with
          | none =>
              simp only [map_pure, retain, Option.map_none, pure_bind, Option.elim_none, finish, completeRows_bind_const]
              rw [complete_of_nonempty _ ha, lift_bind_const]
          | some answer => exact ih answer { state with memory := memory } ha
      | inr input =>
          cases input with
          | read input =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              have hread (labels : Coordinate → Digest) := bind_read state.rows input
                (fun answer table => retain labels table <$>
                  runWith (observedImpl environment labels table) (next answer) (readState environment state input answer))
              simp_rw [hread]
              rw [RetainedObservation.bind_comm]
              apply congrArg (reply state.rows input >>= ·)
              funext answer
              exact ih answer (readState environment state input answer) ha
          | probe input test =>
              cases hcache : state.rows input with
              | some answer =>
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, pure_bind, Option.elim_some]
                  have hrows : Function.update state.rows input (some answer) = state.rows := by
                    rw [← hcache, Function.update_eq_self]
                  simpa only [readState, hrows, observedRun, lazyRun] using ih answer (readState environment state input answer) ha
              | none =>
                  change HashOutput → OracleComp (World auxSpec Coordinate Cell) Result at next
                  dsimp only [OracleSpec.Range, World, ResidualSpec] at ih ⊢
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, observe_bind, pure_bind, Option.elim_none, Option.elim_some, finish]
                  dsimp only [OracleSpec.Range, World, OracleSpec.add_apply_inr, ResidualSpec]
                  simp only [bind_if, pure_bind, Option.elim_none, Option.elim_some, map_if, map_pure, retain, Option.map_none]
                  rw [ResidualProbeCompletion.bind_fresh_probe state.candidates ha state.rows input hcache test
                    (pure (none, stoppedState environment state input test))
                    (fun answer labels table => retain labels table <$>
                      runWith (observedImpl environment labels table) (next answer) (probeState environment state input test answer))]
                  apply observe_congr
                  intro answer hanswer
                  exact ih answer (probeState environment state input test answer)
                    (lazyResponse_nonempty state.candidates test answer hanswer)
          | disclose coordinate =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              rw [bind_disclose state.candidates coordinate (fun value labels => completeRows state.rows >>= fun table =>
                retain labels table <$> runWith (observedImpl environment labels table) (next value)
                  (disclosedState environment state coordinate value))]
              apply congrArg (cell (state.candidates coordinate) >>= ·)
              funext value
              exact ih value (disclosedState environment state coordinate value)
                (discloseTableValue_nonempty state.candidates ha coordinate value)

end SphincsSecurity.Concrete.AdaptiveResidualLabels
