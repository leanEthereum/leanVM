import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.UniformTableObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value AuxIndex : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
  {auxSpec : OracleSpec AuxIndex}

abbrev TableSpec (Coordinate Value : Type) := Coordinate →ₒ Value

noncomputable def observedImpl (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value) :
    QueryImpl (auxSpec + TableSpec Coordinate Value) (StateT (Coordinate → Finset Value) SPMF)
  | .inl input => StateT.mk fun allowed => (fun answer => (answer, allowed)) <$> auxiliary input
  | .inr coordinate => StateT.mk fun allowed =>
      pure (table coordinate, discloseTableValue allowed coordinate (table coordinate))

noncomputable def lazyImpl (auxiliary : QueryImpl auxSpec SPMF) :
    QueryImpl (auxSpec + TableSpec Coordinate Value) (StateT (Coordinate → Finset Value) SPMF)
  | .inl input => StateT.mk fun allowed => (fun answer => (answer, allowed)) <$> auxiliary input
  | .inr coordinate => StateT.mk fun allowed =>
      (fun answer => (answer, discloseTableValue allowed coordinate answer)) <$> cell (allowed coordinate)

noncomputable def observedRun {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    SPMF (Result × (Coordinate → Finset Value)) :=
  (simulateQ (observedImpl auxiliary table) computation).run allowed

noncomputable def lazyRun {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    SPMF (Result × (Coordinate → Finset Value)) :=
  (simulateQ (lazyImpl auxiliary) computation).run allowed

omit [Fintype Coordinate] [DecidableEq Value] in
theorem observedRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (result : Result) (allowed : Coordinate → Finset Value) :
    observedRun auxiliary table (pure result) allowed = pure (result, allowed) := by
  simp only [observedRun, simulateQ_pure, StateT.run_pure]

omit [Fintype Coordinate] [DecidableEq Value] in
theorem lazyRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (result : Result) (allowed : Coordinate → Finset Value) :
    lazyRun auxiliary (pure result) allowed = pure (result, allowed) := by
  simp only [lazyRun, simulateQ_pure, StateT.run_pure]

omit [Fintype Coordinate] [DecidableEq Value] in
theorem observedRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (input : (auxSpec + TableSpec Coordinate Value).Domain)
    (next : (auxSpec + TableSpec Coordinate Value).Range input → OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) :
    observedRun auxiliary table (liftM ((auxSpec + TableSpec Coordinate Value).query input) >>= next) allowed =
      ((observedImpl auxiliary table input).run allowed >>= fun result =>
        observedRun auxiliary table (next result.1) result.2) := by
  simp only [observedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

omit [Fintype Coordinate] [DecidableEq Value] in
theorem lazyRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (input : (auxSpec + TableSpec Coordinate Value).Domain)
    (next : (auxSpec + TableSpec Coordinate Value).Range input → OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) :
    lazyRun auxiliary (liftM ((auxSpec + TableSpec Coordinate Value).query input) >>= next) allowed =
      ((lazyImpl auxiliary input).run allowed >>= fun result => lazyRun auxiliary (next result.1) result.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem run_posterior {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    (complete allowed >>= fun table =>
      (fun result => (table, result)) <$> observedRun auxiliary table computation allowed) =
        (lazyRun auxiliary computation allowed >>= fun result =>
          (fun table => (table, result)) <$> complete result.2) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure result => simp only [observedRun_pure, lazyRun_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, bind_map_left, map_bind, bind_assoc]
          rw [RetainedObservation.bind_comm]
          exact congrArg (fun continuation => auxiliary input >>= continuation)
            (funext fun answer => ih answer allowed)
      | inr coordinate =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
          rw [bind_disclose allowed coordinate (fun answer table =>
            (fun result => (table, result)) <$>
              observedRun auxiliary table (next answer) (discloseTableValue allowed coordinate answer))]
          exact congrArg (fun continuation => cell (allowed coordinate) >>= continuation)
            (funext fun answer => ih answer (discloseTableValue allowed coordinate answer))

end SphincsSecurity.Concrete.UniformTableObservation
