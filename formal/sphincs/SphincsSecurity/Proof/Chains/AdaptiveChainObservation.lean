import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.PartialChainObservation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}

abbrev PrefixSpec (n : Nat) (State : Type) := (Fin n × State) →ₒ State

noncomputable def observedImpl (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State) :
    QueryImpl (auxSpec + PrefixSpec n State) (StateT (Fin n → State → Option State) PMF)
  | .inl input => StateT.mk fun observed => (auxiliary input).map (fun answer => (answer, observed))
  | .inr query => StateT.mk fun observed =>
      PMF.pure (tables query.1 query.2, record observed query (tables query.1 query.2))

noncomputable def lazyImpl (auxiliary : QueryImpl auxSpec PMF) :
    QueryImpl (auxSpec + PrefixSpec n State) (StateT (Fin n → State → Option State) PMF)
  | .inl input => StateT.mk fun observed => (auxiliary input).map (fun answer => (answer, observed))
  | .inr query => StateT.mk fun observed =>
      (rowLaw (observed query.1 query.2)).map (fun answer => (answer, record observed query answer))

noncomputable def observedRun {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    PMF (Result × (Fin n → State → Option State)) :=
  (simulateQ (observedImpl auxiliary tables) computation).run observed

noncomputable def lazyRun {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    PMF (Result × (Fin n → State → Option State)) :=
  (simulateQ (lazyImpl auxiliary) computation).run observed

omit [Fintype State] [Nonempty State] in
theorem observedRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (result : Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (pure result) observed = PMF.pure (result, observed) := by
  simp only [observedRun, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure]

theorem lazyRun_pure {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (result : Result) (observed : Fin n → State → Option State) :
    lazyRun auxiliary (pure result) observed = PMF.pure (result, observed) := by
  simp only [lazyRun, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure]

omit [Fintype State] [Nonempty State] in
theorem observedRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (input : (auxSpec + PrefixSpec n State).Domain)
    (next : (auxSpec + PrefixSpec n State).Range input → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (liftM ((auxSpec + PrefixSpec n State).query input) >>= next) observed =
      ((observedImpl auxiliary tables input).run observed).bind
        (fun result => observedRun auxiliary tables (next result.1) result.2) := by
  simp only [observedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind]

theorem lazyRun_query_bind {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (input : (auxSpec + PrefixSpec n State).Domain)
    (next : (auxSpec + PrefixSpec n State).Range input → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    lazyRun auxiliary (liftM ((auxSpec + PrefixSpec n State).query input) >>= next) observed =
      ((lazyImpl auxiliary input).run observed).bind (fun result => lazyRun auxiliary (next result.1) result.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind]

theorem run_posterior {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (completeTables observed).bind (fun tables =>
      (observedRun auxiliary tables computation observed).map (fun result => (tables, result))) =
        (lazyRun auxiliary computation observed).bind (fun result =>
          (completeTables result.2).map (fun tables => (tables, result))) := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result =>
      simp only [observedRun_pure, lazyRun_pure, PMF.pure_bind, PMF.map, PMF.pure_bind]
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, PMF.bind_map, PMF.map_bind, PMF.bind_bind]
          rw [PMF.bind_comm]
          exact congrArg (fun continuation => (auxiliary input).bind continuation)
            (funext fun answer => ih answer observed)
      | inr query =>
          simp only [observedRun_query_bind, lazyRun_query_bind, observedImpl, lazyImpl,
            StateT.run_mk, PMF.pure_bind, PMF.bind_map, PMF.bind_bind]
          rw [completeTables_bind_observe observed query (fun answer tables =>
            (observedRun auxiliary tables (next answer) (record observed query answer)).map
              (fun result => (tables, result)))]
          exact congrArg (fun continuation => (rowLaw (observed query.1 query.2)).bind continuation)
            (funext fun answer => ih answer (record observed query answer))

end SphincsSecurity.Concrete.PartialChainEndpoint
