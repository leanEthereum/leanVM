import SphincsSecurity.Proof.Chains.AdaptiveChainCheckpoint
import SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result Output : Type}

omit [Fintype State] [Nonempty State] in
theorem observedRun_bind (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (before >>= after) observed =
      (observedRun auxiliary tables before observed).bind (fun middle => observedRun auxiliary tables (after middle.1) middle.2) := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]

omit [Fintype State] [Nonempty State] in
theorem checkpointObservedRun_project (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : Checkpoint → Result → Output) :
    (checkpointObservedRun auxiliary tables before (fun middle => after middle.1) observed).map
      (fun result => (project result.1.1 result.2.1.1, result.2.2)) =
    observedRun auxiliary tables (do let middle ← before; let result ← after middle; pure (project middle result)) observed := by
  simp only [checkpointObservedRun, PMF.map_bind, PMF.map_comp, Function.comp_def,
    observedRun_bind, bind_pure_comp, observedRun_map]
  apply congrArg (observedRun auxiliary tables before observed).bind
  funext middle
  rw [← observedRun_map auxiliary tables (QueryCap.counted IsPrefixQuery (after middle.1))
    (fun result => project middle.1 result.1) middle.2]
  rw [← Functor.map_map, QueryCap.counted_forget, observedRun_map]

theorem realCheckpointRun_project (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : State → Checkpoint → Result → Output) :
    (realCheckpointRun auxiliary before (fun endpoint middle => after endpoint middle.1) observed).map
      (fun result => (result.1, project result.1 result.2.1.1 result.2.2.1.1, result.2.2.2)) =
    realRun auxiliary (fun endpoint => do
      let middle ← before endpoint
      let result ← after endpoint middle
      pure (project endpoint middle result)) observed := by
  simp only [realCheckpointRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (fun law => law.map (fun result => (pair.2, result)))
    (checkpointObservedRun_project (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed (project pair.2))
  simpa only [PMF.map_comp, Function.comp_def] using h

end SphincsSecurity.Concrete.PartialChainEndpoint
