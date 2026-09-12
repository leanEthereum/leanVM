import SphincsSecurity.Proof.Reference.ReferenceContactGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

abbrev FrontierStop := PublicParameter → OtsReferenceWords → OtsFrontierValues → OtsContactTrace.Trace → Prop

variable (stop : FrontierStop) [∀ parameter words frontier, DecidablePred (stop parameter words frontier)]

noncomputable def checkpointSplitRun {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (computation : OracleComp OracleWorld Result) :
    OracleComp OracleWorld (OtsContactTrace.Trace × (Result × OtsContactTrace.Trace)) := do
  let middle ← QueryPause.run (stop parameter words frontier)
    (fun input answer history => history * hashObservationTrace input answer) computation 1
  let tail ← QueryPause.traced hashObservationTrace middle.2
  pure (middle.1, tail)

noncomputable def checkpointObserver : FrontierObserver ContactResult := fun parameter words frontier computation =>
  (fun result => ⟨frontier, result.1, result.2.1, result.2.2⟩) <$>
    checkpointSplitRun stop parameter words frontier computation

theorem checkpointObserver_trace (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.output, result.before * result.after)) <$>
      checkpointObserver stop parameter words frontier computation = QueryPause.traced hashObservationTrace computation := by
  have h := QueryPause.trace_resume hashObservationTrace (stop parameter words frontier) computation 1
  have he : (fun result : (Bool × SigningBoundaryTrace) × OtsContactTrace.Trace => (result.1, 1 * result.2)) <$>
      QueryPause.traced hashObservationTrace computation = QueryPause.traced hashObservationTrace computation := by
    simp only [one_mul]
    change id <$> _ = _
    exact id_map _
  simpa only [checkpointObserver, checkpointSplitRun, Functor.map_map, map_bind, map_pure] using h.trans he

theorem checkpointObserver_frontier_trace (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.frontier, result.output, result.before * result.after)) <$>
      checkpointObserver stop parameter words frontier computation =
        (fun result => (frontier, result)) <$> QueryPause.traced hashObservationTrace computation := by
  simpa only [checkpointObserver, Functor.map_map] using
    congrArg (Functor.map (fun result => (frontier, result))) (checkpointObserver_trace stop parameter words frontier computation)

theorem checkpointObserver_contact : checkpointObserver OtsContactTrace.Stopped = contactObserver := rfl

end SphincsSecurity.Concrete
