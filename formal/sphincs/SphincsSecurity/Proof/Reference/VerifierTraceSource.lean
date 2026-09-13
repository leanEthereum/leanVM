import SphincsSecurity.Proof.Reference.VerifierTraceDescent
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedTrace {Result : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) : ProbComp (Result × Trace) :=
  simulateQ (fixedHashWorld f) (QueryPause.traced hashObservationTrace computation)

theorem fixedTrace_forget {Result : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) :
    Prod.fst <$> fixedTrace f computation = simulateQ (fixedHashWorld f) computation := by
  rw [fixedTrace, ← simulateQ_map, QueryPause.traced_forget]

theorem fixedTrace_pure {Result : Type} (f : QueryImpl HashSpec Id) (value : Result) :
    fixedTrace f (pure value) = pure (value, 1) := by
  simp only [fixedTrace, QueryPause.traced_pure, simulateQ_pure]

theorem fixedTrace_bind {Result Next : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result)
    (next : Result → OracleComp OracleWorld Next) :
    fixedTrace f (computation >>= next) = fixedTrace f computation >>= fun first =>
      (fun second => (second.1, first.2 * second.2)) <$> fixedTrace f (next first.1) := by
  simp only [fixedTrace, QueryPause.traced, simulateQ_bind, WriterT.run_bind, simulateQ_map]

theorem fixedTrace_map {Result Next : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) (g : Result → Next) :
    fixedTrace f (g <$> computation) = (fun result => (g result.1, result.2)) <$> fixedTrace f computation := by
  simp only [fixedTrace, QueryPause.traced, simulateQ_map, WriterT.run_map]

theorem fixedTrace_hash_query (f : QueryImpl HashSpec Id) (input : HashInput) :
    fixedTrace f (liftM (OracleWorld.query (.inr input))) = pure (f input, FreeMonoid.of (input, f input)) := by
  simp only [fixedTrace, QueryPause.traced, simulateQ_spec_query, QueryImpl.withTrace_apply,
    QueryImpl.id'_apply, WriterT.run_bind, WriterT.run_tell, WriterT.run_monadLift, simulateQ_bind,
    simulateQ_map, simulateQ_spec_query, fixedHashWorld, pure_bind, map_pure, one_mul, hashObservationTrace,
    WriterT.run_pure, simulateQ_pure, mul_one]

def answerTrace {Result : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec Result) : Trace :=
  FreeMonoid.ofList ((queriedInputs f computation).map fun input => (input, f input))

theorem containsRun_answerTrace {Result : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec Result) :
    ContainsRun f (answerTrace f computation) computation := by
  intro input hi
  exact List.mem_map_of_mem (f := fun input => (input, f input)) hi

private theorem boundaryComputation_bind {Result Next : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld Result)
    (next : Result → OracleComp OracleWorld Next) :
    boundaryComputation parameter (computation >>= next) = boundaryComputation parameter computation >>= fun first =>
      (fun second => (second.1, first.2 * second.2)) <$> boundaryComputation parameter (next first.1) := by
  simp only [boundaryComputation, simulateQ_bind, WriterT.run_bind]

private theorem boundaryComputation_hash_query (parameter : PublicParameter) (input : HashInput) :
    boundaryComputation parameter (liftM (OracleWorld.query (.inr input))) =
      (fun answer => (answer, signingBoundaryTrace parameter (.inr input) answer)) <$> liftM (OracleWorld.query (.inr input)) := by
  simp only [boundaryComputation, simulateQ_spec_query, QueryImpl.withTrace_apply, QueryImpl.id'_apply,
    WriterT.run_bind, WriterT.run_map, WriterT.run_tell, WriterT.run_monadLift, map_pure, one_mul, bind_pure_comp,
    Functor.map_map]

theorem fixedTrace_boundary_hash {Result : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec Result) :
    fixedTrace f (boundaryComputation parameter (liftM computation)) = pure (boundaryEval parameter f computation, answerTrace f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [liftM_pure, boundaryComputation, simulateQ_pure, WriterT.run_pure, fixedTrace_pure,
        boundaryEval_pure, answerTrace, queriedInputs_pure, List.map_nil]
      rfl
  | query_bind input next ih =>
      rw [liftM_bind, boundaryComputation_bind, fixedTrace_bind]
      change (fixedTrace f (boundaryComputation parameter (liftM (OracleWorld.query (.inr input)))) >>= _) = _
      rw [boundaryComputation_hash_query, fixedTrace_map, fixedTrace_hash_query, map_pure, pure_bind,
        fixedTrace_map, ih, map_pure, map_pure]
      simp only [answerTrace, queriedInputs_query_bind, List.map_cons, FreeMonoid.ofList_cons]
      rw [boundaryEval_bind, boundaryEval_hash_query]
      rfl

end SphincsSecurity.Concrete.OtsContactTrace
