import SphincsSecurity.Proof.Base.QueryPauseInvariant
namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Trace Result : Type} {spec : OracleSpec Index} [Monoid Trace]
  (observation : (input : spec.Domain) → spec.Range input → Trace)

noncomputable def traced (computation : OracleComp spec Result) : OracleComp spec (Result × Trace) :=
  (simulateQ ((QueryImpl.id' spec).withTrace observation) computation).run

theorem traced_pure (result : Result) : traced observation (pure result : OracleComp spec Result) = pure (result, 1) := by
  simp only [traced, simulateQ_pure, WriterT.run_pure]

theorem traced_forget (computation : OracleComp spec Result) : Prod.fst <$> traced observation computation = computation := by
  rw [traced, QueryImpl.fst_map_run_withTrace, simulateQ_id']

theorem traced_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    traced observation (liftM (spec.query input) >>= next) =
      liftM (spec.query input) >>= fun answer => (fun tail => (tail.1, observation input answer * tail.2)) <$> traced observation (next answer) := by
  simp only [traced, simulateQ_bind, simulateQ_spec_query, QueryImpl.withTrace_apply,
    WriterT.run_bind, WriterT.run_tell, QueryImpl.id'_apply, WriterT.run_monadLift, bind_map_left, bind_assoc, pure_bind, one_mul, Functor.map_map]

theorem traced_counted (selected : Index → Prop) [DecidablePred selected] (cost : Trace → Nat)
    (hzero : cost 1 = 0)
    (hstep : ∀ input answer trace, cost (observation input answer * trace) = (if selected input then 1 else 0) + cost trace)
    (computation : OracleComp spec Result) :
    (fun result => (result.1, cost result.2)) <$> traced observation computation = QueryCap.counted selected computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [traced_pure, QueryCap.counted_pure, map_pure, hzero]
  | query_bind input next ih =>
      simp only [traced_query_bind, QueryCap.counted_query_bind, map_bind, Functor.map_map, hstep]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]

theorem trace_resume (stop : Trace → Prop) [DecidablePred stop]
    (computation : OracleComp spec Result) (history : Trace) :
    (do
      let paused ← run stop (fun input answer memory => memory * observation input answer) computation history
      let tail ← traced observation paused.2
      pure (tail.1, paused.1 * tail.2)) =
        (fun result => (result.1, history * result.2)) <$> traced observation computation := by
  induction computation using OracleComp.inductionOn generalizing history with
  | pure result => simp only [run_pure, traced_pure, pure_bind, map_pure, mul_one]
  | query_bind input next ih =>
      rw [run_query_bind]
      by_cases hs : stop history
      · simp only [if_pos hs, pure_bind, bind_pure_comp]
      · simp only [if_neg hs, bind_assoc, traced_query_bind, map_bind, Functor.map_map, ← mul_assoc]
        exact congrArg (fun continuation => liftM (spec.query input) >>= continuation)
          (funext fun answer => ih answer (history * observation input answer))

end SphincsSecurity.QueryPause
