import SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (stop : Memory → Prop) [DecidablePred stop]
  (step : (input : spec.Domain) → spec.Range input → Memory → Memory)

noncomputable def run (computation : OracleComp spec Result) : Memory → OracleComp spec (Memory × OracleComp spec Result) :=
  OracleComp.construct (fun result memory => pure (memory, pure result))
    (fun input original next memory =>
      if stop memory then pure (memory, liftM (spec.query input) >>= original)
      else liftM (spec.query input) >>= fun answer => next answer (step input answer memory)) computation

theorem run_pure (result : Result) (memory : Memory) :
    run stop step (pure result : OracleComp spec Result) memory = pure (memory, pure result) := rfl

theorem run_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) (memory : Memory) :
    run stop step (liftM (spec.query input) >>= next) memory =
      if stop memory then pure (memory, liftM (spec.query input) >>= next)
      else liftM (spec.query input) >>= fun answer => run stop step (next answer) (step input answer memory) := rfl

theorem resume (computation : OracleComp spec Result) (memory : Memory) :
    (run stop step computation memory >>= fun paused => paused.2) = computation := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [run_pure, pure_bind]
  | query_bind input next ih =>
      rw [run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, pure_bind]
      · simp only [if_neg hs, bind_assoc, ih]

variable (selected : Index → Prop) [DecidablePred selected]

theorem counted_resume (computation : OracleComp spec Result) (memory : Memory) :
    (do
      let paused ← QueryCap.counted selected (run stop step computation memory)
      let result ← QueryCap.counted selected paused.1.2
      pure (result.1, paused.2 + result.2)) = QueryCap.counted selected computation := by
  rw [← QueryCap.counted_bind, resume]

end SphincsSecurity.QueryPause
