import VCVio.OracleComp.QueryTracking.QueryBound
namespace XmssSecurity.QueryCounting

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index} {Result Next : Type}
  (selected : Index → Prop) [DecidablePred selected]

noncomputable def counted (computation : OracleComp spec Result) : OracleComp spec (Result × Nat) :=
  OracleComp.construct (fun result => pure (result, 0))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, (if selected input then 1 else 0) + result.2)) computation

theorem counted_pure (result : Result) : counted selected (pure result : OracleComp spec Result) = pure (result, 0) := rfl

theorem counted_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    counted selected (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← counted selected (next answer)
      pure (result.1, (if selected input then 1 else 0) + result.2)) := rfl

theorem counted_forget (computation : OracleComp spec Result) :
    Prod.fst <$> counted selected computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [counted_pure, map_pure]
  | query_bind input next ih =>
      simp only [counted_query_bind, map_bind, bind_pure_comp, Functor.map_map, ih]

theorem counted_bind (computation : OracleComp spec Result) (next : Result → OracleComp spec Next) :
    counted selected (computation >>= next) = (do
      let first ← counted selected computation
      let second ← counted selected (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, counted_pure, zero_add, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, counted_query_bind, ih, pure_bind, Nat.add_assoc]

theorem counted_map (computation : OracleComp spec Result) (f : Result → Next) :
    counted selected (f <$> computation) = (fun result => (f result.1, result.2)) <$> counted selected computation := by
  rw [show f <$> computation = computation >>= fun result => pure (f result) from (bind_pure_comp f computation).symm,
    counted_bind]
  simp only [counted_pure, Nat.add_zero, bind_pure_comp, map_pure]

end XmssSecurity.QueryCounting
