import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.QueryCap

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

noncomputable def run (computation : OracleComp spec Result) : Nat → OracleComp spec (Option (Result × Nat)) :=
  OracleComp.construct (fun result budget => pure (some (result, budget)))
    (fun input _ next budget =>
      if selected input then
        match budget with
        | 0 => pure none
        | remaining + 1 => liftM (spec.query input) >>= fun answer => next answer remaining
      else liftM (spec.query input) >>= fun answer => next answer budget) computation

theorem run_pure (result : Result) (budget : Nat) :
    run selected (pure result : OracleComp spec Result) budget = pure (some (result, budget)) := rfl

theorem run_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) (budget : Nat) :
    run selected (liftM (spec.query input) >>= next) budget =
      if selected input then
        match budget with
        | 0 => pure none
        | remaining + 1 => liftM (spec.query input) >>= fun answer => run selected (next answer) remaining
      else liftM (spec.query input) >>= fun answer => run selected (next answer) budget := rfl

theorem run_queryBound (computation : OracleComp spec Result) (budget : Nat) :
    (run selected computation budget).IsQueryBoundP selected budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure result => simp only [run_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [run_query_bind]
      by_cases hselected : selected input
      · rw [if_pos hselected]
        cases budget with
        | zero => exact isQueryBoundP_pure selected none 0
        | succ budget =>
            simp only [isQueryBoundP_query_bind_iff, hselected, not_true_eq_false, false_or, Nat.zero_lt_succ,
              ↓reduceIte, Nat.add_sub_cancel, true_and]
            exact fun answer => ih answer budget
      · simp only [isQueryBoundP_query_bind_iff, hselected, not_false_eq_true, true_or,
          ↓reduceIte, true_and]
        exact fun answer => ih answer budget

theorem run_bind (computation : OracleComp spec Result) (next : Result → OracleComp spec Next) (budget : Nat) :
    run selected (computation >>= next) budget = (do
      match ← run selected computation budget with
      | none => pure none
      | some result => run selected (next result.1) result.2) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure result => simp only [pure_bind, run_pure]
  | query_bind input continuation ih =>
      rw [bind_assoc, run_query_bind, run_query_bind]
      by_cases hselected : selected input
      · rw [if_pos hselected, if_pos hselected]
        cases budget with
        | zero => simp only [pure_bind]
        | succ budget => simp only [bind_assoc, ih]
      · simp only [if_neg hselected, bind_assoc, ih]

def finish (budget : Nat) (result : Result × Nat) : Option (Result × Nat) :=
  if result.2 ≤ budget then some (result.1, budget - result.2) else none

theorem run_eq_counted (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat) :
    simulateQ impl (run selected computation budget) =
      (simulateQ impl (counted selected computation)).map (finish budget) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure result =>
      simp only [run_pure, counted_pure, simulateQ_pure, ← PMF.monad_map_eq_map, map_pure,
        finish, Nat.zero_le, if_true, Nat.sub_zero]
  | query_bind input next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases hselected : selected input
      · rw [if_pos hselected]
        cases budget with
        | zero =>
            simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, PMF.monad_bind_eq_bind,
              PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
              finish, if_pos hselected, Nat.add_comm 1, Nat.add_one_le_iff, Nat.not_lt_zero, if_false, PMF.bind_const]
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, ih, simulateQ_pure, PMF.monad_bind_eq_bind,
              PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, finish, if_pos hselected,
              Nat.add_comm 1, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
      · simp only [if_neg hselected, simulateQ_bind, simulateQ_spec_query, ih, simulateQ_pure,
          PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
          Nat.zero_add, Prod.mk.eta]

end SphincsSecurity.QueryCap
