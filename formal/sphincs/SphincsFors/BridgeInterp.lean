import SphincsFors.BridgeSaturation
import SphincsFors.BridgeRich

/-! One interpreter for cost-level computations: the lazy comparison step, the weighted budget
cap (stopping before a query or tick that exceeds it), the privileged reveals, the original-cost
trace and the saturation payments, all at once. It agrees with the composition of the separate
wrappers, so later arguments can follow the structure of the cost-level program. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Result of an interpreted run: the capped result, the reveals, the trace and, for every
ordinary query in order, its input and whether no hit was decided before it. -/
abbrev Run (D ι α : Type) := Option α × List ι × List (Entry D) × List (D × Bool)

/-- The touch record of one query. -/
noncomputable def touch (state : DebtState D R ι) : (SourceCostSpec D R ι).Domain → List (D × Bool)
  | .inl (.inr (.inl bytes)) => [(bytes, decide (¬Realized tg initial state))]
  | _ => []

noncomputable def interp {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ℕ → DebtState D R ι → ProbComp (Run D ι α × DebtState D R ι) :=
  OracleComp.construct (fun value _ state => pure ((some value, [], [], []), state))
    (fun input _ next budget state =>
      if sourceCost input ≤ budget then
        costStep model input state >>= fun result =>
          (fun out => ((out.1.1, revealed input ++ out.1.2.1, recorded input ++ out.1.2.2.1,
              touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
            next result.1 (budget - sourceCost input) result.2
      else pure ((none, [], [], []), state)) computation

omit [Fintype ι] in
theorem interp_pure {α : Type} (value : α) (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (pure value : OracleComp (SourceCostSpec D R ι) α) budget state =
      pure ((some value, [], [], []), state) := rfl

omit [Fintype ι] in
theorem interp_query_bind {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (liftM ((SourceCostSpec D R ι).query input) >>= next) budget state =
      if sourceCost input ≤ budget then
        costStep model input state >>= fun result =>
          (fun out => ((out.1.1, revealed input ++ out.1.2.1, recorded input ++ out.1.2.2.1,
              touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
            interp tg initial model (next result.1) (budget - sourceCost input) result.2
      else pure ((none, [], [], []), state) := rfl

omit [Fintype ι] in
theorem lazyRun_map {α β : Type} (g : α → β) (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (state : DebtState D R ι) :
    lazyRun model (g <$> computation) state =
      (fun result => (g result.1, result.2)) <$> lazyRun model computation state := by
  simp only [lazyRun, simulateQ_map, StateT.run_map]

omit [Fintype ι] in
theorem lazyRun_erase_query_bind {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α)
    (state : DebtState D R ι) :
    lazyRun model (erase (liftM ((SourceCostSpec D R ι).query input) >>= next)) state =
      costStep model input state >>= fun result => lazyRun model (erase (next result.1)) result.2 := by
  cases input with
  | inl input => rw [erase_query_bind_inl, lazyRun_query_bind]; rfl
  | inr amount =>
      rw [erase_query_bind_inr]
      change _ = (pure ((), state) >>= _)
      rw [pure_bind]

omit [Fintype ι] in
/-- The interpreter agrees with the lazy run of the wrapped computation. -/
theorem lazyRun_wrapped {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) :
    lazyRun model (erase (trace (withReveals (cap computation budget)))) state =
      (fun out => (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
        interp tg initial model computation budget state := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [interp_query_bind]
      change lazyRun model (erase (trace (withReveals (if sourceCost input ≤ budget then
        liftM ((SourceCostSpec D R ι).query input) >>= fun value => cap (next value) (budget - sourceCost input)
        else pure none)))) state = _
      split_ifs with hcost
      · rw [withReveals_query_bind, trace_query_bind, lazyRun_erase_query_bind, map_bind]
        refine bind_congr fun result => ?_
        rw [trace_map, erase_map, lazyRun_map, erase_map, lazyRun_map, ih, Functor.map_map,
          Functor.map_map, Functor.map_map]
      · rfl

/-! ### The saturation payments in the interpreter -/

/-- Flagged digest touches: digest queries made before any hit was decided. -/
noncomputable def flaggedCount (touches : List (D × Bool)) : ℕ :=
  (touches.filter fun entry => decide (tg.digest entry.1) && entry.2).length

omit [Fintype ι] [SampleableType R] in
theorem flaggedCount_append (first second : List (D × Bool)) :
    flaggedCount tg (first ++ second) = flaggedCount tg first + flaggedCount tg second := by
  simp [flaggedCount, List.filter_append]

omit [Fintype ι] [SampleableType R] in
theorem flaggedCount_touch (state : DebtState D R ι) (input : (SourceCostSpec D R ι).Domain) :
    flaggedCount tg (touch tg initial state input) = pays tg initial state input := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · rfl
  · simp only [touch, pays, flaggedCount, List.filter_cons, List.filter_nil]
    by_cases hd : tg.digest bytes <;> by_cases hr : Realized tg initial state <;> simp [hd, hr]
  · rfl
  · rfl

/-! ### Expected flagged touches -/

/-- Expected number of flagged digest touches of an interpreted run. -/
noncomputable def expectedFlagged {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp tg initial model computation budget state] *
    (flaggedCount tg out.1.2.2.2 : ℝ≥0∞)

/-! ### Sequential composition -/

/-- Continue an interpreted run with a second computation, after the first one ended normally. -/
noncomputable def interpThen {α β : Type} (next : α → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ)
    (out : Run D ι α × DebtState D R ι) : ProbComp (Run D ι β × DebtState D R ι) :=
  match out.1.1 with
  | none => pure ((none, out.1.2.1, out.1.2.2.1, out.1.2.2.2), out.2)
  | some value =>
      (fun out' => ((out'.1.1, out.1.2.1 ++ out'.1.2.1, out.1.2.2.1 ++ out'.1.2.2.1,
          out.1.2.2.2 ++ out'.1.2.2.2), out'.2)) <$>
        interp tg initial model (next value) (budget - traceCost out.1.2.2.1) out.2

omit [Fintype ι] in
theorem interp_bind {α β : Type} (first : OracleComp (SourceCostSpec D R ι) α)
    (next : α → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (first >>= next) budget state =
      interp tg initial model first budget state >>= interpThen tg initial model next budget := by
  induction first using OracleComp.inductionOn generalizing budget state with
  | pure value =>
      rw [pure_bind, interp_pure, pure_bind]
      simp only [interpThen, traceCost, List.map_nil, List.sum_nil, Nat.sub_zero, List.nil_append]
      rw [show (fun out' : Run D ι β × DebtState D R ι =>
          ((out'.1.1, out'.1.2.1, out'.1.2.2.1, out'.1.2.2.2), out'.2)) = id from rfl, id_map]
  | query_bind input rest ih =>
      rw [bind_assoc, interp_query_bind, interp_query_bind]
      split_ifs with hcost
      · rw [bind_assoc]
        refine bind_congr fun result => ?_
        rw [ih, map_bind, bind_map_left]
        refine bind_congr fun out => ?_
        simp only [interpThen]
        cases out.1.1 with
        | none => simp
        | some value =>
            simp only [Functor.map_map, List.append_assoc, traceCost_append, recorded_cost, Nat.sub_sub]
      · rw [pure_bind]
        rfl

end SphincsFors.Security.HiddenDebt
