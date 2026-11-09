module

public import FORS.Reduction.PreparedSample

@[expose] public section

/-! Probabilistic semantics of the graph-view game with an explicit cost trace, and the exact
"identical until the seed is named" comparison for two fixed answer functions. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Stop

variable [Params]

open Completeness HiddenCost GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Private draws are real; ordinary queries read a fixed function; reveals read a fixed table;
honest-work ticks are free here (their cost is kept in the trace); an honest read reads the fixed
function at the raw input it stands for. -/
noncomputable def fixedCostP (f : HashInput → HashOutput) (table : HiddenGraph.Table) :
    QueryImpl CostSpec ProbComp
  | .inl (.inl draw) => liftM (unifSpec.query draw)
  | .inl (.inr (.inl input)) => pure (f input)
  | .inl (.inr (.inr coordinate)) => pure (table coordinate)
  | .inr (.inl _) => pure ()
  | .inr (.inr honest) => pure (f (HonestInputs.toInput honest))

noncomputable def costRun {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) : ProbComp (α × List (Entry HashInput)) :=
  simulateQ (fixedCostP f table) (trace computation)

theorem costRun_pure {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table) (value : α) :
    costRun f table (pure value) = pure (value, []) := by
  simp [costRun, trace_pure]

theorem costRun_query_bind {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (input : CostSpec.Domain) (next : CostSpec.Range input → OracleComp CostSpec α) :
    costRun f table (liftM (CostSpec.query input) >>= next) =
      fixedCostP f table input >>= fun answer =>
        (fun result => (result.1, recorded input ++ result.2)) <$> costRun f table (next answer) := by
  rw [costRun, trace_query_bind, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map, costRun]

theorem liftM_id_pmf {α : Type} (x : α) : (liftM (show Id α from x) : PMF α) = PMF.pure x := rfl

theorem evalDist_liftM_id {α : Type} (x : α) :
    (liftM (show Id α from x) : PMF α) =ᵈ (pure x : ProbComp α) := by
  rw [liftM_id_pmf]
  exact Assembly.evalDistEq_pure x

/-! ### Identical until a marked ordinary input -/

/-- Some ordinary input of the trace satisfies the marker. -/
def Hits (marked : HashInput → Prop) (entries : List (Entry HashInput)) : Prop :=
  ∃ input, Sum.inl input ∈ entries ∧ marked input

/-! ### Capping the original budget -/

theorem cap_query_bind' {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : Nat) :
    cap (liftM (CostSpec.query input) >>= next) budget =
      if sourceCost input ≤ budget then
        liftM (CostSpec.query input) >>= fun value => cap (next value) (budget - sourceCost input)
      else pure none := rfl

end FORS.Security.Stop
