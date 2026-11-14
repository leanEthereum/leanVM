/-
  LeanVM.Guest.B1.Whir.CHonNames

  The kinds of open_stacked's callees by name at a configuration, as one decidable proposition.
-/

module

public import LeanVM.Guest.B1.Place.OsMean

/-!
# The callees' kinds, decided

`HonNames c`: the names the body calls at each level map to their kinds (`osKindOf`): the fold
and closing rounds, the grinds, `fold_final_msg`, each level's message and out-of-domain squeeze;
the helpers it dispatches into (`level_positions`, `level_queries`, `level_residual`) to none.
`Whir/CHonNames{0..3}.lean` decide it for the 11 arms at each rate.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.B1

@[expose] public section

/-- **The callees' kinds at a configuration.** -/
def HonNames (c : OsCfg) : Prop :=
  let lv := fun l ↦ c.levels.getD l default
  osKindOf "opening_round" = some .round ∧ osKindOf "opening_tail_round" = some .tail ∧
  osKindOf ("grind_check__L" ++ natStr queryGrind) = some (.grind queryGrind) ∧
  osKindOf ("grind_check__L" ++ natStr levelOodGrind) = some (.grind levelOodGrind) ∧
  osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog) ∧
  osKindOf ("opening_message__L" ++ natStr (c.yrLen + (lv c.yrLevel).folds) ++ "_L1") =
    some (.msg (c.yrLen + (lv c.yrLevel).folds) 1) ∧
  (∀ l < c.yrLevel,
    osKindOf ("opening_message__L" ++ natStr (2 + (lv l).folds) ++ "_L1") = some (.msg (2 + (lv l).folds) 1) ∧
    osKindOf ("squeeze_point_from__L" ++ natStr (lv l).logCols) = some (.spf (lv l).logCols) ∧
    osKindOf (osResidualName (lv l)) = none) ∧
  ∀ l < c.levels.length,
    osKindOf (osPositionsName (lv l)) = none ∧ osKindOf (osQueriesName c l (lv l)) = none

instance (c : OsCfg) : Decidable (HonNames c) := by
  unfold HonNames; dsimp only; infer_instance

end
end LeanVM.Guest.B1.Whir
