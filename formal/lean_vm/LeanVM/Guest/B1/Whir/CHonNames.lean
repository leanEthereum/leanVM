/-
  LeanVM.Guest.B1.Whir.CHonNames

  The kinds of open_stacked's callees by name at a configuration, as one decidable proposition.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.OsCallV

/-!
# The callees' kinds, decided

`HonNames c`: the names the body calls at each level map to their kinds (`osKindOf`): the fold
and closing rounds, the grinds, `fold_final_msg`, each level's message, out-of-domain squeezes and
cap check; its decoder, squeeze loop, `opening_queries` and residual loop to none; the cap depths in range.
`Whir/CHonNames{0..3}.lean` decide it for the 28 candidates.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.B1

@[expose] public section

/-- **The callees' kinds at a configuration.** -/
def HonNames (c : OsCfg) : Prop :=
  let lv := osLvAt c
  osKindOf "opening_round" = some .round ∧ osKindOf "opening_tail_round" = some .tail ∧
  osKindOf ("grind_check__L" ++ natStr queryGrind) = some (.grind queryGrind) ∧
  osKindOf ("grind_check__L" ++ natStr levelOodGrind) = some (.grind levelOodGrind) ∧
  osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog) ∧
  osKindOf ("opening_message__L" ++ natStr (c.yrLen + (lv c.yrLevel).folds) ++ "_L1") =
    some (.msg (c.yrLen + (lv c.yrLevel).folds) 1) ∧
  (∀ l < c.yrLevel,
    osKindOf ("opening_message__L" ++ natStr (2 + (lv l).folds) ++ "_L1") = some (.msg (2 + (lv l).folds) 1) ∧
    osKindOf ("squeeze_point_from__L" ++ natStr (lv l).logCols) = some (.spf (lv l).logCols)) ∧
  (∀ l < c.yrLevel, osKindOf (c.resLoop l) = none) ∧
  ∀ l < c.levels.length,
    osKindOf ("verify_merkle_cap__L" ++ natStr (lv l).capDepth) = some (.cap (lv l).capDepth) ∧
    osKindOf ("decode_query_windows__L" ++ natStr (lv l).depth ++ "_L" ++ natStr (lv l).capDepth) = none ∧
    osKindOf (c.sqLoop l) = none ∧ osKindOf (osQueriesName c l (lv l)) = none ∧
    2 ≤ (lv l).capDepth ∧ (lv l).capDepth ≤ (lv l).depth

instance (c : OsCfg) : Decidable (HonNames c) := by
  unfold HonNames; dsimp only; infer_instance

end
end LeanVM.Guest.B1.Whir
