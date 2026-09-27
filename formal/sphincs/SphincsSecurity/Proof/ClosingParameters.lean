import SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef

/-!
# Where the two budget routes meet

`budgetSplit` is the budget at which the proof switches from the forced few-time games to the retained residual monitor. `primitiveCoefficient` bounds, per query below it, the one-time primitive events and the message work of the full certificate. Both are sealed; their values enter only `primitive_rates_small` and the closing arithmetic.
-/

namespace SphincsSecurity.Concrete

open ENNReal

irreducible_def budgetSplit : Nat := 2 ^ 114

noncomputable irreducible_def primitiveCoefficient : ENNReal := 7 / 4

theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num

end SphincsSecurity.Concrete
