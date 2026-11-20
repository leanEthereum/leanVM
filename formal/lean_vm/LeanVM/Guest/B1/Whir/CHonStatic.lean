/-
  LeanVM.Guest.B1.Whir.CHonStatic

  The configuration facts the honest buffers' reads take, as one decidable proposition.
-/

module

public import LeanVM.Guest.B1.Whir.CHead
public import LeanVM.Guest.B1.Place.OsBos

/-!
# The honest buffers' configuration facts

`HonStatic c`: the levels' segments of `query_positions` in order within its buffer, the
non-final levels' rows of `ood_z` in order within it, the fold rounds' offsets, and the buffers'
sizes (`osSizesL`) at the indices the reads use. `Whir/CHonStatic{0..3}.lean` decide it for the 28 candidates.
`chain_disj` (`Place/OsBos`): segments in order are disjoint.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- The positions one squeeze decodes at a level. -/
abbrev sqPer (lv : OsLv) : ℕ := 128 / lv.depth

/-- **The honest buffers' configuration facts.** -/
def HonStatic (c : OsCfg) : Prop :=
  let n := c.levels.length
  let lv := fun l ↦ c.levels.getD l default
  2 ≤ n ∧ c.yrLevel + 1 = n ∧ c.yrLog ≤ yrLogCap ∧
  (∀ l < n, (lv l).posOff + (lv l).squeezes * sqPer (lv l) ≤
    (if l + 1 < n then (lv (l + 1)).posOff else c.posTotal)) ∧
  (∀ l < n, 1 ≤ sqPer (lv l)) ∧
  (∀ l < c.yrLevel, (lv l).colsOff + (lv l).logCols ≤
    (if l + 1 < c.yrLevel then (lv (l + 1)).colsOff else c.colsTotal)) ∧
  (lv 0).foldsOff = 0 ∧ (∀ l < c.yrLevel, (lv (l + 1)).foldsOff = (lv l).foldsOff + (lv l).folds) ∧
  (lv c.yrLevel).foldsOff + (lv c.yrLevel).folds = c.nFolds ∧
  (osSizesL c).length = 19 + c.yrLevel ∧
  (∀ j < 11, (osSizesL c).getD j 0 = (headSizes c).getD j 0) ∧
  (∀ l < c.yrLevel, (osSizesL c).getD (11 + l) 0 = 2 + (lv l).folds) ∧
  (osSizesL c).getD (11 + c.yrLevel) 0 = c.yrLen + (lv c.yrLevel).folds ∧
  (∀ k < 7, (osSizesL c).getD (12 + c.yrLevel + k) 0 =
    [yrLogCap, pointCap, pointCap, c.colsTotal, n, n, 2 * n].getD k 0)

instance (c : OsCfg) : Decidable (HonStatic c) := by
  unfold HonStatic; dsimp only; infer_instance

end
end LeanVM.Guest.B1.Whir
