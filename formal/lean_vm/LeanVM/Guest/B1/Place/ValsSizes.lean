/-
  LeanVM.Guest.B1.Place.ValsSizes

  open_stacked's buffers' sizes are below `2^64 - 1` at every arm, decided.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# The buffers' sizes, decided

`osSizesL_rateV`: the sizes do not depend on the rate; `osSizesL_boundV`: at every arm they are
below `2^64 - 1`, so their `g`-power words name them (`logG`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osSizesL_rateV (m ri : ℕ) : osSizesL (osCfgR m ri) = osSizesL (osCfg m) := by
  simp [osSizesL, osCfgR, OsCfg.withLevels, osCfg, osLevelsR]

/-- **Every arm's buffers' sizes are below `2^64 - 1`.** -/
theorem osSizesL_boundV : ∀ m < osArms, ∀ e ∈ osSizesL (osCfg m), e < 2 ^ 64 - 1 := by
  decide +kernel

end
end LeanVM.Guest.B1
