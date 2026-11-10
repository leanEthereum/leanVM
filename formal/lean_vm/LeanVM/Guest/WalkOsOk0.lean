/-
  LeanVM.Guest.WalkOsOk0

  The certificates of `open_stacked__L0` to `open_stacked__L6` assume the window table and hand
  on, at each level's `opening_queries` call, that level's walk (`osOk`), and their candidates'
  numbers are the ones the walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_0 : osLvB (osCfg 0) = true := by decide +kernel

theorem osOk_332 : osOk 332 (osCfg 0) = true := by decide +kernel

theorem osLvB_1 : osLvB (osCfg 1) = true := by decide +kernel

theorem osOk_333 : osOk 333 (osCfg 1) = true := by decide +kernel

theorem osLvB_2 : osLvB (osCfg 2) = true := by decide +kernel

theorem osOk_334 : osOk 334 (osCfg 2) = true := by decide +kernel

theorem osLvB_3 : osLvB (osCfg 3) = true := by decide +kernel

theorem osOk_335 : osOk 335 (osCfg 3) = true := by decide +kernel

theorem osLvB_4 : osLvB (osCfg 4) = true := by decide +kernel

theorem osOk_336 : osOk 336 (osCfg 4) = true := by decide +kernel

theorem osLvB_5 : osLvB (osCfg 5) = true := by decide +kernel

theorem osOk_337 : osOk 337 (osCfg 5) = true := by decide +kernel

theorem osLvB_6 : osLvB (osCfg 6) = true := by decide +kernel

theorem osOk_338 : osOk 338 (osCfg 6) = true := by decide +kernel

end
end LeanVM.Guest.End
