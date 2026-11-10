/-
  LeanVM.Guest.WalkOsOk1

  The certificates of `open_stacked__L7` to `open_stacked__L13` assume the window table and hand
  on, at each level's `opening_queries` call, that level's walk (`osOk`), and their candidates'
  numbers are the ones the walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_7 : osLvB (osCfg 7) = true := by decide +kernel

theorem osOk_339 : osOk 339 (osCfg 7) = true := by decide +kernel

theorem osLvB_8 : osLvB (osCfg 8) = true := by decide +kernel

theorem osOk_340 : osOk 340 (osCfg 8) = true := by decide +kernel

theorem osLvB_9 : osLvB (osCfg 9) = true := by decide +kernel

theorem osOk_341 : osOk 341 (osCfg 9) = true := by decide +kernel

theorem osLvB_10 : osLvB (osCfg 10) = true := by decide +kernel

theorem osOk_342 : osOk 342 (osCfg 10) = true := by decide +kernel

theorem osLvB_11 : osLvB (osCfg 11) = true := by decide +kernel

theorem osOk_343 : osOk 343 (osCfg 11) = true := by decide +kernel

theorem osLvB_12 : osLvB (osCfg 12) = true := by decide +kernel

theorem osOk_344 : osOk 344 (osCfg 12) = true := by decide +kernel

theorem osLvB_13 : osLvB (osCfg 13) = true := by decide +kernel

theorem osOk_345 : osOk 345 (osCfg 13) = true := by decide +kernel

end
end LeanVM.Guest.End
