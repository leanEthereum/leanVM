/-
  LeanVM.Guest.WalkOsOk2

  The certificates of `open_stacked__L14` to `open_stacked__L20` assume the window table and hand
  on, at each level's `opening_queries` call, that level's walk (`osOk`), and their candidates'
  numbers are the ones the walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_14 : osLvB (osCfg 14) = true := by decide +kernel

theorem osOk_346 : osOk 346 (osCfg 14) = true := by decide +kernel

theorem osLvB_15 : osLvB (osCfg 15) = true := by decide +kernel

theorem osOk_347 : osOk 347 (osCfg 15) = true := by decide +kernel

theorem osLvB_16 : osLvB (osCfg 16) = true := by decide +kernel

theorem osOk_348 : osOk 348 (osCfg 16) = true := by decide +kernel

theorem osLvB_17 : osLvB (osCfg 17) = true := by decide +kernel

theorem osOk_349 : osOk 349 (osCfg 17) = true := by decide +kernel

theorem osLvB_18 : osLvB (osCfg 18) = true := by decide +kernel

theorem osOk_350 : osOk 350 (osCfg 18) = true := by decide +kernel

theorem osLvB_19 : osLvB (osCfg 19) = true := by decide +kernel

theorem osOk_351 : osOk 351 (osCfg 19) = true := by decide +kernel

theorem osLvB_20 : osLvB (osCfg 20) = true := by decide +kernel

theorem osOk_352 : osOk 352 (osCfg 20) = true := by decide +kernel

end
end LeanVM.Guest.End
