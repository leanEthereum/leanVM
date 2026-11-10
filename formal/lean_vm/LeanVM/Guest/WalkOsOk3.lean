/-
  LeanVM.Guest.WalkOsOk3

  The certificates of `open_stacked__L21` to `open_stacked__L27` assume the window table and hand
  on, at each level's `opening_queries` call, that level's walk (`osOk`), and their candidates'
  numbers are the ones the walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_21 : osLvB (osCfg 21) = true := by decide +kernel

theorem osOk_353 : osOk 353 (osCfg 21) = true := by decide +kernel

theorem osLvB_22 : osLvB (osCfg 22) = true := by decide +kernel

theorem osOk_354 : osOk 354 (osCfg 22) = true := by decide +kernel

theorem osLvB_23 : osLvB (osCfg 23) = true := by decide +kernel

theorem osOk_355 : osOk 355 (osCfg 23) = true := by decide +kernel

theorem osLvB_24 : osLvB (osCfg 24) = true := by decide +kernel

theorem osOk_356 : osOk 356 (osCfg 24) = true := by decide +kernel

theorem osLvB_25 : osLvB (osCfg 25) = true := by decide +kernel

theorem osOk_357 : osOk 357 (osCfg 25) = true := by decide +kernel

theorem osLvB_26 : osLvB (osCfg 26) = true := by decide +kernel

theorem osOk_358 : osOk 358 (osCfg 26) = true := by decide +kernel

theorem osLvB_27 : osLvB (osCfg 27) = true := by decide +kernel

theorem osOk_359 : osOk 359 (osCfg 27) = true := by decide +kernel

end
end LeanVM.Guest.End
