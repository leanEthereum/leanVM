/-
  LeanVM.Guest.WalkOsOk2

  The certificates of `open_stacked__L14` to `open_stacked__L20` hand on, at each level's
  `opening_queries` call, that level's walk (`osOk`), and their candidates' numbers are the ones the
  walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_14 : osLvB (osCfg 14) = true := by decide +kernel

theorem osOk_317 : osOk 317 (osCfg 14) = true := by decide +kernel

theorem osLvB_15 : osLvB (osCfg 15) = true := by decide +kernel

theorem osOk_318 : osOk 318 (osCfg 15) = true := by decide +kernel

theorem osLvB_16 : osLvB (osCfg 16) = true := by decide +kernel

theorem osOk_319 : osOk 319 (osCfg 16) = true := by decide +kernel

theorem osLvB_17 : osLvB (osCfg 17) = true := by decide +kernel

theorem osOk_320 : osOk 320 (osCfg 17) = true := by decide +kernel

theorem osLvB_18 : osLvB (osCfg 18) = true := by decide +kernel

theorem osOk_321 : osOk 321 (osCfg 18) = true := by decide +kernel

theorem osLvB_19 : osLvB (osCfg 19) = true := by decide +kernel

theorem osOk_322 : osOk 322 (osCfg 19) = true := by decide +kernel

theorem osLvB_20 : osLvB (osCfg 20) = true := by decide +kernel

theorem osOk_323 : osOk 323 (osCfg 20) = true := by decide +kernel

end
end LeanVM.Guest.End
