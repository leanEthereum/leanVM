/-
  LeanVM.Guest.WalkOsOk0

  The certificates of `open_stacked__L0` to `open_stacked__L6` hand on, at each level's
  `opening_queries` call, that level's walk (`osOk`), and their candidates' numbers are the ones the
  walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_0 : osLvB (osCfg 0) = true := by decide +kernel

theorem osOk_303 : osOk 303 (osCfg 0) = true := by decide +kernel

theorem osLvB_1 : osLvB (osCfg 1) = true := by decide +kernel

theorem osOk_304 : osOk 304 (osCfg 1) = true := by decide +kernel

theorem osLvB_2 : osLvB (osCfg 2) = true := by decide +kernel

theorem osOk_305 : osOk 305 (osCfg 2) = true := by decide +kernel

theorem osLvB_3 : osLvB (osCfg 3) = true := by decide +kernel

theorem osOk_306 : osOk 306 (osCfg 3) = true := by decide +kernel

theorem osLvB_4 : osLvB (osCfg 4) = true := by decide +kernel

theorem osOk_307 : osOk 307 (osCfg 4) = true := by decide +kernel

theorem osLvB_5 : osLvB (osCfg 5) = true := by decide +kernel

theorem osOk_308 : osOk 308 (osCfg 5) = true := by decide +kernel

theorem osLvB_6 : osLvB (osCfg 6) = true := by decide +kernel

theorem osOk_309 : osOk 309 (osCfg 6) = true := by decide +kernel

end
end LeanVM.Guest.End
