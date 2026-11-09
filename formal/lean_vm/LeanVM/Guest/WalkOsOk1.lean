/-
  LeanVM.Guest.WalkOsOk1

  The certificates of `open_stacked__L7` to `open_stacked__L13` hand on, at each level's
  `opening_queries` call, that level's walk (`osOk`), and their candidates' numbers are the ones the
  walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_7 : osLvB (osCfg 7) = true := by decide +kernel

theorem osOk_310 : osOk 310 (osCfg 7) = true := by decide +kernel

theorem osLvB_8 : osLvB (osCfg 8) = true := by decide +kernel

theorem osOk_311 : osOk 311 (osCfg 8) = true := by decide +kernel

theorem osLvB_9 : osLvB (osCfg 9) = true := by decide +kernel

theorem osOk_312 : osOk 312 (osCfg 9) = true := by decide +kernel

theorem osLvB_10 : osLvB (osCfg 10) = true := by decide +kernel

theorem osOk_313 : osOk 313 (osCfg 10) = true := by decide +kernel

theorem osLvB_11 : osLvB (osCfg 11) = true := by decide +kernel

theorem osOk_314 : osOk 314 (osCfg 11) = true := by decide +kernel

theorem osLvB_12 : osLvB (osCfg 12) = true := by decide +kernel

theorem osOk_315 : osOk 315 (osCfg 12) = true := by decide +kernel

theorem osLvB_13 : osLvB (osCfg 13) = true := by decide +kernel

theorem osOk_316 : osOk 316 (osCfg 13) = true := by decide +kernel

end
end LeanVM.Guest.End
