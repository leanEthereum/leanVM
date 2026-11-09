/-
  LeanVM.Guest.WalkOsOk3

  The certificates of `open_stacked__L21` to `open_stacked__L27` hand on, at each level's
  `opening_queries` call, that level's walk (`osOk`), and their candidates' numbers are the ones the
  walk's obligation needs (`osLvB`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osLvB_21 : osLvB (osCfg 21) = true := by decide +kernel

theorem osOk_324 : osOk 324 (osCfg 21) = true := by decide +kernel

theorem osLvB_22 : osLvB (osCfg 22) = true := by decide +kernel

theorem osOk_325 : osOk 325 (osCfg 22) = true := by decide +kernel

theorem osLvB_23 : osLvB (osCfg 23) = true := by decide +kernel

theorem osOk_326 : osOk 326 (osCfg 23) = true := by decide +kernel

theorem osLvB_24 : osLvB (osCfg 24) = true := by decide +kernel

theorem osOk_327 : osOk 327 (osCfg 24) = true := by decide +kernel

theorem osLvB_25 : osLvB (osCfg 25) = true := by decide +kernel

theorem osOk_328 : osOk 328 (osCfg 25) = true := by decide +kernel

theorem osLvB_26 : osLvB (osCfg 26) = true := by decide +kernel

theorem osOk_329 : osOk 329 (osCfg 26) = true := by decide +kernel

theorem osLvB_27 : osLvB (osCfg 27) = true := by decide +kernel

theorem osOk_330 : osOk 330 (osCfg 27) = true := by decide +kernel

end
end LeanVM.Guest.End
