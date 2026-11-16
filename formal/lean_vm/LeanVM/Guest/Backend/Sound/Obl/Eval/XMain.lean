/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XMain

  The `opening_queries` specializations pass `mainOk`, by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Walk
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `0` to `9` of `mainTab` pass their check.** -/
theorem evalMain_0 : ((mainTab.drop 0).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `10` to `19` of `mainTab` pass their check.** -/
theorem evalMain_10 : ((mainTab.drop 10).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `20` to `29` of `mainTab` pass their check.** -/
theorem evalMain_20 : ((mainTab.drop 20).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `30` to `39` of `mainTab` pass their check.** -/
theorem evalMain_30 : ((mainTab.drop 30).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `40` to `49` of `mainTab` pass their check.** -/
theorem evalMain_40 : ((mainTab.drop 40).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `50` to `59` of `mainTab` pass their check.** -/
theorem evalMain_50 : ((mainTab.drop 50).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `60` to `69` of `mainTab` pass their check.** -/
theorem evalMain_60 : ((mainTab.drop 60).take 10).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `70` to `75` of `mainTab` pass their check.** -/
theorem evalMain_70 : ((mainTab.drop 70).take 6).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
