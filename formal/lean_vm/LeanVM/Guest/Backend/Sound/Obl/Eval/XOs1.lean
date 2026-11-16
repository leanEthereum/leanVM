/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XOs1

  `open_stacked__L6` to `__L10` pass `osOk`, by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Os
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `6` to `6` of `osTab` pass their check.** -/
theorem evalOs_6 : ((osTab.drop 6).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `7` to `7` of `osTab` pass their check.** -/
theorem evalOs_7 : ((osTab.drop 7).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `8` to `8` of `osTab` pass their check.** -/
theorem evalOs_8 : ((osTab.drop 8).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `9` to `9` of `osTab` pass their check.** -/
theorem evalOs_9 : ((osTab.drop 9).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `10` to `10` of `osTab` pass their check.** -/
theorem evalOs_10 : ((osTab.drop 10).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
