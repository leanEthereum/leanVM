/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XOs0

  `open_stacked__L0` to `__L5` pass `osOk`, by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Os
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `0` to `0` of `osTab` pass their check.** -/
theorem evalOs_0 : ((osTab.drop 0).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `1` to `1` of `osTab` pass their check.** -/
theorem evalOs_1 : ((osTab.drop 1).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `2` to `2` of `osTab` pass their check.** -/
theorem evalOs_2 : ((osTab.drop 2).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `3` to `3` of `osTab` pass their check.** -/
theorem evalOs_3 : ((osTab.drop 3).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `4` to `4` of `osTab` pass their check.** -/
theorem evalOs_4 : ((osTab.drop 4).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

/-- **Entries `5` to `5` of `osTab` pass their check.** -/
theorem evalOs_5 : ((osTab.drop 5).take 1).all (fun e => osOk e.1 e.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
