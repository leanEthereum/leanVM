/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XLoop1

  The loop helpers of `opening_queries` pass `loopOk` (second half), by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Walk
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `38` to `45` of `loopTab` pass their check.** -/
theorem evalLoop_38 : ((loopTab.drop 38).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `46` to `53` of `loopTab` pass their check.** -/
theorem evalLoop_46 : ((loopTab.drop 46).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `54` to `61` of `loopTab` pass their check.** -/
theorem evalLoop_54 : ((loopTab.drop 54).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `62` to `69` of `loopTab` pass their check.** -/
theorem evalLoop_62 : ((loopTab.drop 62).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `70` to `75` of `loopTab` pass their check.** -/
theorem evalLoop_70 : ((loopTab.drop 70).take 6).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
