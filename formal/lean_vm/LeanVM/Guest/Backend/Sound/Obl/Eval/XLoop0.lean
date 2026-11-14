/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.XLoop0

  The loop helpers of `opening_queries` pass `loopOk` (first half), by kernel evaluation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Walk
public import LeanVM.Guest.Backend.Sound.Obl.GuestXTab

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Guest

@[expose] public section

/-- **Entries `0` to `7` of `loopTab` pass their check.** -/
theorem evalLoop_0 : ((loopTab.drop 0).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `8` to `15` of `loopTab` pass their check.** -/
theorem evalLoop_8 : ((loopTab.drop 8).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `16` to `23` of `loopTab` pass their check.** -/
theorem evalLoop_16 : ((loopTab.drop 16).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `24` to `31` of `loopTab` pass their check.** -/
theorem evalLoop_24 : ((loopTab.drop 24).take 8).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Entries `32` to `37` of `loopTab` pass their check.** -/
theorem evalLoop_32 : ((loopTab.drop 32).take 6).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
