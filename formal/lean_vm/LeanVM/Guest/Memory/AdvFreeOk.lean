/-
  LeanVM.Guest.Memory.AdvFreeOk

  `AdvFreeOk`, from the kernel's checks of its ranges.
-/

module

public import LeanVM.Guest.Memory.AdvFreeOk0
public import LeanVM.Guest.Memory.AdvFreeOk25
public import LeanVM.Guest.Memory.AdvFreeOk50
public import LeanVM.Guest.Memory.AdvFreeOk325
public import LeanVM.Guest.Memory.AdvFreeOk350
public import LeanVM.Guest.Memory.AdvFreeOk800
public import LeanVM.Guest.Memory.AdvFreeOk1200
public import LeanVM.Guest.CoreData

/-!
# Every function passes `advFreeChk`

`advFreeOk`: the kernel's checks of `advFreeChk` on every function (`AdvFreeOk0` and the rest, a module per
range, the ranges cut around the largest functions).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest

public section

/-- **Every function passes `advFreeChk`.** -/
theorem advFreeOk : AdvFreeOk := by
  unfold AdvFreeOk
  rw [coreProgram_length]
  have h := (((((advFree_ok_0.append advFree_ok_25).append advFree_ok_50).append advFree_ok_325).append
    advFree_ok_350).append advFree_ok_800).append advFree_ok_1200
  exact h

end

end LeanVM.Guest.Memory
