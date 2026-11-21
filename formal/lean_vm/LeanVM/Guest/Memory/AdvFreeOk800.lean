/-
  LeanVM.Guest.Memory.AdvFreeOk800

  `advFreeChk` on functions 800 to 1199, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_800 : RangeOk advFreeChk 800 400 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
