/-
  LeanVM.Guest.Memory.AdvFreeOk0

  `advFreeChk` on functions 0 to 24, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_0 : RangeOk advFreeChk 0 25 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
