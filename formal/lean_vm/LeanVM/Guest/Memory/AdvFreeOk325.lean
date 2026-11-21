/-
  LeanVM.Guest.Memory.AdvFreeOk325

  `advFreeChk` on functions 325 to 349, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_325 : RangeOk advFreeChk 325 25 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
