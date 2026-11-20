/-
  LeanVM.Guest.Memory.AdvFreeOk450

  `advFreeChk` on functions 450 to 574, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_450 : RangeOk advFreeChk 450 125 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
