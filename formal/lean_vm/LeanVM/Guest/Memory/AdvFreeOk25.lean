/-
  LeanVM.Guest.Memory.AdvFreeOk25

  `advFreeChk` on functions 25 to 49, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_25 : RangeOk advFreeChk 25 25 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
