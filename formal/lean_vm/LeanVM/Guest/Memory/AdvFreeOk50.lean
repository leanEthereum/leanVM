/-
  LeanVM.Guest.Memory.AdvFreeOk50

  `advFreeChk` on functions 50 to 324, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_50 : RangeOk advFreeChk 50 275 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
