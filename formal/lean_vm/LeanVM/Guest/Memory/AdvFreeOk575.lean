/-
  LeanVM.Guest.Memory.AdvFreeOk575

  `advFreeChk` on functions 575 to 799, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_575 : RangeOk advFreeChk 575 225 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
