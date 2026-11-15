/-
  LeanVM.Guest.Memory.AdvFreeOk350

  `advFreeChk` on functions 350 to 799, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_350 : RangeOk advFreeChk 350 450 := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
