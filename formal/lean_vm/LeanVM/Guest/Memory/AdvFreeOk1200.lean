/-
  LeanVM.Guest.Memory.AdvFreeOk1200

  `advFreeChk` on functions 1200 to 1600, by the kernel.
-/

module

public import LeanVM.Guest.Memory.AdvFree

namespace LeanVM.Guest.Memory

public section

theorem advFree_ok_1200 : RangeOk advFreeChk 1200 (core_count% - 1200) := by unfold RangeOk; decide +kernel

end

end LeanVM.Guest.Memory
