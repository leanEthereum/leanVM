/-
  LeanVM.Guest.Memory.GuestHints.Part5

  A kernel check of `chkH` on a range of the guest's functions.
-/

module

public import LeanVM.Guest.Memory.GuestHints.Check

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

theorem hintsRange_1080 : RangeOk chkH 1080 260 := by
  unfold RangeOk; decide +kernel

end
end LeanVM.Guest.Memory
