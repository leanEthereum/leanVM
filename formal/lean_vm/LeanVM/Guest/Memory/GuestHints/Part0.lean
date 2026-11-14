/-
  LeanVM.Guest.Memory.GuestHints.Part0

  A kernel check of `chkH` on a range of the guest's functions.
-/

module

public import LeanVM.Guest.Memory.GuestHints.Check

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

theorem hintsRange_0 : RangeOk chkH 0 36 := by
  unfold RangeOk; decide +kernel

end
end LeanVM.Guest.Memory
