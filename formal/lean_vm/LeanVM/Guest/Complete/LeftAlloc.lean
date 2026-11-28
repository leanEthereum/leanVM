/-
  LeanVM.Guest.Complete.LeftAlloc

  `GuestLeft`'s fields `dynPow` and `progOk`, at the deployed choices.
-/

module

public import LeanVM.Guest.Complete.Open
public import LeanVM.Guest.EndExecADynG

namespace LeanVM.Guest.Complete

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

/-- **`GuestLeft.dynPow`**: each dynamic buffer's size a power of `g`. -/
theorem dynPow_left : DynPowA (lay alW) (refD alW) := dynPowA_guest

end

end LeanVM.Guest.Complete
