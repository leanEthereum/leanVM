/-
  LeanVM.Guest.EndExecAGaps

  The allocation track's facts on the deployed alignment, assembled.
-/

module

public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.EndExecAKeep
public import LeanVM.Guest.EndExecAReady

/-!
# The allocation track's facts, all proved

`allocGaps_guest : AllocGaps`: the callee frames' pointers and sizes, `framePtr_alignA` and
`frameSize_alignA`, and the dynamic sizes' powers, `dynPow_guest`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest.Bridge (alignA)

public section

theorem allocGaps_guest : AllocGaps := ⟨dynPow_guest, frameSize_alignA, framePtr_alignA⟩

theorem allocReady_guest : AllocReady alignA := allocGaps_guest.allocReady

theorem sizesAt_guest : SizesAt alignA := allocGaps_guest.sizesAt

/-- **Each step keeps `YAlloc alignA`.** -/
theorem keepY_allocA_guest : KeepY (YAlloc alignA) := keepY_allocA sizesAt_guest curArith_alignA

end

end LeanVM.Guest.EndExec
