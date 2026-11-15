/-
  LeanVM.Guest.EndExecAGaps

  The allocation track's facts on the deployed alignment, assembled.
-/

module

public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.EndExecAWr
public import LeanVM.Guest.EndExecAExcl
public import LeanVM.Guest.EndExecHeap

/-!
# The allocation track's facts, all proved

`allocGaps_guest : AllocGaps`: the callee frames' pointers and sizes, `framePtr_alignA` and
`frameSize_alignA`, the dynamic sizes' powers, `dynPow_guest`, the advised sizes, `advNext_alignA`, on the
`heap_sizes` stream the reference tree's (`heapPops_ref`), the late hints, `lateReady_alignA`, and the
excluded function's buffer and late hint, `exclReady_alignA` and `lateExcl_guest`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest.Bridge (alignA)

public section

theorem allocGaps_guest : AllocGaps :=
  ⟨dynPow_guest, advNext_alignA, lateReady_alignA lateExcl_guest, frameSize_alignA, framePtr_alignA,
    exclReady_alignA⟩

theorem allocReady_guest : AllocReady alignA := allocGaps_guest.allocReady

theorem sizesAt_guest : SizesAt alignA := allocGaps_guest.sizesAt

/-- **Each step keeps `YAlloc alignA`.** -/
theorem keepY_allocA_guest : KeepY (YAlloc alignA) := keepY_allocA_of sizesAt_guest heapPops_ref

end

end LeanVM.Guest.EndExec
