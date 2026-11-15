/-
  LeanVM.Guest.EndExecAGaps

  What the allocation track still rests on, after the callee frames' pointers and sizes.
-/

module

public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.EndExecAWr
public import LeanVM.Guest.EndExecAExcl
public import LeanVM.Guest.EndExecHeap

/-!
# The allocation track's open facts

`AllocOpen.gaps : AllocOpen → AllocGaps`: `AllocGaps`' callee frame facts are proved,
`framePtr_alignA` and `frameSize_alignA`, the latter but for the frame hints the sizes check skips
(`FrSkip`), the dynamic sizes' powers, `dynPow_guest`, and the advised sizes, `advNext_alignA`, on the
`heap_sizes` stream the reference tree's (`heapPops_ref`), the late hints, `lateReady_alignA`, and the
excluded function's buffer and late hint, `exclReady_alignA` and `lateExcl_guest`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest.Bridge (alignA)

public section

/-- **What the allocation track rests on and does not prove**, on the deployed alignment. -/
structure AllocOpen : Prop where
  frSkip : FrSkip

theorem AllocOpen.gaps (G : AllocOpen) : AllocGaps :=
  ⟨dynPow_guest, advNext_alignA, lateReady_alignA lateExcl_guest, frameSize_alignA G.frSkip, framePtr_alignA,
    exclReady_alignA⟩

theorem AllocOpen.allocReady (G : AllocOpen) : AllocReady alignA := G.gaps.allocReady

theorem AllocOpen.sizesAt (G : AllocOpen) : SizesAt alignA := G.gaps.sizesAt

/-- **Each step keeps `YAlloc alignA`.** -/
theorem AllocOpen.keep (G : AllocOpen) : KeepY (YAlloc alignA) := keepY_allocA_of G.sizesAt heapPops_ref

end

end LeanVM.Guest.EndExec
