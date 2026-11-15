/-
  LeanVM.Guest.EndExecAGaps

  What the allocation track still rests on, after the callee frames' pointers and sizes.
-/

module

public import LeanVM.Guest.EndExecAFrSize
public import LeanVM.Guest.EndExecADyn
public import LeanVM.Guest.EndExecAHeap

/-!
# The allocation track's open facts

`AllocOpen.gaps : AllocOpen → AllocGaps`: `AllocGaps`' callee frame facts are proved,
`framePtr_alignA` and `frameSize_alignA`, the latter but for the frame hints the sizes check skips
(`FrSkip`), the dynamic sizes' powers, `dynPow_guest`, and the advised sizes, `advNext_alignA`, on the
`heap_sizes` stream the reference tree's (`HeapPops`); the rest stays named.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest.Bridge (alignA)

public section

/-- **What the allocation track rests on and does not prove**, on the deployed alignment. -/
structure AllocOpen : Prop where
  heapPops : HeapPops
  late : LateReady alignA
  frSkip : FrSkip
  excl : ExclReady alignA

theorem AllocOpen.gaps (G : AllocOpen) : AllocGaps :=
  ⟨dynPow_guest, advNext_alignA, G.late, frameSize_alignA G.frSkip, framePtr_alignA, G.excl⟩

theorem AllocOpen.allocReady (G : AllocOpen) : AllocReady alignA := G.gaps.allocReady

theorem AllocOpen.sizesAt (G : AllocOpen) : SizesAt alignA := G.gaps.sizesAt

/-- **Each step keeps `YAlloc alignA`.** -/
theorem AllocOpen.keep (G : AllocOpen) : KeepY (YAlloc alignA) := keepY_allocA_of G.sizesAt G.heapPops

end

end LeanVM.Guest.EndExec
