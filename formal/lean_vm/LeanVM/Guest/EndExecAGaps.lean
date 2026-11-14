/-
  LeanVM.Guest.EndExecAGaps

  What the allocation track still rests on, after the callee frames' pointers and sizes.
-/

module

public import LeanVM.Guest.EndExecAFrSize

/-!
# The allocation track's open facts

`AllocOpen.gaps : AllocOpen → AllocGaps`: `AllocGaps`' callee frame facts are proved,
`framePtr_alignA` and `frameSize_alignA`, the latter but for the frame hints the sizes check skips
(`FrSkip`); the rest stays named.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest.Bridge (alignA)

public section

/-- **What the allocation track rests on and does not prove**, on the deployed alignment. -/
structure AllocOpen : Prop where
  dynPow : DynPow
  advNext : AdvNext alignA
  late : LateReady alignA
  frSkip : FrSkip
  excl : ExclReady alignA

theorem AllocOpen.gaps (G : AllocOpen) : AllocGaps :=
  ⟨G.dynPow, G.advNext, G.late, frameSize_alignA G.frSkip, framePtr_alignA, G.excl⟩

theorem AllocOpen.allocReady (G : AllocOpen) : AllocReady alignA := G.gaps.allocReady

theorem AllocOpen.sizesAt (G : AllocOpen) : SizesAt alignA := G.gaps.sizesAt

end

end LeanVM.Guest.EndExec
