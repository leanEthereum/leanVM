import LeanVM.Guest.EndExecAGaps
import LeanVM.Guest.EndExecAGapsChk
import LeanVM.Guest.Bridge.FrAl
import LeanVM.Guest.Bridge.AddrChk
import LeanVM.Guest.EndExecAAddr
import LeanVM.Guest.EndExecAStat
import LeanVM.Guest.EndExecABuf
import LeanVM.Guest.EndExecAFrame
import LeanVM.Guest.EndExecAFrSize
import LeanVM.Guest.EndExecAFrHint

/-!
# The allocation track, pinned

`allocTrack_of`, `allocTrack_ofCur` and `curArith_of` (the allocation track's obligations at the bump pointer's track `YAlloc`, from
`MainA`, `SizesAt`, `CurArith` and `AllocReady`), `ExecGaps.ofHintsA`, and their parts, on Lean's
three axioms.
-/

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofHintsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofHintsA

/-- info: 'LeanVM.Guest.EndExec.allocTrack_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocTrack_of

/-- info: 'LeanVM.Guest.EndExec.keepY_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.keepY_alloc

/-- info: 'LeanVM.Guest.EndExec.hintAllocW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.hintAllocW_of

/-- info: 'LeanVM.Guest.EndExec.refTrack_mainA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.refTrack_mainA

/-- info: 'LeanVM.Guest.Memory.hints_nextFreeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.hints_nextFreeA

/-- info: 'LeanVM.Guest.Memory.instsA_kid_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.instsA_kid_pos

/-- info: 'LeanVM.Guest.Memory.endCurA_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.endCurA_ret

/-- info: 'LeanVM.Guest.Memory.endCurA_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.endCurA_tail

/-- info: 'LeanVM.Guest.Memory.kid_posA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.kid_posA

/-- info: 'LeanVM.Guest.EndExec.curArith_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.curArith_of

/-- info: 'LeanVM.Guest.EndExec.allocTrack_ofCur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocTrack_ofCur

/-- info: 'LeanVM.Guest.EndExec.cursor_stepA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.cursor_stepA

/-- info: 'LeanVM.Guest.Bridge.stepRule_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.stepRule_off

/-- info: 'LeanVM.Guest.EndExec.allocTrack_ofReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocTrack_ofReady

/-- info: 'LeanVM.Guest.EndExec.sizesAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.sizesAt_of

/-- info: 'LeanVM.Guest.EndExec.allocReady_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocReady_of

/-- info: 'LeanVM.Guest.EndExec.mainA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.mainA_of

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofHintsAlloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofHintsAlloc

/-- info: 'LeanVM.Guest.EndExec.allocTrack_ofHint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocTrack_ofHint

/-- info: 'LeanVM.Guest.EndExec.endCurA_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.endCurA_chain

/-- info: 'LeanVM.Guest.EndExec.allocB_of_bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allocB_of_bump

/-- info: 'LeanVM.Guest.EndExec.curHyps_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.curHyps_of

/-- info: 'LeanVM.Guest.Bridge.curFactsX_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.curFactsX_of

/-- info: 'LeanVM.Guest.Bridge.loopX_notLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.loopX_notLast

/-- info: 'LeanVM.Guest.EndExec.instsA_bufsOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.instsA_bufsOk

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofHintsAllocChk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofHintsAllocChk

/-- info: 'LeanVM.Guest.Bridge.frAl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.frAl_of

/-- info: 'LeanVM.Guest.Bridge.frAl_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.frAl_dispatch

/-- info: 'LeanVM.Guest.Bridge.allocFnJ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.allocFnJ_of

/-- info: 'LeanVM.Guest.Bridge.allocFnChk_alignA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.allocFnChk_alignA

/-- info: 'LeanVM.Guest.Bridge.addrFnJ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.addrFnJ_of

/-- info: 'LeanVM.Guest.Bridge.addrFnChk_alignA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.addrFnChk_alignA

/-- info: 'LeanVM.Guest.EndExec.addrReady_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.addrReady_of

/-- info: 'LeanVM.Guest.EndExec.addrTail_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.addrTail_of

/-- info: 'LeanVM.Guest.EndExec.addrStat_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.addrStat_of

/-- info: 'LeanVM.Guest.EndExec.bufHint_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.bufHint_of

/-- info: 'LeanVM.Guest.EndExec.cellRefB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.cellRefB

/-- info: 'LeanVM.Guest.EndExec.bufAtomB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.bufAtomB

/-- info: 'LeanVM.Guest.Bridge.allocShape_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.allocShape_walk

/-- info: 'LeanVM.Guest.Bridge.pairsB_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.pairsB_get

/-- info: 'LeanVM.Guest.Bridge.bufFnChk_alignA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.bufFnChk_alignA

/-- info: 'LeanVM.Guest.Bridge.bufsOf_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.bufsOf_idx

/-- info: 'LeanVM.Guest.EndExec.frame_nextA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.frame_nextA

/-- info: 'LeanVM.Guest.EndExec.site_nextA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.site_nextA

/-- info: 'LeanVM.Guest.EndExec.reach_jumpA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.reach_jumpA

/-- info: 'LeanVM.Guest.EndExec.frameSize_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.frameSize_of

/-- info: 'LeanVM.Guest.EndExec.frame_memA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.frame_memA

/-- info: 'LeanVM.Guest.EndExec.cellRefN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.cellRefN

/-- info: 'LeanVM.Guest.EndExec.allBufs_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.allBufs_of_frame

/-- info: 'LeanVM.Guest.EndExec.callee_in_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.callee_in_site

/-- info: 'LeanVM.Guest.EndExec.frameHint_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.frameHint_of

/-- info: 'LeanVM.Guest.Bridge.frFnJ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.frFnJ_of

/-- info: 'LeanVM.Guest.Bridge.frFnChk_alignA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.frFnChk_alignA

/-- info: 'LeanVM.Guest.Bridge.frAlJ_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.frAlJ_of
