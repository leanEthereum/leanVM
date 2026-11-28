import LeanVM.Guest.B1.VsC.VsOrcPh1011
import LeanVM.Guest.B1.VsC.VsOrcBnd
import LeanVM.Guest.B1.VsC.VsOrcPh711

/-!
# The honest phases `Ph7` to `Ph11` and the quiet boundary, pinned

vsph2's pieces (`VsOrcPhC.lean`, `VsOrcPh7.lean` … `VsOrcPh1011.lean`, `VsOrcBnd.lean`, `VsOrcPh711.lean`). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.eqLevels_lev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.eqLevels_lev

/-- info: 'LeanVM.Guest.B1.VsC.ptrRegion_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ptrRegion_idx

/-- info: 'LeanVM.Guest.B1.VsC.ptrsBelow_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ptrsBelow_idx

/-- info: 'LeanVM.Guest.B1.VsC.loadsInA_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.loadsInA_addr

/-- info: 'LeanVM.Guest.B1.VsC.hintsIn_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.hintsIn_addr

/-- info: 'LeanVM.Guest.B1.VsC.CallAtA.addrR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CallAtA.addrR

/-- info: 'LeanVM.Guest.B1.VsC.CallAtA.idxR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CallAtA.idxR

/-- info: 'LeanVM.Guest.B1.VsC.vsW_retC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_retC

/-- info: 'LeanVM.Guest.B1.VsC.chainLast_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chainLast_ne

/-- info: 'LeanVM.Guest.B1.VsC.vsW_rets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_rets

/-- info: 'LeanVM.Guest.B1.VsC.ph7Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.arraysApart3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.arraysApart3

/-- info: 'LeanVM.Guest.B1.VsC.ph8Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph8Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.vsPsH_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPsH_quiet

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.Bnd.quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.Bnd.quiet

/-- info: 'LeanVM.Guest.B1.VsC.ph9Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph9Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.ph10Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph10Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.ph11Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph11Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bufAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bufAt

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.mem_Wo2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.mem_Wo2

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.nums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.nums

/-- info: 'LeanVM.Guest.B1.VsC.ph7_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7_of

/-- info: 'LeanVM.Guest.B1.VsC.ph8_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph8_of

/-- info: 'LeanVM.Guest.B1.VsC.ph9_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph9_of

/-- info: 'LeanVM.Guest.B1.VsC.ph10_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph10_of

/-- info: 'LeanVM.Guest.B1.VsC.ph11_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph11_of

/-- info: 'LeanVM.Guest.B1.VsC.ph7to11S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph7to11S
