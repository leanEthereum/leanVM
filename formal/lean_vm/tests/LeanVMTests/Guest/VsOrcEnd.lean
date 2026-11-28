import LeanVM.Guest.B1.VsC.VsOrcEnd
import LeanVM.Guest.B1.VsC.VsOrcBuf
import LeanVM.Guest.B1.VsC.VsOrcExport

/-!
# `verify_sub`'s end at the honest oracle, pinned

`VsOrcEnd.lean` (the final condition with the walk, `vsKEndW`, and its honest form), `VsOrcBuf.lean` (the buffers at the
honest oracle), `VsOrcExport.lean` (the export). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.vsWinHypW_of_orcW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWinHypW_of_orcW

/-- info: 'LeanVM.Guest.B1.VsC.vsWindowsFromCallees_of_orcW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindowsFromCallees_of_orcW

/-- info: 'LeanVM.Guest.B1.VsC.vsKEndW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsKEndW_of

/-- info: 'LeanVM.Guest.B1.VsC.gcWin_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.gcWin_low

/-- info: 'LeanVM.Guest.B1.VsC.gcWin_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.gcWin_top

/-- info: 'LeanVM.Guest.B1.VsC.vsHW_of_gcWin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsHW_of_gcWin

/-- info: 'LeanVM.Guest.B1.VsC.vsW_gcWin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_gcWin

/-- info: 'LeanVM.Guest.B1.VsC.vsKEndW_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsKEndW_honest

/-- info: 'LeanVM.Guest.B1.VsC.vsW_ptr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_ptr

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_fixed

/-- info: 'LeanVM.Guest.B1.VsC.vsOwn_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOwn_base

/-- info: 'LeanVM.Guest.B1.VsC.phExportOk_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.phExportOk_honest
