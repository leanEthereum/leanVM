import LeanVM.Guest.Complete.WithinCount
import LeanVM.Guest.Complete.Left

/-!
# The callees' ends bounded, `main`'s end from them, pinned

The interface fix of `iface`: `main`'s callees end within `2^40` of their cursor below `2^60`
(`AtEveryB`, `VsCompleteHypA`), `main`'s window ends below `2^57` (`SegT`, `MainWindowAt`), and the count
bounds a placed `main` below `2^63` within `2^30` (`MainEndWithin`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.AtEveryB.toAtEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.AtEveryB.toAtEvery

/-- info: 'LeanVM.Guest.Complete.AtEveryB.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.AtEveryB.mono

/-- info: 'LeanVM.Guest.Complete.atEveryB_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.atEveryB_of_le

/-- info: 'LeanVM.Guest.Complete.end_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.end_step

/-- info: 'LeanVM.Guest.Complete.fs_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.fs_add_le

/-- info: 'LeanVM.Guest.Complete.loopBlock_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopBlock_add_le

/-- info: 'LeanVM.Guest.Complete.kidBlock_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidBlock_add_le

/-- info: 'LeanVM.Guest.Complete.segA_winsT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_winsT

/-- info: 'LeanVM.Guest.Complete.mCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mCalls_le

/-- info: 'LeanVM.Guest.Complete.mainWindowAt_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowAt_of_hyp

/-- info: 'LeanVM.Guest.Complete.mainWindowFromCallees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowFromCallees

/-- info: 'LeanVM.Guest.Complete.mainCompleteA_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCompleteA_of_window

/-- info: 'LeanVM.Guest.Complete.endWithin_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.endWithin_of_count

/-- info: 'LeanVM.Guest.Complete.within_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.within_deployed

/-- info: 'LeanVM.Guest.Complete.kidL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidL_callAtA

/-- info: 'LeanVM.Guest.Complete.mainDupx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainDupx

/-- info: 'LeanVM.Guest.B1.VsC.vsComplete_of_windowsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsComplete_of_windowsA

/-- info: 'LeanVM.Guest.B1.VsC.vsWindowsA_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindowsA_of_hyp

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_left
