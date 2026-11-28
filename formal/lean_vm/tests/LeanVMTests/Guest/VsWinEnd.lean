import LeanVM.Guest.B1.VsC.VsPhOpen
import LeanVM.Guest.B1.VsC.VsPost
import LeanVM.Guest.B1.VsC.VsPostE

/-!
# `verify_sub`'s last windows and its final condition, pinned

`wC`'s windows `38 ..< 43` (vswin11), `vsPostA` from the skeleton, its inputs on the honest run (vswin13). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_open

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_bound

/-- info: 'LeanVM.Guest.B1.VsC.vsPhOpen_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPhOpen_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsPhExport_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPhExport_wins

/-- info: 'LeanVM.Guest.B1.VsC.flat_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.flat_skel

/-- info: 'LeanVM.Guest.B1.VsC.ite_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ite_skel

/-- info: 'LeanVM.Guest.B1.VsC.vs_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_skel

/-- info: 'LeanVM.Guest.B1.VsC.vsPostA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPostA_of

/-- info: 'LeanVM.Guest.B1.VsC.vsWindowsA_of_hypW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindowsA_of_hypW

/-- info: 'LeanVM.Guest.B1.VsC.vs_skel_parts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_skel_parts

/-- info: 'LeanVM.Guest.B1.VsC.vs_kOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_kOk

/-- info: 'LeanVM.Guest.B1.VsC.vs_skelPops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_skelPops

/-- info: 'LeanVM.Guest.B1.VsC.vs_sameStreams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_sameStreams

/-- info: 'LeanVM.Guest.B1.VsC.vs_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_exact

/-- info: 'LeanVM.Guest.B1.VsC.vsXs_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsXs_exact

/-- info: 'LeanVM.Guest.B1.VsC.vsPostA_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPostA_final
