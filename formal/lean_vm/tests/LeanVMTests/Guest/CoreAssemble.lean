import LeanVM.Guest.EndExecAssemble

/-!
# The core route's certificates assembled, pinned

`ModeCerts` and `MainOk` from each certificate's facts, the functions off the route as a hypothesis, and
`ExecGaps` from the assembly, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Mode.modeCerts_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.modeCerts_of

/-- info: 'LeanVM.Guest.Mode.slots_guest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.slots_guest

/-- info: 'LeanVM.Guest.Mode.mainOk_guest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.mainOk_guest

/-- info: 'LeanVM.Guest.EndExec.assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.assemble

/-- info: 'LeanVM.Guest.EndExec.res_of_track' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.res_of_track

/-- info: 'LeanVM.Guest.EndExec.term_of_nodeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.term_of_nodeA

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofAssembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofAssembled
