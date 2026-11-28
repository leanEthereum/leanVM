import LeanVM.Guest.EndExecH

/-!
# The hint bridge's fields of `ExecGaps`, pinned

`ExecGaps.ofHints` (the hint fields and tracks from the bridge's premises and the allocation
track's obligations) and its parts, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofHints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofHints

/-- info: 'LeanVM.Guest.EndExec.hintWitness_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.hintWitness_cur

/-- info: 'LeanVM.Guest.EndExec.hintComputed_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.hintComputed_cur

/-- info: 'LeanVM.Guest.EndExec.hintsUsed_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.hintsUsed_cur

/-- info: 'LeanVM.Guest.EndExec.keepY_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.keepY_cur

/-- info: 'LeanVM.Guest.EndExec.initY_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.initY_cur

/-- info: 'LeanVM.Guest.EndExec.keepY_used' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.keepY_used

/-- info: 'LeanVM.Guest.EndExec.trackAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.trackAt

/-- info: 'LeanVM.Guest.EndExec.traceRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.traceRef

/-- info: 'LeanVM.Guest.EndExec.posAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.posAt
