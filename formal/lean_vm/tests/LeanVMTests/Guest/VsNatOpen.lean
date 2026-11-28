import LeanVM.Guest.B1.VsC.VsNatOpen
import LeanVM.Guest.B1.VsC.VsNatOpenCtx

/-!
# The run to its end, natively, pinned

On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.runSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runSteps

/-- info: 'LeanVM.Guest.B1.VsC.queryStepsOf_bind'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.queryStepsOf_bind'

/-- info: 'LeanVM.Guest.B1.VsC.runId_bind_q' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runId_bind_q

/-- info: 'LeanVM.Guest.B1.VsC.qstT_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.qstT_frame

/-- info: 'LeanVM.Guest.B1.VsC.noPacked_recordQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.noPacked_recordQueries

/-- info: 'LeanVM.Guest.B1.VsC.endsAny_whirOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.endsAny_whirOpen

/-- info: 'LeanVM.Guest.B1.VsC.runTc_commitStack_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runTc_commitStack_roots

/-- info: 'LeanVM.Guest.B1.VsC.natFront_at'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natFront_at'

/-- info: 'LeanVM.Guest.B1.VsC.runsTo_ringSwitch2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runsTo_ringSwitch2

/-- info: 'LeanVM.Guest.B1.VsC.natMemoryTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natMemoryTerm

/-- info: 'LeanVM.Guest.B1.VsC.runTc_bindPublicInput_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runTc_bindPublicInput_val

/-- info: 'LeanVM.Guest.B1.VsC.natVSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natVSO

/-- info: 'LeanVM.Guest.B1.VsC.openRunQueries_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openRunQueries_of

/-- info: 'LeanVM.Guest.B1.VsC.childQueries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.childQueries_eq

/-- info: 'LeanVM.Guest.B1.VsC.natOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.natOpen

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.hsid_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.hsid_nat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.hos_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.hos_nat
