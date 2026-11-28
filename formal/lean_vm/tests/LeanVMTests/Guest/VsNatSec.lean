import LeanVM.Guest.B1.VsC.VsNatSec

/-!
# The link section's runs at the honest context, pinned

On Lean's three axioms (the kernel's checks on two of them).
-/

/-- info: 'LeanVM.Guest.B1.Link.Arith.chkRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.chkRun_sound

/-- info: 'LeanVM.Guest.B1.Link.Arith.exec_evalG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.exec_evalG

/-- info: 'LeanVM.Guest.B1.Link.Arith.linkSecStatementRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.linkSecStatementRun

/-- info: 'LeanVM.Guest.B1.VsC.linkSec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.linkSec_eq

/-- info: 'LeanVM.Guest.B1.VsC.vsStores_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsStores_ok

/-- info: 'LeanVM.Guest.B1.VsC.chkRun_runP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chkRun_runP

/-- info: 'LeanVM.Guest.B1.VsC.chkRun_runR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chkRun_runR

/-- info: 'LeanVM.Guest.B1.VsC.linkSecRuns_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.linkSecRuns_of_good

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.rd0_runNe_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.rd0_runNe_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.store573' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.store573

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.linkSecAtoms_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.linkSecAtoms_honest

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.cells19_σ0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.cells19_σ0

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.linkSecVals_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.linkSecVals_of_runs
