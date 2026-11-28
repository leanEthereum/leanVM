import LeanVM.Guest.B1.VsC.VsHonEcPf

/-!
# `verify_sub`'s pinned ends chosen at the honest context

On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.ecPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.ecPart

/-- info: 'LeanVM.Guest.B1.VsC.VsCalleesEndU.row_sideE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCalleesEndU.row_sideE

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.hend_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.hend_of_steps
