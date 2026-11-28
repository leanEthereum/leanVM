import LeanVM.Guest.B1.VsC.VsAvoid

/-!
# No fresh load of `verify_sub` reads the overlay's cells, pinned

On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.avoidAt_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.avoidAt_of_spec

/-- info: 'LeanVM.Guest.B1.VsC.spC_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.spC_ok

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.vsAvoid_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.vsAvoid_of_hyp

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.avoidHyp_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.avoidHyp_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.vsAvoid_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.vsAvoid_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.fresh_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.fresh_of
