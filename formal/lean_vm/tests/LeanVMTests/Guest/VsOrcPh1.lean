import LeanVM.Guest.B1.VsC.VsOrcFront2
import LeanVM.Guest.B1.VsC.VsOrcPh1
import LeanVM.Guest.B1.VsC.VsOrcPh46

/-!
# `verify_sub`'s front and first `wC` phases at the honest oracle, pinned

`VsOrcFront2.lean` (vsph1): `FrontHyp`'s oracle, memory and cell fields at `vsW`. `VsOrcPh1.lean`: `FrontS`.
`VsOrcPh46.lean`: `Ph4to6S`. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.frontHyp_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.frontHyp_honest

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_409_of_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_409_of_front

/-- info: 'LeanVM.Guest.B1.VsC.frontS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.frontS_of

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.pre_rd0F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.pre_rd0F

/-- info: 'LeanVM.Guest.B1.VsC.frontS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.frontS

/-- info: 'LeanVM.Guest.B1.VsC.ph4to6S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph4to6S

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.Bnd.ph46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.Bnd.ph46

/-- info: 'LeanVM.Guest.B1.VsC.announced_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.announced_build

/-- info: 'LeanVM.Guest.B1.VsC.vsPk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPk

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.st0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.st0_eq
