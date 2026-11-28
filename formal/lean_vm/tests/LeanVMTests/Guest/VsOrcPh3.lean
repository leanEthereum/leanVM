import LeanVM.Guest.B1.VsC.VsOrcPh3Spec
import LeanVM.Guest.B1.VsC.VsOrcPh3Ctx

/-!
# `Ph12` to the end at the honest oracle, pinned

`VsOrcPh1213.lean`, `VsOrcPh35.lean`, `VsOrcPhOpen.lean`, `VsOrcPhEnd.lean`: the phases from the table points on, each from its honest inputs and its callees' completeness. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.ph1213Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph1213Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.ph35Ok_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph35Ok_in

/-- info: 'LeanVM.Guest.B1.VsC.phOpenOk_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.phOpenOk_in

/-- info: 'LeanVM.Guest.B1.VsC.openCall_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openCall_of

/-- info: 'LeanVM.Guest.B1.VsC.forall₂_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.forall₂_end

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.kEndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.kEndW

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.ptrL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.ptrL

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.bufAtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.bufAtL

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.phExportOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.phExportOk

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.kEndW_bw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.kEndW_bw


/-- info: 'LeanVM.Guest.B1.VsC.ph1213Ok_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph1213Ok_at

/-- info: 'LeanVM.Guest.B1.VsC.ph35Ok_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph35Ok_at

/-- info: 'LeanVM.Guest.B1.VsC.ph12toEndP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph12toEndP_of

/-- info: 'LeanVM.Guest.B1.VsC.ph1213In_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph1213In_ctx

/-- info: 'LeanVM.Guest.B1.VsC.ph35In_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph35In_ctx

/-- info: 'LeanVM.Guest.B1.VsC.phOpenIn_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.phOpenIn_ctx

/-- info: 'LeanVM.Guest.B1.VsC.endOk_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.endOk_ctx

/-- info: 'LeanVM.Guest.B1.VsC.ph12EndP_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph12EndP_ctx

/-- info: 'LeanVM.Guest.B1.VsC.ph12toEndP_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ph12toEndP_ctx
