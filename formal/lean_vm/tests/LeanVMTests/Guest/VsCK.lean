import LeanVM.Guest.B1.VsC.KRoundsAll
import LeanVM.Guest.B1.VsC.PlainA
import LeanVM.Guest.B1.VsC.CopyLoopA
import LeanVM.Guest.B1.VsC.KLMain
import LeanVM.Guest.B1.VsC.VkCF
import LeanVM.Guest.B1.VsC.VkCChain
import LeanVM.Guest.B1.VsC.VkPM

/-!
# `verify_keccak`'s callees, placed, pinned

`layer_rounds`, `keccak_plain_rounds` and the copy loops, placed. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.layer_rounds_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.layer_rounds_placed

/-- info: 'LeanVM.Guest.B1.VsC.lr_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr_placed

/-- info: 'LeanVM.Guest.B1.VsC.plain_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.plain_core

/-- info: 'LeanVM.Guest.B1.VsC.plain60_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.plain60_placed

/-- info: 'LeanVM.Guest.B1.VsC.plain41_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.plain41_placed

/-- info: 'LeanVM.Guest.B1.VsC.cl_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cl_loop

/-- info: 'LeanVM.Guest.B1.VsC.cl_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cl_shape

/-- info: 'LeanVM.Guest.B1.VsC.cl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cl_placed

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_body_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_body_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.pack_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.pack_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_walk

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_static

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_out

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_kids

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_σ0_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_σ0_calls

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.layer_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.layer_placed

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.keccakLayerCompleteA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.keccakLayerCompleteA

/-- info: 'LeanVM.Guest.B1.VerifySub.vkHead_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkHead_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.vkFirst_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkFirst_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.vkFin_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkFin_complete

/-- info: 'LeanVM.Guest.B1.Tables.pf_verifyKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Tables.pf_verifyKeccak

/-- info: 'LeanVM.Guest.B1.VerifySub.vkData_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkData_of_run

/-- info: 'LeanVM.Guest.B1.VerifySub.VkData.layer_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VkData.layer_facts

/-- info: 'LeanVM.Guest.B1.VerifySub.vkOut_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkOut_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.vkIn_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkIn_complete

/-- info: 'LeanVM.Guest.B1.VerifySub.vkFromLayerA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vkFromLayerA

/-- info: 'LeanVM.Guest.B1.VerifySub.verifyKeccakCompleteA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.verifyKeccakCompleteA

/-- info: 'LeanVM.Guest.B1.VerifySub.VkData.vk_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VkData.vk_kids

/-- info: 'LeanVM.Guest.B1.VerifySub.VkData.body_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VkData.body_holds
