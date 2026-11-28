import LeanVM.Guest.B1.VsC.CalleesEnd

/-!
# `verify_sub`'s callees' ends, bounded, pinned

Every callee of `verify_sub` but `open_stacked` completes placed with its end within `2^β` of its
cursor, every frame below `2^16` (`CalleesB.lean`, `CalleesEnd.lean`). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.vsCalleesEndA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsCalleesEndA_complete

/-- info: 'LeanVM.Guest.B1.VsC.vsLinkCalleesAB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsLinkCalleesAB_of

/-- info: 'LeanVM.Guest.B1.VsC.cs_completeAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cs_completeAB

/-- info: 'LeanVM.Guest.B1.VsC.cst_completeAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cst_completeAB

/-- info: 'LeanVM.Guest.B1.VsC.rst_completeAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rst_completeAB

/-- info: 'LeanVM.Guest.B1.VerifySub.verifyKeccakCompleteAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.verifyKeccakCompleteAB

/-- info: 'LeanVM.Guest.B1.VerifySub.KL.keccakLayerCompleteA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.KL.keccakLayerCompleteA

/-- info: 'LeanVM.Guest.B1.VerifySub.VkData.eF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VkData.eF_le

/-- info: 'LeanVM.Guest.B1.VsC.stack_selectors_placedB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.stack_selectors_placedB

/-- info: 'LeanVM.Guest.B1.VsC.lr_main_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr_main_placed

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_completeA

/-- info: 'LeanVM.Guest.B1.VsC.link_terminal_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_terminal_completeA

/-- info: 'LeanVM.Guest.B1.VsC.VsCalleesEndA.toA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCalleesEndA.toA

/-- info: 'LeanVM.Guest.B1.VsC.vsCalleesEndA_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsCalleesEndA_b2c
