import LeanVM.Guest.Complete.DaVerify

/-!
# `da_verify`'s completeness, pinned

The cell check, the blob check and both loops, `da_pad`, and `da_verify` from its dual codeword's
builders' completeness. Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.da_vector_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_vector_free

/-- info: 'LeanVM.Guest.Complete.da_weights_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_weights_free

/-- info: 'LeanVM.Guest.Complete.da_verify_exactFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_verify_exactFree

/-- info: 'LeanVM.Guest.Complete.callCompletes0_straight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletes0_straight

/-- info: 'LeanVM.Guest.Complete.callCompletes_straight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletes_straight

/-- info: 'LeanVM.Guest.Complete.da_verify_cell_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_verify_cell_completes

/-- info: 'LeanVM.Guest.Complete.blob_loop_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.blob_loop_completes

/-- info: 'LeanVM.Guest.Complete.da_verify_blob_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_verify_blob_completes

/-- info: 'LeanVM.Guest.Complete.dv_loop_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dv_loop_completes

/-- info: 'LeanVM.Guest.Complete.da_pad_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_pad_completes

/-- info: 'LeanVM.Guest.Complete.weightsHold_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.weightsHold_of

/-- info: 'LeanVM.Guest.Complete.da_verify_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_verify_completes
