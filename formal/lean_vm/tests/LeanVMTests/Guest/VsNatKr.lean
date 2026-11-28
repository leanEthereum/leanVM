import LeanVM.Guest.B1.VsC.VsNatKr

/-!
# The Keccak reduction's run at the honest context, pinned

On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.VkOs.vk_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VkOs.vk_shape

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.kec_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.kec_nat

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.kec_bufs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.kec_bufs
