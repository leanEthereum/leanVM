import LeanVM.Guest.Complete.Compose
import LeanVM.Guest.Complete.MainB1
import LeanVM.Guest.Complete.Limits
import LeanVM.Guest.B1.Sig.SphincsCompleteHolds
import LeanVM.Guest.B1.Sig.XmssSigPops
import LeanVM.Guest.B1.Da.LevelsComplete
import LeanVM.Guest.B1.Da.PaddingComplete

/-!
# The guest's B1 completeness outside `verify_sub`, pinned

The restored signature checks with their pops, the DA levels and padding, the limits and the
layout-free composition, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.GuestLimits.of_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.GuestLimits.of_deployed

/-- info: 'LeanVM.Guest.Complete.callCompletes_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletes_node

/-- info: 'LeanVM.Guest.B1.Sig.verify_lean_xmss_complete_pops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Sig.verify_lean_xmss_complete_pops

/-- info: 'LeanVM.Guest.B1.Sig.sphincs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Sig.sphincs_complete

/-- info: 'LeanVM.Guest.B1.Da.da_levels_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Da.da_levels_complete

/-- info: 'LeanVM.Guest.B1.Da.da_padding_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Da.da_padding_complete
