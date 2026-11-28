import LeanVM.Guest.Complete.RawS
import LeanVM.Guest.Complete.RawX

/-!
# The raw leanSPHINCS signatures' completeness, pinned

`verify_sig_lean_sphincs` and `sp_wots` complete taking no words of their own, popping the
signature's entries, every node exact; `main_loop3` and `main_loop2` complete from every counter. Lean's three
axioms.
-/

/-- info: 'LeanVM.Guest.Memory.sp_wots_exactFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.sp_wots_exactFree

/-- info: 'LeanVM.Guest.B1.Sig.sNode_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Sig.sNode_exact

/-- info: 'LeanVM.Guest.Complete.CallCompletes0.toCallCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.CallCompletes0.toCallCompletes

/-- info: 'LeanVM.Guest.Complete.callCompletes0_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletes0_node

/-- info: 'LeanVM.Guest.Complete.sp_wots_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.sp_wots_completes

/-- info: 'LeanVM.Guest.Complete.verify_sig_lean_sphincs_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.verify_sig_lean_sphincs_completes

/-- info: 'LeanVM.Guest.Complete.main_loop3_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_loop3_completes

/-- info: 'LeanVM.Guest.Memory.main_loop2_exactFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.main_loop2_exactFree

/-- info: 'LeanVM.Guest.Complete.main_loop2_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_loop2_completes
