import LeanVM.Guest.B1.VsC.OrcFix
import LeanVM.Guest.B1.VsC.VsOrc
import LeanVM.Guest.B1.VsC.VsOrcFront
import LeanVM.Guest.B1.VsC.VsOrcHonest
import LeanVM.Guest.B1.VsC.VsOrcTail
import LeanVM.Guest.B1.VsC.VsOrcSpec
import LeanVM.Guest.B1.VsC.VsOrcMem
import LeanVM.Guest.B1.VsC.CalleesA
import LeanVM.Guest.B1.VsC.VsOrcAllocs

/-!
# `verify_sub`'s windows by phase and the causal oracle, pinned

The per-phase skeleton (`VsOrc.lean`, `VsOrcTail.lean`), the causal fixpoint (`OrcFix.lean`) and the honest oracle's shared pieces (`VsOrcHonest.lean`). On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_causal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_causal

/-- info: 'LeanVM.Guest.B1.VsC.fixW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.fixW_eq

/-- info: 'LeanVM.Guest.B1.VsC.vsFix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsFix_eq

/-- info: 'LeanVM.Guest.B1.VsC.frontOk_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.frontOk_wins

/-- info: 'LeanVM.Guest.B1.VsC.wcOk_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wcOk_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsHyp_of_orc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsHyp_of_orc

/-- info: 'LeanVM.Guest.B1.VsC.vsWinHyp_of_orc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWinHyp_of_orc

/-- info: 'LeanVM.Guest.B1.VsC.vsWinHypFromCallees_of_orc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWinHypFromCallees_of_orc

/-- info: 'LeanVM.Guest.B1.VsC.frontNum_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.frontNum_of_child

/-- info: 'LeanVM.Guest.B1.VsC.ev_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ev_congr

/-- info: 'LeanVM.Guest.B1.VsC.vsEv_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsEv_congr

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_congr

/-- info: 'LeanVM.Guest.B1.VsC.fixW_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.fixW_congr

/-- info: 'LeanVM.Guest.B1.VsC.vsRule_causal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsRule_causal

/-- info: 'LeanVM.Guest.B1.VsC.vsW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_eq

/-- info: 'LeanVM.Guest.B1.VsC.vsW_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_alloc

/-- info: 'LeanVM.Guest.B1.VsC.vsW_42' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_42

/-- info: 'LeanVM.Guest.B1.VsC.vsW_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW_ret

/-- info: 'LeanVM.Guest.B1.VsC.tailOk_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tailOk_wins

/-- info: 'LeanVM.Guest.B1.VsC.WCOkT.wcOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.WCOkT.wcOk

/-- info: 'LeanVM.Guest.B1.VsC.vsPhases_of_specs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPhases_of_specs

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.lowDef_rd0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.lowDef_rd0

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.pre_rd0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.pre_rd0

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.holdsWords_rd0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.holdsWords_rd0

/-- info: 'LeanVM.Guest.B1.VsC.VsCtx.wordsInA_Wo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsCtx.wordsInA_Wo

/-- info: 'LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_specs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsOrcWFromCallees_of_specs

/-- info: 'LeanVM.Guest.B1.VsC.vsComplete_of_windowsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsComplete_of_windowsA

/-- info: 'LeanVM.Guest.B1.VsC.vsAllocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsAllocs
