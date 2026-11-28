import LeanVM.Guest.Complete.BridgeB1
import LeanVM.Guest.Complete.TransferA
import LeanVM.Guest.Complete.ComposeA
import LeanVM.Guest.Complete.ComposeL

/-!
# `main`'s placed completeness to B2's premise, pinned

The aligned completeness of a call (`CallAtA`, `CallCompletesA`, its weakening and forgetting),
`MainB1` and the reference run's ISA side from `main`'s placed completeness, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.CallAtA.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.CallAtA.mono

/-- info: 'LeanVM.Guest.Complete.CallCompletesA.toCallCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.CallCompletesA.toCallCompletes

/-- info: 'LeanVM.Guest.Complete.mainB1_of_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainB1_of_callAtA

/-- info: 'LeanVM.Guest.Complete.refX_of_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.refX_of_callAtA

/-- info: 'LeanVM.Guest.Complete.mainB1_of_mainCompleteA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainB1_of_mainCompleteA

/-- info: 'LeanVM.Guest.Complete.callAtA_of_callCompletes0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_of_callCompletes0

/-- info: 'LeanVM.Guest.Complete.callCompletesA_of_callCompletes0_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletesA_of_callCompletes0_leaf

/-- info: 'LeanVM.Guest.Complete.kidsAtF_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsAtF_words

/-- info: 'LeanVM.Guest.Complete.callAtA_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_node

/-- info: 'LeanVM.Guest.Complete.kidsAtL_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsAtL_words

/-- info: 'LeanVM.Guest.Complete.callAtA_nodeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_nodeL
