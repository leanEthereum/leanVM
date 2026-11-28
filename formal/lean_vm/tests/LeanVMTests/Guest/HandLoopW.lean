import LeanVM.Guest.Complete.HandLoopW

/-!
# `main`'s words and cycle hand facts, pinned

`Complete/HandLoopW.lean`, on Lean's three axioms (a subset of them): `GuestLeft.hand` and `GuestLeft.cycles`.
-/

/-- info: 'LeanVM.Guest.Complete.loopHand_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopHand_all

/-- info: 'LeanVM.Guest.Complete.mainHand_alW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainHand_alW

/-- info: 'LeanVM.Guest.Complete.mainCycles_alW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCycles_alW
