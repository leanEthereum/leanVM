import LeanVM.Guest.Complete.HandKids

/-!
# `main`'s hand facts but the loop's, pinned

`Complete/HandKids.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.main_kids_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_kids_hand

/-- info: 'LeanVM.Guest.Complete.mainHand_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainHand_of

/-- info: 'LeanVM.Guest.Complete.claimThenHand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.claimThenHand

/-- info: 'LeanVM.Guest.Complete.mainHand_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainHand_of_loop
