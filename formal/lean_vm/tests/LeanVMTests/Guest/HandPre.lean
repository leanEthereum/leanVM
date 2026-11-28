import LeanVM.Guest.Budget.HandPre
import LeanVM.Guest.Budget.HandSame

/-!
# Preconditions down a tree, and re-valuing off the path, pinned

`Budget/HandPre.lean`, `Budget/HandSame.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Budget.every_pathIn_preAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.every_pathIn_preAt

/-- info: 'LeanVM.Guest.Budget.sameOnPath_setVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.sameOnPath_setVals
