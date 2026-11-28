import LeanVM.Guest.Budget.HandPops

/-!
# Values from the pops, pinned

Every node's path within the honest entries (`Budget/HandPops.lean`), on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Budget.every_pathIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.every_pathIn

/-- info: 'LeanVM.Guest.Budget.every_pathIn_of_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.every_pathIn_of_streams

/-- info: 'LeanVM.Guest.Budget.PathIn.pathHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.PathIn.pathHolds

/-- info: 'LeanVM.Guest.Budget.heap_words_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.heap_words_getD
