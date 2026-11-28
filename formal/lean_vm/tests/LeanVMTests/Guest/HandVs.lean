import LeanVM.Guest.Complete.HandVs

/-!
# `verify_sub`'s values and `main`'s cycles, pinned

`Complete/HandVs.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.vsVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.vsVals

/-- info: 'LeanVM.Guest.Complete.mainCycles_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCycles_all
