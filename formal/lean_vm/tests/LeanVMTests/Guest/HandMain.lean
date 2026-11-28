import LeanVM.Guest.Complete.HandMain

/-!
# `main`'s own hand fact, pinned

The honest entries by stream and `main`'s values from its meta hint (`Complete/HandHonest.lean`,
`Complete/HandMain.lean`), on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.honest_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honest_mem

/-- info: 'LeanVM.Guest.Complete.main_meta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_meta

/-- info: 'LeanVM.Guest.Complete.main_hand_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_hand_own
