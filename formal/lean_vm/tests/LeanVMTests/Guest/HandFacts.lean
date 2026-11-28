import LeanVM.Guest.Complete.HandFacts

/-!
# Path-local hand facts, pinned

`Complete/HandFacts.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.squeeze_packed_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.squeeze_packed_hand

/-- info: 'LeanVM.Guest.Complete.rs_eq_run_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.rs_eq_run_hand

/-- info: 'LeanVM.Guest.Complete.ring_rows_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.ring_rows_hand

/-- info: 'LeanVM.Guest.Complete.link_rounds_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.link_rounds_hand

