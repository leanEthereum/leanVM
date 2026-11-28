import LeanVM.Guest.Complete.HandDigest

/-!
# Hand facts from the pops, pinned

`Complete/HandDigest.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.da_verify_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_verify_hand

/-- info: 'LeanVM.Guest.Complete.claim_else_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.claim_else_hand

/-- info: 'LeanVM.Guest.Complete.list_split_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.list_split_in
