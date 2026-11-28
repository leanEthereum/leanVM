import LeanVM.Guest.Memory.StaticSound
import LeanVM.Guest.Budget.HandVals

/-!
# The hand functions' virtual values, pinned

What each hand function's path fixes of its virtual values (`Budget/HandVals.lean`), on Lean's three axioms
(a subset of them).
-/

/-- info: 'LeanVM.Guest.Budget.every_pathHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.every_pathHolds

/-- info: 'LeanVM.Guest.Budget.squeeze_packed_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.squeeze_packed_vals

/-- info: 'LeanVM.Guest.Budget.rs_eq_run_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.rs_eq_run_vals

/-- info: 'LeanVM.Guest.Budget.ring_rows_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.ring_rows_vals

/-- info: 'LeanVM.Guest.Budget.link_rounds_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.link_rounds_vals

/-- info: 'LeanVM.Guest.Budget.claim_list_digest_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.claim_list_digest_vals

/-- info: 'LeanVM.Guest.Budget.child_claim_list_digest_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.child_claim_list_digest_vals

/-- info: 'LeanVM.Guest.Memory.hand_node_le_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.hand_node_le_same

/-- info: 'LeanVM.Guest.Memory.kidsValid_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.kidsValid_congr
