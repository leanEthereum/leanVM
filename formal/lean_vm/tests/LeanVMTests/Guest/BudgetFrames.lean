import LeanVM.Guest.Complete.WithinCount
import LeanVM.Guest.Complete.Left

/-!
# The count's frames and `main`'s end, pinned

b2c's frame sizes within the certificates' on functions (not everywhere), the bounds with that
hypothesis, `main`'s end within the count below `2^63` and vacuous above, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Budget.cost_mono_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.cost_mono_valid

/-- info: 'LeanVM.Guest.Budget.wordsA_le_of_cost_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.wordsA_le_of_cost_v

/-- info: 'LeanVM.Guest.Budget.checker_bounds_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checker_bounds_v

/-- info: 'LeanVM.Guest.Budget.checkerZero_bounds_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checkerZero_bounds_v

/-- info: 'LeanVM.Guest.Budget.fs_eq_fsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.fs_eq_fsW

/-- info: 'LeanVM.Guest.Budget.fs_within_fsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.fs_within_fsW

/-- info: 'LeanVM.Guest.Budget.not_fs_le_fsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.not_fs_le_fsW

/-- info: 'LeanVM.Guest.Complete.callAtA_main_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_main_vacuous

/-- info: 'LeanVM.Guest.Complete.end_le_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.end_le_of_count

/-- info: 'LeanVM.Guest.Complete.within_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.within_deployed

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_left
