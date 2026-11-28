import LeanVM.Guest.Complete.Committed
import LeanVM.Guest.Complete.Reduce

/-!
# The guest's execution completeness, reduced, pinned

The executor's `KECCAK` windows and `GuestExecutionComplete` from the guest's run within its bounds,
on Lean's three axioms.
-/

/-- info: 'LeanVM.Prover.Exec.execute_keccakBlocksInWindows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Exec.execute_keccakBlocksInWindows

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_runsWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_runsWithin

/-- info: 'LeanVM.Guest.Complete.committedOfRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.committedOfRows
