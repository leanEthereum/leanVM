import LeanVM.Guest.Complete.Open

/-!
# The end composition, pinned

`GuestExecutionComplete` from the packages' statements (`GuestOpen`), and its glue, on Lean's
three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_open

/-- info: 'LeanVM.Guest.Complete.ref_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.ref_of_open

/-- info: 'LeanVM.Guest.Complete.bounds_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.bounds_main

/-- info: 'LeanVM.Guest.Complete.run_jumpTables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.run_jumpTables

/-- info: 'LeanVM.Guest.Memory.pops_retempA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.pops_retempA

/-- info: 'LeanVM.Guest.Complete.fits_deployed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.fits_deployed

/-- info: 'LeanVM.Guest.Complete.deployed_above_checker' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.deployed_above_checker

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_rest
