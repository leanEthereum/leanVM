import LeanVM.Guest.Budget.Runs

/-!
# The guest's count by a node's items, pinned

The words, rows and weighted rows against the deployed and a corrected budget, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Budget.deployed_budget_ofWitness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.deployed_budget_ofWitness

/-- info: 'LeanVM.Guest.Budget.nodeWords_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.nodeWords_le

/-- info: 'LeanVM.Guest.Budget.nodeRows_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.nodeRows_lt

/-- info: 'LeanVM.Guest.Budget.nodeWeighted_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.nodeWeighted_le

/-- info: 'LeanVM.Guest.Budget.childWords_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.childWords_eq

/-- info: 'LeanVM.Guest.Budget.childWords_le_corrected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.childWords_le_corrected

/-- info: 'LeanVM.Guest.Budget.childWords_corrected_attained' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.childWords_corrected_attained

/-- info: 'LeanVM.Guest.Budget.childRows_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.childRows_le

/-- info: 'LeanVM.Guest.Budget.childWeighted_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.childWeighted_le

/-- info: 'LeanVM.Guest.Budget.corrected_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.corrected_bounds

/-- info: 'LeanVM.Guest.Budget.declaredFit_of_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.declaredFit_of_held
