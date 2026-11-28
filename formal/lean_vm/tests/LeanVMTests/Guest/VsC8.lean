import LeanVM.Guest.B1.VsC.ColSelCAll
import LeanVM.Guest.B1.VsC.LeafA
import LeanVM.Guest.B1.VsC.SelTablesA
import LeanVM.Guest.B1.VsC.ColSelA
import LeanVM.Guest.B1.VsC.RsRowsAllA
import LeanVM.Guest.B1.VsC.Vsc8CalleesA
import LeanVM.Guest.B1.VsC.StkSelA
import LeanVM.Guest.B1.VsC.RstA
import LeanVM.Guest.B1.VsC.AsgA
import LeanVM.Guest.B1.VsC.Log2A
import LeanVM.Guest.B1.VsC.CertifyA
import LeanVM.Guest.B1.VsC.RingColsA

/-!
# The stack selectors' callees, complete, pinned

`column_selector`, every specialization, in `CallCompletes0` form. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.csel_complete0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.csel_complete0

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes0_straight_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes0_straight_ex

/-- info: 'LeanVM.Guest.B1.VsC.column_selector_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.column_selector_complete

/-- info: 'LeanVM.Guest.B1.VsC.callAtA_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callAtA_leaf

/-- info: 'LeanVM.Guest.B1.VsC.callAtA_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callAtA_fwd

/-- info: 'LeanVM.Guest.B1.VsC.selector_tables_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.selector_tables_placed

/-- info: 'LeanVM.Guest.B1.VsC.callAtA_straight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callAtA_straight

/-- info: 'LeanVM.Guest.B1.VsC.column_selector_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.column_selector_placed

/-- info: 'LeanVM.Guest.B1.VsC.rs_eq_rows_all_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rs_eq_rows_all_placed

/-- info: 'LeanVM.Guest.B1.VsC.stack_selectors_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.stack_selectors_placed

/-- info: 'LeanVM.Guest.B1.VsC.rl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rl_placed

/-- info: 'LeanVM.Guest.B1.VsC.rst_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rst_completeA

/-- info: 'LeanVM.Guest.B1.VsC.rs_eq_rows_all_placed'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rs_eq_rows_all_placed'

/-- info: 'LeanVM.Guest.B1.VsC.asg_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.asg_placed

/-- info: 'LeanVM.Guest.B1.VsC.log2_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.log2_placed

/-- info: 'LeanVM.Guest.B1.VsC.cs_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cs_completeA

/-- info: 'LeanVM.Guest.B1.VsC.ring_cols_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ring_cols_placed
