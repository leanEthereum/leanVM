import LeanVM.Guest.B1.VsC.EqChainA
import LeanVM.Guest.B1.VsC.RingRowsA

/-!
# `check_stack_terminal`'s callees placed, pinned

`eq_prefix_chain`, `rs_eq_rows`, `rs_eq_run` and its loop, `ring_rows` and its loop. On Lean's three
axioms. (Apart from `VsC8.lean`: `RsRunA` imports `LinkCallees`, whose `lrs_complete` clashes with
`SlowC`'s, which `VsC8.lean` imports.)
-/

/-- info: 'LeanVM.Guest.B1.VsC.eq_prefix_chain_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.eq_prefix_chain_placed

/-- info: 'LeanVM.Guest.B1.VsC.rs_eq_rows_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rs_eq_rows_placed

/-- info: 'LeanVM.Guest.B1.VsC.rrl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rrl_placed

/-- info: 'LeanVM.Guest.B1.VsC.rs_eq_run_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rs_eq_run_placed

/-- info: 'LeanVM.Guest.B1.VsC.rrg_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rrg_placed

/-- info: 'LeanVM.Guest.B1.VsC.ring_rows_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ring_rows_placed
