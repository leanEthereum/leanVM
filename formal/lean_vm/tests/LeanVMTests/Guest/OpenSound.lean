import LeanVM.Guest.B1.Whir.Verify
import LeanVM.Guest.B1.Eq.RsEqRun
import LeanVM.Guest.B1.Eq.RsRowsAll
import LeanVM.Guest.B1.Eq.RingRows
import LeanVM.Guest.B1.Ring.Target
import LeanVM.Guest.B1.Ring.Cols

/-!
# The stacked opening in the circuit, pinned

`open_stacked`'s soundness at every stack size and rate (`LeanVM.Guest.B1.Whir.open_stacked_sound_w`) and
its run of `verifyWhir` (`open_stacked_verifyWhir`), and the meanings of `ring_switch_target`, `ring_cols`,
`rs_eq_run`, `rs_eq_rows_all` and `ring_rows`, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.Whir.open_stacked_sound_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.open_stacked_sound_w

/-- info: 'LeanVM.Guest.B1.VerifySub.ring_switch_target_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.ring_switch_target_holds

/-- info: 'LeanVM.Guest.B1.VerifySub.ring_cols_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.ring_cols_holds

/-- info: 'LeanVM.Guest.B1.Whir.open_stacked_verifyWhir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.open_stacked_verifyWhir

/-- info: 'LeanVM.Guest.B1.rs_eq_run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.rs_eq_run_sound

/-- info: 'LeanVM.Guest.B1.rs_eq_rows_all_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.rs_eq_rows_all_holds

/-- info: 'LeanVM.Guest.B1.ring_rows_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.ring_rows_sound
