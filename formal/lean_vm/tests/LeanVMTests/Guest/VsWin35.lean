import LeanVM.Guest.B1.VsC.RingRun
import LeanVM.Guest.B1.VsC.VsPh35

/-!
# `wC`'s windows `35 ..< 38`, pinned

`verify_keccak`'s window, the ring switch's run (its grind and its three buffers) and `ring_switch_target`'s window
(`VsPh35.lean`), with the generic parts (`RingRun.lean`), on Lean's axioms only.
-/

/-- info: 'LeanVM.Guest.B1.VsC.ringCoefficients_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ringCoefficients_getD

/-- info: 'LeanVM.Guest.B1.VsC.rcBlock_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rcBlock_vals

/-- info: 'LeanVM.Guest.B1.VsC.rcStores_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rcStores_mem

/-- info: 'LeanVM.Guest.B1.VsC.rsStores_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rsStores_mem

/-- info: 'LeanVM.Guest.B1.VsC.runHyp_append0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runHyp_append0

/-- info: 'LeanVM.Guest.B1.VsC.runHyp_alloc_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runHyp_alloc_cons

/-- info: 'LeanVM.Guest.B1.VsC.vsPh35_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh35_wins
