import LeanVM.Guest.CoreMode.HeapCSound

/-!
# The heap check's point witnesses, pinned

A run's points (`runOkP`), the cells past a word (`ptsW`, `ptrPts`) and a signature's cells (`reqP`) take a `der`
witness (`ptOkD`), its own run's points `ptOk`'s; the check stays sound (`heapOkC_sound`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.CoreMode.runOkP_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.runOkP_ok

/-- info: 'LeanVM.Guest.CoreMode.ptOkD_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.ptOkD_ok

/-- info: 'LeanVM.Guest.CoreMode.runOk_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.runOk_ok

/-- info: 'LeanVM.Guest.CoreMode.ptsW_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.ptsW_ok

/-- info: 'LeanVM.Guest.CoreMode.reqP_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.reqP_ok

/-- info: 'LeanVM.Guest.CoreMode.ptrPts_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.ptrPts_ok

/-- info: 'LeanVM.Guest.CoreMode.runOkD_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.runOkD_ok

/-- info: 'LeanVM.Guest.CoreMode.reqS_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.reqS_ok

/-- info: 'LeanVM.Guest.CoreMode.heapOkC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.heapOkC_sound
