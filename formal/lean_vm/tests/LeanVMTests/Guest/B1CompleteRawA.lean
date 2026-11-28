import LeanVM.Guest.Complete.RawFields

/-!
# The raw signatures' loops placed, pinned

`main_loop2` and `main_loop3` complete with their shapes and placed at every frame and cursor;
`MainCalleesAt`'s fields `rawx` and `raws` on every node, for every coverage table holding the raw
signatures' marks. Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.l2_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.l2_facts

/-- info: 'LeanVM.Guest.Complete.l2_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.l2_atEvery

/-- info: 'LeanVM.Guest.Complete.l3_pureIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.l3_pureIn

/-- info: 'LeanVM.Guest.Complete.verify_sig_lean_sphincs_completesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.verify_sig_lean_sphincs_completesA

/-- info: 'LeanVM.Guest.Complete.l3_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.l3_atEvery

/-- info: 'LeanVM.Guest.Complete.rawx_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.rawx_field

/-- info: 'LeanVM.Guest.Complete.raws_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.raws_field

/-- info: 'LeanVM.Guest.Complete.rawMarks_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.rawMarks_of
