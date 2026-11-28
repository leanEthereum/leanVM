import LeanVM.Guest.B2C.RefX

/-!
# B2's completeness, pinned

The reference run's ISA side for Hotwire's guest (`LeanVM.Guest.B2C.refX_exists`): on the honest
memory laid out by the aligned allocator, extended by the hints' heap words and the hint-only
values, a valid execution of the guest within the tree's opcode counts, from B1's facts about
`main`'s tree (`MainB1`) and the hint-only cells' freshness (`ExtraOk`), on Lean's three axioms;
with B2's completeness on any memory covering the honest writes (`b2_completeL`, `b2_countL`) from
the kernel-checked completeness checks (`b2Hyps`).
-/

/-- info: 'LeanVM.Guest.B2C.refX_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B2C.refX_exists

/-- info: 'LeanVM.Guest.B2C.b2Hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B2C.b2Hyps

/-- info: 'LeanVM.Guest.Memory.honestX_retempE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.honestX_retempE

/-- info: 'LeanVM.Guest.coreProgram_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.coreProgram_wf
