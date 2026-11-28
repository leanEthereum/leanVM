import LeanVM.Guest.Complete.RefFramesCore

/-!
# The reference run's frames, pinned

`Ref.Ok`'s `frames` and `aligned` on a reference run of the honest tree that is a valid execution
(`refFrames_of`), from the tree track with the jump cells stated without `r.Ok` (`JumpCellsV`), and
its data facts on the deployed guest (`lastSelf_core`, `loopFsAl_core`, `kecAl_core`), on Lean's three
axioms.
-/

/-- info: 'LeanVM.Guest.EndExec.refFrames_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.refFrames_of

/-- info: 'LeanVM.Guest.EndExec.refFrames_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.refFrames_core

/-- info: 'LeanVM.Guest.EndExec.lastSelf_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.lastSelf_core

/-- info: 'LeanVM.Guest.EndExec.loopFsAl_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.loopFsAl_core

/-- info: 'LeanVM.Guest.EndExec.kecAl_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.kecAl_core

/-- info: 'LeanVM.Guest.Memory.instsA_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.instsA_al

/-- info: 'LeanVM.Guest.EndExec.JumpCellsV.toAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.JumpCellsV.toAt
