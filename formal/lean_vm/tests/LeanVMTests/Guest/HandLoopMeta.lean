import LeanVM.Guest.Complete.HandLoopMeta

/-!
# The loop's `child_meta` stream, pinned

`Complete/HandLoopMeta.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.loopMetaStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopMetaStream

/-- info: 'LeanVM.Guest.Complete.loopMeta_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopMeta_all

/-- info: 'LeanVM.Guest.Complete.honest_meta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honest_meta
