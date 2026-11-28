import LeanVM.Guest.Complete.HandLoop

/-!
# The children's loop's counts and tools, pinned

`Complete/HandLoop.lean`, `Complete/HandLoopKit.lean`, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Complete.loopMeta_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopMeta_of

/-- info: 'LeanVM.Guest.Complete.child_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.child_hand

/-- info: 'LeanVM.Guest.Complete.loop_node_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loop_node_split

/-- info: 'LeanVM.Guest.Complete.loopRun_countT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopRun_countT
