module

public import NativeRustcArm.WotsLeaf

/-! # `wots_leaf`'s theorem uses Lean's three axioms only -/

/--
info: 'NativeRustcArm.WotsLeaf.wotsLeaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.WotsLeaf.wotsLeaf_spec
