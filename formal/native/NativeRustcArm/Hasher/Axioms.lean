module

public import NativeRustcArm.Hasher.Update
public import NativeRustcArm.Hasher.Finalize

/-!
# The axioms of `Hasher::update`'s and `Hasher::finalize`'s proofs

Lean's three.
-/

/--
info: 'NativeRustcArm.Hasher.Update.update_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.Hasher.Update.update_spec

/--
info: 'NativeRustcArm.Hasher.Finalize.finalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.Hasher.Finalize.finalize_spec
