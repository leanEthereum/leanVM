module

public import NativeRustcX64.Hasher.Finalize

/-!
# The axioms of `Hasher::finalize`'s x86-64 proof

Lean's three.
-/

/--
info: 'NativeRustcX64.Hasher.Finalize.finalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.Hasher.Finalize.finalize_spec
