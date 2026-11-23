module

import NativeRustcX64.Hasher.Update

/-!
# The axioms of `Hasher::update`'s proof (x86-64)

`update_spec` depends on Lean's three axioms only.
-/

/--
info: 'NativeRustcX64.Hasher.Update.update_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.Hasher.Update.update_spec
