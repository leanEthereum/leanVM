module

import NativeRustcX64.KeccakF.Spec

/-!
# The axioms of `keccak_f`'s proof (x86-64)

`keccakF_spec` depends on Lean's three axioms only.
-/

/--
info: 'NativeRustcX64.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.keccakF_spec
