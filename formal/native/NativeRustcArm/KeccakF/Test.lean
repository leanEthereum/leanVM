module

import NativeRustcArm.KeccakF.Spec

/-!
# The axioms of `keccak_f`'s proof

`keccakF_spec` depends on Lean's three axioms only.
-/

/--
info: 'NativeRustcArm.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.keccakF_spec
