module

import NativeRustcVmX64.Wire.Decode

/-! Guard: `decode_spec` uses only Lean's three axioms. -/

/--
info: 'NativeRustcVmX64.Wire.Decode.decode_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Wire.Decode.decode_spec
