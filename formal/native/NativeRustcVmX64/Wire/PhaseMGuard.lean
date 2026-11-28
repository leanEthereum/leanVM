module

import NativeRustcVmX64.Wire.PhaseM

/-! Guard: `phaseM_spec` uses only Lean's three axioms. -/

/--
info: 'NativeRustcVmX64.Wire.PhaseM.phaseM_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Wire.PhaseM.phaseM_spec
