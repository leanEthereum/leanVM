module

public import NativeRustcVmX64.Whir.InducedWeight

/-! # Kernel axiom guard for `induced_weight` -/

/--
info: 'NativeRustcVmX64.Whir.InducedWeight.inducedWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.InducedWeight.inducedWeight_spec
