module

public import NativeRustcVmX64.Whir.WhirLevels

/-!
# `whir.rs`' levels on x86-64: `whir_levels`, `next_level`, `final_level`

The contracts' proofs (`NativeRustcVmX64.Whir.Levels.WL.whirLevels_spec`), checked here to rest on
Lean's three axioms only.
-/

/--
info: 'NativeRustcVmX64.Whir.Levels.WL.whirLevels_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.Levels.WL.whirLevels_spec
