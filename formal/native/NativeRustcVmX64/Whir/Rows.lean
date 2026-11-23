module

public import NativeRustcVmX64.Whir.GlueLevel.Spec

/-!
# `whir.rs`'s row functions on x86-64: the finished contracts and their axioms

`glue_level` (`NativeRustcVmX64.Whir.GlueLevel.glueLevel_spec`). Each end theorem uses Lean's
three axioms only.
-/

/--
info: 'NativeRustcVmX64.Whir.GlueLevel.glueLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.GlueLevel.glueLevel_spec
