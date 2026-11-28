module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Spec
public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Spec

/-!
# `whir.rs`'s `each_row` instances on x86-64: the finished contracts and their axioms

`each_row::<final_level's closure>` (`NativeRustcVmX64.Whir.EachRowOfFinalLevel.eachRowFinal_spec`)
and `each_row::<next_level's closure>` (`NativeRustcVmX64.Whir.EachRowOfNextLevel.eachRowNext_spec`).
Each end theorem uses Lean's three axioms only.
-/

/--
info: 'NativeRustcVmX64.Whir.EachRowOfFinalLevel.eachRowFinal_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.EachRowOfFinalLevel.eachRowFinal_spec

/--
info: 'NativeRustcVmX64.Whir.EachRowOfNextLevel.eachRowNext_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.EachRowOfNextLevel.eachRowNext_spec
