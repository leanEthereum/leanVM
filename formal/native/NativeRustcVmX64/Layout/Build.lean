module

public import NativeRustcVmX64.Layout.StackOffsets
public import NativeRustcVmX64.Layout.PlacementsOf
public import NativeRustcVmX64.Layout.BuildLayout

/-!
# The x86-64 layout builders: axiom guards

`stack_offsets`, `placements_of` and `build_layout` meet their contracts, on Lean's three axioms.
-/

/--
info: 'NativeRustcVmX64.Layout.StackOffsets.stackOffsets_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.StackOffsets.stackOffsets_spec

/--
info: 'NativeRustcVmX64.Layout.PlacementsOf.placementsOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.PlacementsOf.placementsOf_spec

/--
info: 'NativeRustcVmX64.Layout.BuildLayout.buildLayout_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.BuildLayout.buildLayout_spec
