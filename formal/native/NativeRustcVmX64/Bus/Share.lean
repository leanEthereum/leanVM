module

public import NativeRustcVmX64.Bus.BytecodeShare
public import NativeRustcVmX64.Bus.AccumulateSide

/-!
# The bytecode share and the sides' totals on x86-64

`bytecode_share` and `accumulate_side`'s entry-to-return contracts, on Lean's three axioms.
-/

/--
info: 'NativeRustcVmX64.Bus.BytecodeShare.bytecodeShare_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Bus.BytecodeShare.bytecodeShare_spec

/-- info: 'NativeRustcVmX64.Bus.AccumulateSide.accumulateSide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.AccumulateSide.accumulateSide_spec
