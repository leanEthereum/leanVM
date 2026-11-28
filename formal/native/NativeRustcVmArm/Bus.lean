module

public import NativeRustcVmArm.Bus.ComputedBytecodeValue
public import NativeRustcVmArm.Bus.Fingerprints
public import NativeRustcVmArm.Bus.FpClosure
public import NativeRustcVmArm.Bus.BlockForm
public import NativeRustcVmArm.Bus.BusLayout
public import NativeRustcVmArm.Bus.BytecodeShare
public import NativeRustcVmArm.Bus.Gkr
public import NativeRustcVmArm.Bus.VerifyBusBalance
public import NativeRustcVmArm.Bus.AccumulateSide

/-!
# `bus.rs` on AArch64: the finished contracts

Each `<fn>_spec` proves `Spec (label <fn>Label) <Fn>Pre <Fn>Post` (`NativeRustcVmArm/Spec/Bus.lean`)
from its callees' contracts; the guards check they use Lean's three axioms only (`gkr.rs`'s:
`NativeRustcVmArm/Bus/Gkr.lean`).
-/

/-- info: 'NativeRustcVmArm.Bus.ComputedBytecodeValue.computedBytecodeValue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.ComputedBytecodeValue.computedBytecodeValue_spec

/-- info: 'NativeRustcVmArm.Bus.Fingerprints.fingerprints_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.Fingerprints.fingerprints_spec

/-- info: 'NativeRustcVmArm.Bus.FpClosure.fpClosure_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.FpClosure.fpClosure_spec

/-- info: 'NativeRustcVmArm.Bus.BlockForm.blockForm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.BlockForm.blockForm_spec

/-- info: 'NativeRustcVmArm.Bus.BusLayout.busLayout_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.BusLayout.busLayout_spec

/-- info: 'NativeRustcVmArm.Bus.BytecodeShare.bytecodeShare_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.BytecodeShare.bytecodeShare_spec

/--
info: 'NativeRustcVmArm.Bus.VerifyBusBalance.verifyBusBalance_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.VerifyBusBalance.verifyBusBalance_spec

/-- info: 'NativeRustcVmArm.Bus.AccumulateSide.accumulateSide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.AccumulateSide.accumulateSide_spec
