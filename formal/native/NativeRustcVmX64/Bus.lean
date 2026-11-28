module

public import NativeRustcVmX64.Bus.ComputedBytecodeValue
public import NativeRustcVmX64.Bus.Fingerprints
public import NativeRustcVmX64.Bus.BlockForm
public import NativeRustcVmX64.Bus.BusLayout

/-!
# `bus.rs` on x86-64: the finished contracts

Each `<fn>_spec` proves `Spec (label <fn>Label) <Fn>Pre <Fn>Post` (`NativeRustcVmX64/Spec/Bus.lean`)
from its callees' contracts; the guards check they use Lean's three axioms only.
-/

/-- info: 'NativeRustcVmX64.Bus.ComputedBytecodeValue.computedBytecodeValue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.ComputedBytecodeValue.computedBytecodeValue_spec

/-- info: 'NativeRustcVmX64.Bus.Fingerprints.fingerprints_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.Fingerprints.fingerprints_spec

/-- info: 'NativeRustcVmX64.Bus.BlockForm.blockForm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.BlockForm.blockForm_spec

/-- info: 'NativeRustcVmX64.Bus.BusLayout.busLayout_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.BusLayout.busLayout_spec
