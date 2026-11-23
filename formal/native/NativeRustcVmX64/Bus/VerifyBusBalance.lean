module

public import NativeRustcVmX64.Bus.VerifyBusBalanceClosure0
public import NativeRustcVmX64.Bus.VerifyBusBalance.Main

/-!
# `verify_bus_balance` and its closure on x86-64: the finished contracts

`NativeRustcVmX64.Bus.VerifyBusBalance.verifyBusBalance_spec` (`verify_bus_balance`,
`NativeRustcVmX64/Bus/VerifyBusBalance/Main.lean`) and
`NativeRustcVmX64.Bus.FpClosure.fpClosure_spec` (`verify_bus_balance::{closure#0}`,
`NativeRustcVmX64/Bus/VerifyBusBalanceClosure0.lean`), on Lean's three axioms.
-/

/-- info: 'NativeRustcVmX64.Bus.VerifyBusBalance.verifyBusBalance_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.VerifyBusBalance.verifyBusBalance_spec

/-- info: 'NativeRustcVmX64.Bus.FpClosure.fpClosure_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.FpClosure.fpClosure_spec
