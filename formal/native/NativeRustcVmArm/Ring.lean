module

public import NativeRustcVmArm.Ring.Psi
public import NativeRustcVmArm.Ring.Coeff
public import NativeRustcVmArm.Ring.Target
public import NativeRustcVmArm.Ring.Switch
public import NativeRustcVmArm.Ring.Column
public import NativeRustcVmArm.Ring.Claim
public import NativeRustcVmArm.Ring.Weight

/-!
# `ring_switch.rs` and `stack.rs`'s weights on AArch64

The contracts (`NativeRustcVmArm.Spec.Ring`) met: `Ring.Psi.ringPsi_spec`,
`Ring.Coeff.ringCoefficients_spec`, `Ring.Target.ringTarget_spec`, `Ring.Switch.ringSwitch_spec`,
`Ring.Column.columnWeight_spec`, `Ring.Claim.ringClaimWeight_spec`, `Ring.Weight.ringWeight_spec`. The build fails if an axiom
footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmArm.Ring.Psi.ringPsi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Psi.ringPsi_spec

/-- info: 'NativeRustcVmArm.Ring.Coeff.ringCoefficients_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Coeff.ringCoefficients_spec

/-- info: 'NativeRustcVmArm.Ring.Target.ringTarget_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Target.ringTarget_spec

/-- info: 'NativeRustcVmArm.Ring.Switch.ringSwitch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Switch.ringSwitch_spec

/-- info: 'NativeRustcVmArm.Ring.Column.columnWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Column.columnWeight_spec

/-- info: 'NativeRustcVmArm.Ring.Claim.ringClaimWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Claim.ringClaimWeight_spec

/-- info: 'NativeRustcVmArm.Ring.Weight.ringWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Ring.Weight.ringWeight_spec
