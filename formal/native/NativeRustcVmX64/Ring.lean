module

public import NativeRustcVmX64.Ring.Psi
public import NativeRustcVmX64.Ring.Coeff
public import NativeRustcVmX64.Ring.Switch
public import NativeRustcVmX64.Ring.Column
public import NativeRustcVmX64.Ring.Claim
public import NativeRustcVmX64.Ring.Target
public import NativeRustcVmX64.Ring.Weight

/-!
# Ring switching and the stack weights on x86-64

The contracts (`NativeRustcVmX64.Spec.Ring`) of rustc's `ring_switch.rs` and `stack.rs`
functions met so far: `Ring.Psi.ringPsi_spec`, `Ring.Coeff.ringCoefficients_spec`,
`Ring.Target.ringTarget_spec`, `Ring.Switch.ringSwitch_spec`, `Ring.Column.columnWeight_spec`,
`Ring.Weight.ringWeight_spec`, `Ring.Claim.ringClaimWeight_spec`. The blocks run from literal templates
(`NativeRustcVmX64.Ring.Seq`). The build fails if an axiom footprint grows beyond Lean's three
standard axioms.
-/

/-- info: 'NativeRustcVmX64.Ring.Psi.ringPsi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Psi.ringPsi_spec

/-- info: 'NativeRustcVmX64.Ring.Coeff.ringCoefficients_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Coeff.ringCoefficients_spec

/-- info: 'NativeRustcVmX64.Ring.Switch.ringSwitch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Switch.ringSwitch_spec

/-- info: 'NativeRustcVmX64.Ring.Column.columnWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Column.columnWeight_spec

/-- info: 'NativeRustcVmX64.Ring.Claim.ringClaimWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Claim.ringClaimWeight_spec

/-- info: 'NativeRustcVmX64.Ring.Target.ringTarget_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Target.ringTarget_spec

/-- info: 'NativeRustcVmX64.Ring.Weight.ringWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Ring.Weight.ringWeight_spec
