module

public import NativeRustcVmArm.Field.Kmul
public import NativeRustcVmArm.Field.EWMul
public import NativeRustcVmArm.Field.KinvSq
public import NativeRustcVmArm.Field.Kinv
public import NativeRustcVmArm.Field.Kpow
public import NativeRustcVmArm.Field.EWSqIter
public import NativeRustcVmArm.Field.BitLength

/-!
# `field.rs` on AArch64

The contracts (`NativeRustcVmArm.Spec.Field`) of rustc's `kmul`, `EW::mul`, `kinv::sq`, `kinv`,
`kpow`, `EW::sq_iter` and `bit_length`, met: `Field.Kmul.kmul_spec`, `Field.EWMul.ewMul_spec`,
`Field.KinvSq.kinvSq_spec`, `Field.Kinv.kinv_spec`, `Field.Kpow.kpow_spec`,
`Field.EWSqIter.ewSqIter_spec`, `Field.BitLength.bitLength_spec`.
-/

/-- info: 'NativeRustcVmArm.Field.Kmul.kmul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.Kmul.kmul_spec

/-- info: 'NativeRustcVmArm.Field.EWMul.ewMul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.EWMul.ewMul_spec

/-- info: 'NativeRustcVmArm.Field.KinvSq.kinvSq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.KinvSq.kinvSq_spec

/-- info: 'NativeRustcVmArm.Field.Kinv.kinv_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.Kinv.kinv_spec

/-- info: 'NativeRustcVmArm.Field.Kpow.kpow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.Kpow.kpow_spec

/-- info: 'NativeRustcVmArm.Field.EWSqIter.ewSqIter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.EWSqIter.ewSqIter_spec

/-- info: 'NativeRustcVmArm.Field.BitLength.bitLength_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Field.BitLength.bitLength_spec
