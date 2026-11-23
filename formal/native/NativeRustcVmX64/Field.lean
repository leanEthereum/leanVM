module

public import NativeRustcVmX64.Field.Kmul
public import NativeRustcVmX64.Field.EWMul
public import NativeRustcVmX64.Field.KinvSq
public import NativeRustcVmX64.Field.Kinv
public import NativeRustcVmX64.Field.Kpow
public import NativeRustcVmX64.Field.EWSqIter
public import NativeRustcVmX64.Field.BitLength

/-!
# `field.rs` on x86-64

The contracts (`NativeRustcVmX64.Spec.Field`) of rustc's `kmul`, `EW::mul`, `kinv::sq`, `kinv`,
`kpow`, `EW::sq_iter` and `bit_length`, met: `Field.Kmul.kmul_spec`, `Field.EWMul.ewMul_spec`,
`Field.KinvSq.kinvSq_spec`, `Field.Kinv.kinv_spec`, `Field.Kpow.kpow_spec`,
`Field.EWSqIter.ewSqIter_spec`, `Field.BitLength.bitLength_spec`. The build fails if an axiom
footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Field.Kmul.kmul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.Kmul.kmul_spec

/-- info: 'NativeRustcVmX64.Field.EWMul.ewMul_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.EWMul.ewMul_spec

/-- info: 'NativeRustcVmX64.Field.KinvSq.kinvSq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.KinvSq.kinvSq_spec

/-- info: 'NativeRustcVmX64.Field.Kinv.kinv_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.Kinv.kinv_spec

/-- info: 'NativeRustcVmX64.Field.Kpow.kpow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.Kpow.kpow_spec

/-- info: 'NativeRustcVmX64.Field.EWSqIter.ewSqIter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.EWSqIter.ewSqIter_spec

/-- info: 'NativeRustcVmX64.Field.BitLength.bitLength_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Field.BitLength.bitLength_spec
