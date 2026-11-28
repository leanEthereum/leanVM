module

public import NativeRustcVmArm.Bus.GkrStep
public import NativeRustcVmArm.Bus.GkrLayers
public import NativeRustcVmArm.Bus.VerifyGkr

/-!
# `gkr.rs` on AArch64

The contracts (`NativeRustcVmArm.Spec.Bus`) of rustc's `gkr_step`, `gkr_layers` and
`verify_gkr_grand_products`, met: `Bus.GkrStep.gkrStep_spec`, `Bus.GkrLayers.gkrLayers_spec`,
`Bus.VerifyGkr.verifyGkr_spec`.
-/

/--
info: 'NativeRustcVmArm.Bus.GkrStep.gkrStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.GkrStep.gkrStep_spec

/--
info: 'NativeRustcVmArm.Bus.GkrLayers.gkrLayers_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.GkrLayers.gkrLayers_spec

/--
info: 'NativeRustcVmArm.Bus.VerifyGkr.verifyGkr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Bus.VerifyGkr.verifyGkr_spec
