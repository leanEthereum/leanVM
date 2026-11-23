module

public import NativeRustcVmX64.Bus.GkrLayers
public import NativeRustcVmX64.Bus.GkrStep
public import NativeRustcVmX64.Bus.VerifyGkr

/-!
# `gkr.rs` on x86-64

The contracts (`NativeRustcVmX64.Spec.Bus`) of rustc's `gkr_step`, `gkr_layers` and
`verify_gkr_grand_products`, met: `Bus.GkrStep.gkrStep_spec` (given its callees'
contracts), `Bus.GkrLayers.gkrLayers_spec` (given `gkr_step`'s contract),
`Bus.VerifyGkr.verifyGkr_spec` (given `read_scalar`'s and `gkr_layers`'s).
-/

/--
info: 'NativeRustcVmX64.Bus.GkrStep.gkrStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.GkrStep.gkrStep_spec

/--
info: 'NativeRustcVmX64.Bus.GkrLayers.gkrLayers_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.GkrLayers.gkrLayers_spec

/--
info: 'NativeRustcVmX64.Bus.VerifyGkr.verifyGkr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Bus.VerifyGkr.verifyGkr_spec
