module

public import NativeRustcVmArm.Layout.BuildLayout

/-!
# `layout.rs`'s `build_layout` on AArch64

The contract (`NativeRustcVmArm.Spec.Layout`) of rustc's `build_layout`, met:
`Layout.BuildLayout.buildLayout_spec`. The build fails if an axiom footprint grows beyond Lean's
three standard axioms.
-/

/-- info: 'NativeRustcVmArm.Layout.BuildLayout.buildLayout_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.BuildLayout.buildLayout_spec
