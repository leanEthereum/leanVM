module

public import NativeRustcVmArm.Layout.Evaluate
public import NativeRustcVmArm.Layout.FormBufAddTerm
public import NativeRustcVmArm.Layout.FormBufAddScaled

/-!
# `layout.rs`'s forms on AArch64

The contracts (`NativeRustcVmArm.Spec.Layout`) of rustc's `evaluate`, `FormBuf::add_term` and
`FormBuf::add_scaled`, met: `Layout.Evaluate.evaluate_spec`,
`Layout.FormBufAddTerm.formBufAddTerm_spec`, `Layout.FormBufAddScaled.formBufAddScaled_spec`. The
build fails if an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmArm.Layout.Evaluate.evaluate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.Evaluate.evaluate_spec

/-- info: 'NativeRustcVmArm.Layout.FormBufAddTerm.formBufAddTerm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.FormBufAddTerm.formBufAddTerm_spec

/-- info: 'NativeRustcVmArm.Layout.FormBufAddScaled.formBufAddScaled_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.FormBufAddScaled.formBufAddScaled_spec
