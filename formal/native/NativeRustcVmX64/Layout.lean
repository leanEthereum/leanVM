module

public import NativeRustcVmX64.Layout.FormTerms
public import NativeRustcVmX64.Layout.ConstraintsW
public import NativeRustcVmX64.Layout.LayoutWPlacement
public import NativeRustcVmX64.Layout.ColumnKappas
public import NativeRustcVmX64.Layout.Evaluate
public import NativeRustcVmX64.Layout.FormBufAddTerm
public import NativeRustcVmX64.Layout.FormBufAddScaled
public import NativeRustcVmX64.Layout.InsertionSort
public import NativeRustcVmX64.Layout.StackPoint
public import NativeRustcVmX64.Layout.ReadAnnouncedSizes

/-!
# `layout.rs` on x86-64

The contracts (`NativeRustcVmX64.Spec.Layout`) of rustc's layout functions met so far:
`Layout.FormTerms.formTerms_spec`, `Layout.ConstraintsW.constraintsW_spec`,
`Layout.LayoutWPlacement.layoutWPlacement_spec`, `Layout.ColumnKappas.columnKappas_spec`,
`Layout.Evaluate.evaluate_spec`, `Layout.FormBufAddTerm.formBufAddTerm_spec`,
`Layout.FormBufAddScaled.formBufAddScaled_spec`, `Layout.InsertionSort.insertionSort_spec`,
`Layout.StackPoint.stackPoint_spec` (`Spec.Ring`'s contract),
`Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec`. The
build fails if an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Layout.FormTerms.formTerms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.FormTerms.formTerms_spec

/-- info: 'NativeRustcVmX64.Layout.ConstraintsW.constraintsW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.ConstraintsW.constraintsW_spec

/-- info: 'NativeRustcVmX64.Layout.LayoutWPlacement.layoutWPlacement_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.LayoutWPlacement.layoutWPlacement_spec

/-- info: 'NativeRustcVmX64.Layout.ColumnKappas.columnKappas_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.ColumnKappas.columnKappas_spec

/-- info: 'NativeRustcVmX64.Layout.Evaluate.evaluate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.Evaluate.evaluate_spec

/-- info: 'NativeRustcVmX64.Layout.FormBufAddTerm.formBufAddTerm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.FormBufAddTerm.formBufAddTerm_spec

/-- info: 'NativeRustcVmX64.Layout.FormBufAddScaled.formBufAddScaled_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.FormBufAddScaled.formBufAddScaled_spec

/-- info: 'NativeRustcVmX64.Layout.InsertionSort.insertionSort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.InsertionSort.insertionSort_spec

/-- info: 'NativeRustcVmX64.Layout.StackPoint.stackPoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.StackPoint.stackPoint_spec

/-- info: 'NativeRustcVmX64.Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec
