module

public import NativeRustcVmArm.Layout.FormTerms
public import NativeRustcVmArm.Layout.ConstraintsW
public import NativeRustcVmArm.Layout.LayoutWPlacement
public import NativeRustcVmArm.Layout.StackPoint
public import NativeRustcVmArm.Layout.ColumnKappas
public import NativeRustcVmArm.Layout.InsertionSort
public import NativeRustcVmArm.Layout.Forms
public import NativeRustcVmArm.Layout.Stack
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes
public import NativeRustcVmArm.Layout.Build
public import NativeRustcVmArm.Layout.StackOffsets
public import NativeRustcVmArm.Layout.PlacementsOf

/-!
# `layout.rs` on AArch64

The contracts (`NativeRustcVmArm.Spec.Layout`) of rustc's layout functions, met:
`Layout.FormTerms.formTerms_spec`, `Layout.ConstraintsW.constraintsW_spec`,
`Layout.LayoutWPlacement.layoutWPlacement_spec`, `Layout.StackPoint.stackPoint_spec`,
`Layout.ColumnKappas.columnKappas_spec`, `Layout.InsertionSort.insertionSort_spec`,
`Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec`, `Layout.StackOffsets.stackOffsets_spec`, and
`Layout.Forms`' (`evaluate`, `FormBuf::add_term`,
`FormBuf::add_scaled`, guarded there), `Layout.Stack`'s (`push_claim`, `ladder`, `commit_stack`,
`read_ood`, guarded there) and `Layout.Build`'s (`build_layout`, guarded there). The build fails if an axiom footprint grows beyond Lean's
three standard axioms.
-/

/-- info: 'NativeRustcVmArm.Layout.FormTerms.formTerms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.FormTerms.formTerms_spec

/-- info: 'NativeRustcVmArm.Layout.ConstraintsW.constraintsW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.ConstraintsW.constraintsW_spec

/-- info: 'NativeRustcVmArm.Layout.LayoutWPlacement.layoutWPlacement_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.LayoutWPlacement.layoutWPlacement_spec

/-- info: 'NativeRustcVmArm.Layout.StackPoint.stackPoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.StackPoint.stackPoint_spec

/-- info: 'NativeRustcVmArm.Layout.ColumnKappas.columnKappas_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.ColumnKappas.columnKappas_spec

/-- info: 'NativeRustcVmArm.Layout.InsertionSort.insertionSort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.InsertionSort.insertionSort_spec

/-- info: 'NativeRustcVmArm.Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec

/-- info: 'NativeRustcVmArm.Layout.StackOffsets.stackOffsets_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.StackOffsets.stackOffsets_spec

/--
info: 'NativeRustcVmArm.Layout.PlacementsOf.placementsOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.PlacementsOf.placementsOf_spec
