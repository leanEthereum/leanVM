module

public import NativeRustcVmX64.Tables.TableWeights
public import NativeRustcVmX64.Tables.ColumnClaims
public import NativeRustcVmX64.Tables.TablePhase
public import NativeRustcVmX64.Tables.PublicInputPhase

/-!
# `tables.rs` on x86-64 (phases 4 and 5)

The contracts (`NativeRustcVmX64.Spec.Tables`) met: `Tables.TableWeights.table_weights_spec`,
`Tables.ColumnClaims.tableColumnClaims_spec`, `Tables.TablePhase.tablePhase_spec`,
`Tables.PublicInputPhase.publicInputPhase_spec`.
Each depends on Lean's three axioms only (checked below).
-/

/--
info: 'NativeRustcVmX64.Tables.TableWeights.table_weights_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Tables.TableWeights.table_weights_spec

/--
info: 'NativeRustcVmX64.Tables.ColumnClaims.tableColumnClaims_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Tables.ColumnClaims.tableColumnClaims_spec

/--
info: 'NativeRustcVmX64.Tables.TablePhase.tablePhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Tables.TablePhase.tablePhase_spec

/--
info: 'NativeRustcVmX64.Tables.PublicInputPhase.publicInputPhase_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Tables.PublicInputPhase.publicInputPhase_spec
