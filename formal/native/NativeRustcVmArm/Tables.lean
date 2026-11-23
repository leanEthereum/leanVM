module

public import NativeRustcVmArm.Tables.TableWeights
public import NativeRustcVmArm.Tables.PublicInputPhase
public import NativeRustcVmArm.Tables.TablePhase
public import NativeRustcVmArm.Tables.ColumnClaims
public import NativeRustcVmArm.Tables.TableSumcheck
public import NativeRustcVmArm.Tables.TableTerms

/-!
# `tables.rs` on AArch64 (phases 4 and 5)

The contracts (`NativeRustcVmArm.Spec.Tables`) met: `Tables.TableWeights.table_weights_spec`,
`Tables.PublicInputPhase.publicInputPhase_spec`, `Tables.TablePhase.tablePhase_spec`,
`Tables.ColumnClaims.tableColumnClaims_spec`.
Each depends on Lean's three axioms only (checked below).
-/

/--
info: 'NativeRustcVmArm.Tables.TableWeights.table_weights_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmArm.Tables.TableWeights.table_weights_spec

/--
info: 'NativeRustcVmArm.Tables.PublicInputPhase.publicInputPhase_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmArm.Tables.PublicInputPhase.publicInputPhase_spec

/--
info: 'NativeRustcVmArm.Tables.TablePhase.tablePhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmArm.Tables.TablePhase.tablePhase_spec

/--
info: 'NativeRustcVmArm.Tables.ColumnClaims.tableColumnClaims_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmArm.Tables.ColumnClaims.tableColumnClaims_spec

/-- info: 'NativeRustcVmArm.Tables.TableSumcheck.tableSumcheck_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Tables.TableSumcheck.tableSumcheck_spec

/-- info: 'NativeRustcVmArm.Tables.TableTerms.tableTerms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Tables.TableTerms.tableTerms_spec
