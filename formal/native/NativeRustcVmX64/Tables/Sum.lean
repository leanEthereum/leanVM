module

public import NativeRustcVmX64.Tables.TableTerms
public import NativeRustcVmX64.Tables.TableSumcheck

/-!
# `tables.rs`'s `table_terms` and `table_sumcheck` on x86-64

The contracts (`NativeRustcVmX64.Spec.Tables`) met, each given its callees' contracts; their
axioms checked below.
-/

/-- info: 'NativeRustcVmX64.Tables.TableTerms.tableTerms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Tables.TableTerms.tableTerms_spec

/-- info: 'NativeRustcVmX64.Tables.TableSumcheck.tableSumcheck_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Tables.TableSumcheck.tableSumcheck_spec
