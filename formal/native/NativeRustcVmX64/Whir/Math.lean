module

public import NativeRustcVmX64.Whir.SubspaceAtTable
public import NativeRustcVmX64.Whir.GluedEval
public import NativeRustcVmX64.Whir.NovelEval
public import NativeRustcVmX64.Whir.FoldRow
public import NativeRustcVmX64.Whir.SubspaceTable

/-!
# `whir.rs`'s arithmetic functions on x86-64: the finished contracts

`subspace_table` (`Whir.SubspaceTable.subspaceTable_spec`), `subspace_at_table`
(`Whir.SubspaceAtTable.subspaceAtTable_spec`), `glued_eval` (`Whir.GluedEval.gluedEval_spec`),
`novel_eval` (`Whir.NovelEval.novelEval_spec`) and `fold_row` (`Whir.FoldRow.foldRow_spec`), each
from its callees' contracts, on Lean's three axioms.
-/

/--
info: 'NativeRustcVmX64.Whir.SubspaceAtTable.subspaceAtTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.SubspaceAtTable.subspaceAtTable_spec

/--
info: 'NativeRustcVmX64.Whir.GluedEval.gluedEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.GluedEval.gluedEval_spec

/--
info: 'NativeRustcVmX64.Whir.NovelEval.novelEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.NovelEval.novelEval_spec

/--
info: 'NativeRustcVmX64.Whir.FoldRow.foldRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.FoldRow.foldRow_spec

/--
info: 'NativeRustcVmX64.Whir.SubspaceTable.subspaceTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.SubspaceTable.subspaceTable_spec
