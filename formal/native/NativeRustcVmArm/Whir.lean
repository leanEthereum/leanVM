module

public import NativeRustcVmArm.Whir.QueryBits
public import NativeRustcVmArm.Whir.SampleQueries
public import NativeRustcVmArm.Whir.FoldRound
public import NativeRustcVmArm.Whir.FoldRounds
public import NativeRustcVmArm.Whir.GluedEval
public import NativeRustcVmArm.Whir.SubspaceAtTable
public import NativeRustcVmArm.Whir.NovelEval
public import NativeRustcVmArm.Whir.FoldRow
public import NativeRustcVmArm.Whir.GlueLevel.Spec
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Spec
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Spec
public import NativeRustcVmArm.Whir.InducedWeight
public import NativeRustcVmArm.Whir.LanesOf
public import NativeRustcVmArm.Whir.WhirLevels
public import NativeRustcVmArm.Whir.SubspaceTable
public import NativeRustcVmArm.Whir.BasisWEval
public import NativeRustcVmArm.Whir.VerifyStackedOpening
public import NativeRustcVmArm.Whir.NextLevel
public import NativeRustcVmArm.Whir.FinalLevel

/-!
# `whir.rs`'s functions on AArch64

The contracts (`NativeRustcVmArm.Spec.Whir`) of `whir.rs`'s functions met, each given its callees'
contracts; their axioms checked below.
-/

/-- info: 'NativeRustcVmArm.Whir.QueryBits.queryBits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.QueryBits.queryBits_spec

/-- info: 'NativeRustcVmArm.Whir.SampleQueries.sampleQueries_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.SampleQueries.sampleQueries_spec

/-- info: 'NativeRustcVmArm.Whir.GluedEval.gluedEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.GluedEval.gluedEval_spec

/-- info: 'NativeRustcVmArm.Whir.SubspaceAtTable.subspaceAtTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.SubspaceAtTable.subspaceAtTable_spec

/-- info: 'NativeRustcVmArm.Whir.NovelEval.novelEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.NovelEval.novelEval_spec

/-- info: 'NativeRustcVmArm.Whir.FoldRow.foldRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.FoldRow.foldRow_spec

/-- info: 'NativeRustcVmArm.Whir.FoldRound.foldRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.FoldRound.foldRound_spec

/-- info: 'NativeRustcVmArm.Whir.GlueLevel.glueLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.GlueLevel.glueLevel_spec

/-- info: 'NativeRustcVmArm.Whir.EachRowOfFinalLevel.eachRowFinal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.EachRowOfFinalLevel.eachRowFinal_spec

/-- info: 'NativeRustcVmArm.Whir.EachRowOfNextLevel.eachRowNext_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.EachRowOfNextLevel.eachRowNext_spec

/-- info: 'NativeRustcVmArm.Whir.FoldRounds.foldRounds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.FoldRounds.foldRounds_spec

/-- info: 'NativeRustcVmArm.Whir.InducedWeight.inducedWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.InducedWeight.inducedWeight_spec

/-- info: 'NativeRustcVmArm.Whir.LanesOf.lanesOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.LanesOf.lanesOf_spec

/-- info: 'NativeRustcVmArm.Whir.WhirLevels.whirLevels_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.WhirLevels.whirLevels_spec

/-- info: 'NativeRustcVmArm.Whir.SubspaceTable.subspaceTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.SubspaceTable.subspaceTable_spec

/-- info: 'NativeRustcVmArm.Whir.BasisWEval.basisWEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.BasisWEval.basisWEval_spec

/--
info: 'NativeRustcVmArm.Whir.VerifyStackedOpening.verifyStackedOpening_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.VerifyStackedOpening.verifyStackedOpening_spec

/-- info: 'NativeRustcVmArm.Whir.NextLevel.nextLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.NextLevel.nextLevel_spec

/-- info: 'NativeRustcVmArm.Whir.FinalLevel.finalLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Whir.FinalLevel.finalLevel_spec
