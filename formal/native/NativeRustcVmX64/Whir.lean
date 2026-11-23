module

public import NativeRustcVmX64.Whir.QueryBits
public import NativeRustcVmX64.Whir.LanesOf
public import NativeRustcVmX64.Whir.SampleQueries
public import NativeRustcVmX64.Whir.FoldRound
public import NativeRustcVmX64.Whir.FoldRounds

/-!
# `whir.rs`'s functions on x86-64

The contracts (`NativeRustcVmX64.Spec.Whir`) of `whir.rs`'s functions met, each given its callees'
contracts; their axioms checked below.
-/

/-- info: 'NativeRustcVmX64.Whir.QueryBits.queryBits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Whir.QueryBits.queryBits_spec

/-- info: 'NativeRustcVmX64.Whir.LanesOf.lanesOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Whir.LanesOf.lanesOf_spec

/-- info: 'NativeRustcVmX64.Whir.SampleQueries.sampleQueries_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Whir.SampleQueries.sampleQueries_spec

/-- info: 'NativeRustcVmX64.Whir.FoldRound.foldRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Whir.FoldRound.foldRound_spec

/-- info: 'NativeRustcVmX64.Whir.FoldRounds.foldRounds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Whir.FoldRounds.foldRounds_spec
