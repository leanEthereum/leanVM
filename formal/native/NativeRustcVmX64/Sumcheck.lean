module

public import NativeRustcVmX64.Sumcheck.RowsRow
public import NativeRustcVmX64.Sumcheck.Climb
public import NativeRustcVmX64.Sumcheck.RoundPoly
public import NativeRustcVmX64.Sumcheck.Plain
public import NativeRustcVmX64.Sumcheck.Gkr
public import NativeRustcVmX64.Sumcheck.Layer

/-!
# `transcript.rs`'s openings and sumcheck functions on x86-64

The contracts (`NativeRustcVmX64.Spec.Sumcheck`) met, each given its callees' contracts; their
axioms checked below.
-/

/-- info: 'NativeRustcVmX64.Sumcheck.RowsRow.rowsRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.RowsRow.rowsRow_spec

/-- info: 'NativeRustcVmX64.Sumcheck.Climb.climb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.Climb.climb_spec

/-- info: 'NativeRustcVmX64.Sumcheck.RoundPoly.roundPoly_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.RoundPoly.roundPoly_spec

/-- info: 'NativeRustcVmX64.Sumcheck.Plain.sumcheckPlain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.Plain.sumcheckPlain_spec

/-- info: 'NativeRustcVmX64.Sumcheck.Gkr.sumcheckGkr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.Gkr.sumcheckGkr_spec

/-- info: 'NativeRustcVmX64.Sumcheck.Layer.sumcheckLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.Layer.sumcheckLayer_spec
