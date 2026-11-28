module

public import NativeRustcVmArm.Sumcheck.RowsRow
public import NativeRustcVmArm.Sumcheck.Climb
public import NativeRustcVmArm.Sumcheck.RoundPoly
public import NativeRustcVmArm.Sumcheck.Plain
public import NativeRustcVmArm.Sumcheck.Gkr
public import NativeRustcVmArm.Sumcheck.Layer
public import NativeRustcVmArm.Sumcheck.OpenPhase
public import NativeRustcVmArm.Sumcheck.QueryOpenings

/-!
# `transcript.rs`'s openings and sumcheck functions on AArch64

The contracts (`NativeRustcVmArm.Spec.Sumcheck`) met, each given its callees' contracts; their
axioms checked below.
-/

/-- info: 'NativeRustcVmArm.Sumcheck.RowsRow.rowsRow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.RowsRow.rowsRow_spec

/-- info: 'NativeRustcVmArm.Sumcheck.Climb.climb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.Climb.climb_spec

/-- info: 'NativeRustcVmArm.Sumcheck.RoundPoly.roundPoly_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.RoundPoly.roundPoly_spec

/-- info: 'NativeRustcVmArm.Sumcheck.Plain.sumcheckPlain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.Plain.sumcheckPlain_spec

/-- info: 'NativeRustcVmArm.Sumcheck.Gkr.sumcheckGkr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.Gkr.sumcheckGkr_spec

/-- info: 'NativeRustcVmArm.Sumcheck.Layer.sumcheckLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.Layer.sumcheckLayer_spec

/-- info: 'NativeRustcVmArm.Sumcheck.OpenPhase.openPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.OpenPhase.openPhase_spec

/-- info: 'NativeRustcVmArm.Sumcheck.QueryOpenings.queryOpenings_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Sumcheck.QueryOpenings.queryOpenings_spec
