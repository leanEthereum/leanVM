module

public import NativeRustcVmArm.Wire.ReaderLe
public import NativeRustcVmArm.Wire.ReaderDigest
public import NativeRustcVmArm.Wire.ReaderWords
public import NativeRustcVmArm.Wire.InsD
public import NativeRustcVmArm.Wire.Find
public import NativeRustcVmArm.Wire.RdRows
public import NativeRustcVmArm.Wire.ClimbLevel
public import NativeRustcVmArm.Wire.PhaseM
public import NativeRustcVmArm.Wire.WriteOpenings
public import NativeRustcVmArm.Wire.Decode

/-!
# `wire.rs` on AArch64

The contracts (`NativeRustcVmArm.Spec.Wire`) of rustc's wire decoder, met:
`Wire.ReaderLe.readerLe_spec`, `Wire.ReaderDigest.readerDigest_spec`,
`Wire.ReaderWords.readerWords_spec`, `Wire.InsD.insD_spec`, `Wire.Find.find_spec`,
`Wire.RdRows.rdRows_spec`, `Wire.ClimbLevel.climbLevel_spec`, `Wire.PhaseM.phaseM_spec`, `Wire.WriteOpenings.writeOpenings_spec`, `Wire.Decode.decode_spec`.
-/

/-- info: 'NativeRustcVmArm.Wire.ReaderLe.readerLe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.ReaderLe.readerLe_spec

/-- info: 'NativeRustcVmArm.Wire.ReaderDigest.readerDigest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.ReaderDigest.readerDigest_spec

/-- info: 'NativeRustcVmArm.Wire.ReaderWords.readerWords_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.ReaderWords.readerWords_spec

/-- info: 'NativeRustcVmArm.Wire.InsD.insD_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.InsD.insD_spec

/-- info: 'NativeRustcVmArm.Wire.Find.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.Find.find_spec

/-- info: 'NativeRustcVmArm.Wire.RdRows.rdRows_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.RdRows.rdRows_spec

/-- info: 'NativeRustcVmArm.Wire.ClimbLevel.climbLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.ClimbLevel.climbLevel_spec

/-- info: 'NativeRustcVmArm.Wire.PhaseM.phaseM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.PhaseM.phaseM_spec

/--
info: 'NativeRustcVmArm.Wire.WriteOpenings.writeOpenings_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.WriteOpenings.writeOpenings_spec

/-- info: 'NativeRustcVmArm.Wire.Decode.decode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Wire.Decode.decode_spec
