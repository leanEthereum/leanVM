module

public import NativeRustcVmX64.Wire.ReaderLe
public import NativeRustcVmX64.Wire.ReaderDigest
public import NativeRustcVmX64.Wire.ReaderWords
public import NativeRustcVmX64.Wire.InsD
public import NativeRustcVmX64.Wire.Find
public import NativeRustcVmX64.Wire.RdRows
public import NativeRustcVmX64.Wire.ClimbLevel

/-!
# `wire.rs` on x86-64

The contracts (`NativeRustcVmX64.Spec.Wire`) of rustc's wire decoder, met:
`Wire.ReaderLe.readerLe_spec`, `Wire.ReaderDigest.readerDigest_spec`,
`Wire.ReaderWords.readerWords_spec`, `Wire.InsD.insD_spec`, `Wire.Find.find_spec`,
`Wire.RdRows.rdRows_spec`, `Wire.ClimbLevel.climbLevel_spec`.
-/

/-- info: 'NativeRustcVmX64.Wire.ReaderLe.readerLe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.ReaderLe.readerLe_spec

/-- info: 'NativeRustcVmX64.Wire.ReaderDigest.readerDigest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.ReaderDigest.readerDigest_spec

/-- info: 'NativeRustcVmX64.Wire.ReaderWords.readerWords_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.ReaderWords.readerWords_spec

/-- info: 'NativeRustcVmX64.Wire.InsD.insD_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.InsD.insD_spec

/-- info: 'NativeRustcVmX64.Wire.Find.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.Find.find_spec

/-- info: 'NativeRustcVmX64.Wire.RdRows.rdRows_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.RdRows.rdRows_spec

/-- info: 'NativeRustcVmX64.Wire.ClimbLevel.climbLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Wire.ClimbLevel.climbLevel_spec
