module

public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset
public import NativeRustcArm.KeccakF.Spec
public import NativeRustcArm.Hasher.Update
public import NativeRustcArm.Hasher.Finalize
public import NativeRustcArm.Sphincs
public import NativeRustcArm.Xmss
public import NativeRustcArm.Rodata

/-!
# The rustc-compiled verifiers on AArch64

The deployed `lean_xmss::verify` and `lean_sphincs::verify`, compiled by the pinned rustc
(`rustc/build.sh`) to AArch64 assembly, ingested as Kraken programs (`NativeRustcArm.Code`,
`RustcIngest`, during elaboration from committed full assembly, checked against rustc's full
assembly by `rustc/ingest/faithful.sh`) and proved against
Kraken's semantics function by function: each function's contract (`NativeRustcArm.Spec`), proved
from its blocks run by the verified symbolic executor (`NativeRustcArm.Sym`) and its callees'
contracts. The build fails if an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcArm.Mem.Memcpy.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Mem.Memcpy.memcpy_spec

/-- info: 'NativeRustcArm.Mem.Memset.memset_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Mem.Memset.memset_spec

/-- info: 'NativeRustcArm.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.keccakF_spec

/-- info: 'NativeRustcArm.Hasher.Update.update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Hasher.Update.update_spec

/-- info: 'NativeRustcArm.Hasher.Finalize.finalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Hasher.Finalize.finalize_spec

/-- info: 'NativeRustcArm.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.SphincsVerifier.verify_correct

/-- info: 'NativeRustcArm.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.XmssVerifier.verify_correct

/-- info: 'NativeRustcArm.Xmss.rc_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Xmss.rc_data

/-- info: 'NativeRustcArm.Sphincs.rc_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Sphincs.rc_data

/-- info: 'NativeRustcArm.Sphincs.lh_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcArm.Sphincs.lh_data
