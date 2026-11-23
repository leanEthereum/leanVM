module

public import NativeRustcVmX64.Keccak.KeccakF
public import NativeRustcVmX64.Keccak.IvWord
public import NativeRustcVmX64.Keccak.HashPair
public import NativeRustcVmX64.Keccak.WordsHash
public import NativeRustcVmX64.Keccak.WordsIv

/-!
# The Keccak functions of `leanvm_verify`'s x86-64 program

`keccak_f`, `iv_word`, `hash_pair` and both `keccak256_words` instances meet their contracts
(`NativeRustcVmX64.keccakF_spec`, `NativeRustcVmX64.IvWordRun.ivWord_spec`,
`NativeRustcVmX64.HashPairRun.hashPair_spec`, `NativeRustcVmX64.keccak256WordsHash_spec`,
`NativeRustcVmX64.keccak256WordsIv_spec`; statements in `NativeRustcVmX64/Spec/Keccak.lean`), with Lean's three axioms only.
-/

/--
info: 'NativeRustcVmX64.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.keccakF_spec

/--
info: 'NativeRustcVmX64.IvWordRun.ivWord_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.IvWordRun.ivWord_spec

/--
info: 'NativeRustcVmX64.HashPairRun.hashPair_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.HashPairRun.hashPair_spec

/--
info: 'NativeRustcVmX64.keccak256WordsHash_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.keccak256WordsHash_spec

/--
info: 'NativeRustcVmX64.keccak256WordsIv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.keccak256WordsIv_spec
