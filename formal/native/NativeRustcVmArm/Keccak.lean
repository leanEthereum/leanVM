module

public import NativeRustcVmArm.Keccak.KeccakF
public import NativeRustcVmArm.Keccak.WordsHash
public import NativeRustcVmArm.Keccak.WordsIv
public import NativeRustcVmArm.Keccak.IvWord
public import NativeRustcVmArm.Keccak.HashPair

/-!
# The Keccak functions of the leanVM verifier on AArch64

`keccak_f`, `keccak256_words` with `hash_words`'s and `fiat_shamir_iv`'s closures, `iv_word` and
`hash_pair` meet their contracts (`NativeRustcVmArm/Spec/Keccak.lean`), with Lean's three axioms
only.
-/

/-- info: 'NativeRustcVmArm.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.keccakF_spec

/--
info: 'NativeRustcVmArm.keccak256WordsHash_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.keccak256WordsHash_spec

/--
info: 'NativeRustcVmArm.keccak256WordsIv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.keccak256WordsIv_spec

/-- info: 'NativeRustcVmArm.ivWord_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.ivWord_spec

/-- info: 'NativeRustcVmArm.hashPair_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.hashPair_spec
