module

public import NativeRustc.Xmss.Verify
public import NativeRustc.Sphincs.Verify

/-!
# The byte models' axioms

The models of the Rust code are the statement's verifiers: `NativeRustc.Xmss.verify_eq`
(`xmssVerify` on the input words of a key, a message and a signature is
`LeanXmss.verifyWithKeccak`) and `NativeRustc.Sphincs.verify_eq` (`sphincsVerify`,
`Sphincs.verifyWithKeccak`), on the `Hasher`'s (`holds_new`, `holds_update`, `finalize_eq`). The
build fails if their axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustc.Xmss.verify_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Xmss.verify_eq

/-- info: 'NativeRustc.Sphincs.verify_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Sphincs.verify_eq

/-- info: 'NativeRustc.Keccak.holds_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Keccak.holds_update

/-- info: 'NativeRustc.Keccak.finalize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Keccak.finalize_eq
