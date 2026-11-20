module

public import Rv64mc.Model.Clmul
public import Rv64mc.Model.Field
public import Rv64mc.Model.Multilinear

/-!
# Mirrors of the Rust verifier

One Lean function per function of `crates/verifier`, following the Rust's computation (its loops,
accumulators and early exits) on machine words, each proved equal to its counterpart in the
statement (`Statement/LeanVmVerifier.lean`, `Statement/Field.lean`, `Statement/Keccak.lean`) or,
for an internal helper, to what its caller's proof needs. The machine-code proofs target these
mirrors. A module per Rust module: `Field` (`field.rs`, with `Clmul` for `clmul_low`),
`Multilinear` (`multilinear.rs`).
-/
