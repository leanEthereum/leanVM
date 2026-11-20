module

public import Rv64mc.Model.Clmul
public import Rv64mc.Model.Field
public import Rv64mc.Model.Multilinear
public import Rv64mc.Model.Hash
public import Rv64mc.Model.Merkle
public import Rv64mc.Model.Sponge
public import Rv64mc.Model.Transcript
public import Rv64mc.Model.RingSwitch
public import Rv64mc.Model.KeccakGkr
public import Rv64mc.Model.Whir
public import Rv64mc.Model.Layout
public import Rv64mc.Model.Bytecode
public import Rv64mc.Model.Bus

/-!
# Mirrors of the Rust verifier

One Lean function per function of `crates/verifier`, following the Rust's computation (its loops,
accumulators and early exits) on machine words, each proved equal to its counterpart in the
statement (`Statement/LeanVmVerifier.lean`, `Statement/Field.lean`, `Statement/Keccak.lean`) or,
for an internal helper, to what its caller's proof needs. The machine-code proofs target these
mirrors. A module per Rust module: `Field` (`field.rs`, with `Clmul` for `clmul_low`),
`Multilinear` (`multilinear.rs`), `Hash` (`hash.rs`), `Merkle` (`merkle.rs`), and `Sponge` and
`Transcript` (`transcript.rs`); `Tests` checks them on the Rust's test vectors.

The mirrored Rust is `crates/verifier` at commit `1135c5255`; `scripts/model-drift.sh` fails when
a mirrored file changes. The build fails if the axiom footprint of the main equalities grows
beyond Lean's three.
-/

/-- info: 'Rv64mc.Model.eMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.eMul_eq

/-- info: 'Rv64mc.Model.eInv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.eInv_eq

/-- info: 'Rv64mc.Model.scaledMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.scaledMul_eq

/--
info: 'Rv64mc.Model.eqKernelRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.eqKernelRust_eq

/--
info: 'Rv64mc.Model.multilinearEvalRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.multilinearEvalRust_eq

/--
info: 'Rv64mc.Model.keccakHashRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.keccakHashRust_eq

/-- info: 'Rv64mc.Model.rootRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.rootRust_eq

/-- info: 'Rv64mc.Model.merkle_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.merkle_run

/-- info: 'Rv64mc.Model.Sim.sumcheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Model.Sim.sumcheck

/--
info: 'Rv64mc.Model.runProof_of_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.runProof_of_sim

/--
info: 'Rv64mc.Model.stackOffsetsRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.stackOffsetsRust_eq
