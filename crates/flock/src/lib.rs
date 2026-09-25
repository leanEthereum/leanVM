// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`fiat_shamir`] transcript):
//!   1. The caller commits the packed Boolean witness `q_flock` (inside the VM's
//!      one stacked [`pcs`] commitment).
//!   2. [`zerocheck`] reduces `a·b ⊕ c = 0` over the cube to evaluation claims
//!      on `(â, b̂, ĉ)`.
//!   3. [`lincheck`] reduces those to the `2^k_skip` bit-slice values of `z` at
//!      one point, against the per-block matrices.
//!   4. The PCS binds that family of slices ([`hash::SliceClaim`]) to the
//!      commitment.
//!
//! Two circuits, each a per-block R1CS with its witness generation and the
//! leanVM-facing reduction entry points (`Setup::{prove_reduction,
//! verify_reduction, …}`): [`hash`], the BLAKE2s compression (the `BLAKE2s`
//! opcode, the VM's general hash), and [`keccak`], the Keccak-f step (the `SHA3`
//! opcode, for the SPHINCS+ profile's Keccak-256). Steps 2 to 4 above are
//! circuit-agnostic: they take the block shape as plain numbers and reach the
//! matrices only through [`lincheck::LincheckCircuit`], whose impls walk the
//! circuit rather than reading any matrix.
//!
//! BLAKE2s is a 32-bit ARX round whose XORs and rotations are free over GF(2),
//! so its only nonlinear constraints are the product bits of the modular ADDs.
//! The private `gf2` module owns that part: the wire word and the two adder
//! gadgets, forwards and transposed, kept separate because the fused
//! three-operand adder's bit boundaries are the subtlest thing here.
//!
//! Keccak-f's θ, ρ, π and ι are linear over GF(2), so its only nonlinear
//! constraints are χ's products, one per state bit per round. The private `gf2k`
//! module owns the symbolic lane those affine forms are carried in.

mod gf2;
mod gf2k;
pub mod hash;
pub mod keccak;
#[cfg(test)]
mod keccak_reduction_tests;
pub mod lincheck;
/// The circuit driven through the whole reduction. A `src` module rather than
/// its own test binary so it shares the process with the unit tests.
#[cfg(test)]
mod reduction_tests;
pub mod verifier;
mod witness;
pub mod zerocheck;
