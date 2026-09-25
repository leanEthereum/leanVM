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
//! [`hash`] is the protocol's circuit: the BLAKE2s compression as a per-block
//! R1CS, plus its witness generation and the leanVM-facing reduction entry
//! points (`Blake2sSetup::{prove_reduction, verify_reduction, …}`). [`circuit`]
//! is the gate-list vocabulary every other circuit is written in, and [`arith`]
//! holds u64 addition and multiplication in it.
//! Steps 2 to 4 above are
//! circuit-agnostic ([`reduction`]): they take the block shape as plain numbers
//! and reach the matrices only through [`lincheck::LincheckCircuit`], whose
//! impls walk the circuit rather than reading any matrix.
//!
//! BLAKE2s is a 32-bit ARX round whose XORs and rotations are free over GF(2),
//! so its only nonlinear constraints are the product bits of the modular ADDs.
//! The private `gf2` module owns that part: the wire word and the two adder
//! gadgets, forwards and transposed, kept separate because the fused
//! three-operand adder's bit boundaries are the subtlest thing here.

pub mod arith;
pub mod circuit;
mod gf2;
pub mod hash;
pub mod lincheck;
pub mod reduction;
/// The circuit driven through the whole reduction. A `src` module rather than
/// its own test binary so it shares the process, and so the slow
/// [`hash::matrices`] build, with the unit tests.
#[cfg(test)]
mod reduction_tests;
pub mod verifier;
mod witness;
pub mod zerocheck;
