//! Spartan over binary fields for R1CS exported from Clean circuits, prover side.
//!
//! A Clean circuit over GF(2) is one block `(A_0, B_0, C_0)`; a batch proves `2^n_log`
//! instances of it, `A = I ⊗ A_0` and likewise for B and C (SIMD R1CS). The outer
//! sumcheck is flock's zerocheck, the inner sumcheck flock's lincheck with a general
//! `C_0`, and the packed witness is committed and opened with `pcs` (ring switching
//! into stacked WHIR). The block matrices' evaluation is either computed by the
//! verifier directly or proven with [`spark`]. The verifier is `verifier::binary_spartan`,
//! which [`proof::verify`] calls.

pub mod block;
pub mod format;
pub mod proof;
pub mod spark;
