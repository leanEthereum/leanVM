// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system over GF(2), reduced to evaluation claims on the committed packed witness.
//!
//! The protocol, every challenge drawn from the shared transcript:
//!
//! 1. The caller commits every circuit's packed Boolean witness, inside the VM's one stacked commitment.
//! 2. The zerocheck reduces `a·b ⊕ c = 0` over every circuit's cube to claims on its `(â, b̂, ĉ)`.
//! 3. The lincheck reduces those to the bit-slice values of each circuit's `z` at one point.
//! 4. The commitment's opening binds each circuit's slices.
//!
//! One prover and one verifier take any batch of circuits, each a witness over its block.
//!
//! Both sumchecks batch every circuit under shared challenges.
//! Steps 2 to 4 take a circuit's block shape as plain numbers, and reach its matrices only by walking its gate list.
//!
//! Circuits are gate lists over word ports, with u64 addition and multiplication as gadgets.
//! The leanVM's instruction classes are written in them.
//!
//! The hand-optimized BLAKE2s circuit, with its own witness kernels, is flock's throughput benchmark and nothing else.
//! It, the standalone u64 circuits and the walk-only witness entry point build only for tests and the `bench` feature.

#![warn(unreachable_pub)]

pub mod arith;
pub mod circuit;
#[cfg(any(test, feature = "bench"))]
mod gf2;
#[cfg(any(test, feature = "bench"))]
pub mod hash;
pub mod lincheck;
pub mod reduction;
/// The BLAKE2s circuit driven through the whole reduction.
/// It is a source module rather than a test binary, so it shares the unit tests' process.
#[cfg(test)]
mod reduction_tests;
pub mod verifier;
mod witness;
pub mod zerocheck;

pub use witness::Witness;
