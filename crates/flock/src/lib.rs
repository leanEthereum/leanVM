// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system over GF(2), reduced to evaluation claims on a committed packed witness.
//!
//! Every challenge comes from one shared transcript:
//!
//! ```text
//!     1. caller      commits every circuit's packed Boolean witness, inside one stacked commitment
//!     2. zerocheck   a b + c = 0 over every circuit's cube, reduced to claims on its (a, b, c) at one point
//!     3. lincheck    those claims, against the circuit's matrices, reduced to the bit slices of its z at one point
//!     4. caller      the commitment's opening binds each circuit's slices
//! ```
//!
//! One prover and one verifier take any batch of circuits, each a witness over its block.
//! Both sumchecks batch every circuit under shared challenges.
//! The reduction reads a circuit's shape as plain numbers, and reaches its matrices only by walking its gate list.
//!
//! Circuits are gate lists over word ports, with u64 addition and multiplication as gadgets.
//! The leanVM's instruction classes are written in them.
//!
//! The hand-optimized BLAKE2s circuit is flock's throughput benchmark and nothing else.
//! It and the standalone u64 circuits build only for tests and the `bench` feature.

#![warn(unreachable_pub)]

pub mod circuit;
mod error;
pub mod gadgets;
#[cfg(any(test, feature = "bench"))]
mod gf2;
#[cfg(any(test, feature = "bench"))]
pub mod hash;
pub mod lincheck;
pub mod reduction;
mod witness;
pub mod zerocheck;

pub use error::FlockError;
pub use witness::{Tables, Witness};
