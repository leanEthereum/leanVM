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
//! Circuits are gate lists over word ports, with u64 multiplication as a gadget.
//! The leanVM's instruction classes are written in them.

#![warn(unreachable_pub)]

pub mod circuit;
pub mod clean;
pub mod gadgets;
pub mod lincheck;
pub mod reduction;
mod round;
#[cfg(any(test, feature = "test-util"))]
pub mod test_util;
mod witness;
pub mod zerocheck;

use thiserror::Error;

use crate::lincheck::LincheckError;
use crate::zerocheck::ZerocheckError;

pub use witness::{BatchRows, Tables};

/// Why a flock reduction is refused, by the step that refuses it.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FlockError {
    /// The zerocheck refuses.
    #[error("zerocheck: {0}")]
    Zerocheck(ZerocheckError),

    /// The lincheck refuses.
    #[error("lincheck: {0}")]
    Lincheck(LincheckError),
}
