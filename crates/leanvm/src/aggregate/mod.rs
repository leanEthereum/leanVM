//! Aggregation trees: many proofs of one program, verified as one.
//!
//! # Overview
//!
//! ```text
//!                 node                  verifies `arity` tree proofs, of either kind
//!               /      \
//!        first-level   first-level      each verifies `arity_0` proofs of the program
//!          /  \          /  \
//!       leaf  leaf    leaf  leaf
//! ```
//!
//! Every tree proof states the same few hundred words:
//!
//! - a digest of its leaves' outputs,
//! - claims that only the root's verifier evaluates.
//!
//! A tree over one leaf, with `arity_0 = 1`, is a single proof's recursion.

mod leaf;
mod proof;
mod stats;
mod tree;

pub use leaf::{Leaf, LeafShape};
pub use leanvm_core::rec::tree::{DensePoly, FalseClaim, Kind, TreeError};
pub use proof::TreeProof;
pub use stats::{CircuitStats, TableStats};
pub use tree::{Tree, TreeShape};
