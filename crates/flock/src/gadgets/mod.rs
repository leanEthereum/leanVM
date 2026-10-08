//! u64 arithmetic in the gate-list language: wrapping addition, and multiplication wrapping or widening.
//!
//! A gadget takes wires and returns wires, so gadgets compose into larger circuits.
//! Its witness is word arithmetic on the structure its gate list is built from, never the generic walk.

#[cfg(any(test, feature = "bench"))]
pub(crate) mod add;
pub mod mul;
#[cfg(any(test, feature = "bench"))]
mod u64_circuit;

#[cfg(any(test, feature = "bench"))]
pub use u64_circuit::{U64Circuit, U64Op};
