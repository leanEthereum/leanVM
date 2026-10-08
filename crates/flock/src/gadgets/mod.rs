//! u64 arithmetic in the gate-list language: multiplication, wrapping or widening.
//!
//! A gadget takes wires and returns wires, so gadgets compose into larger circuits.
//! Its witness is word arithmetic on the structure its gate list is built from, never the generic walk.

pub mod mul;
