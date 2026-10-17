//! The hash-based signature schemes leanVM aggregates: leanXMSS, stateful, and
//! leanSPHINCS, stateless. Both hash with the same tweakable hash and address layout,
//! so the recursion guest verifies both with one WOTS+C walk and one Merkle step.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

pub mod lean_sphincs;
pub mod lean_xmss;
mod tweak;
