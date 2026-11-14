// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! Boolean witnesses are packed into `K = GF(2^64)` and WHIR opens them
//! over its quadratic extension `E = GF(2^128)`.

pub mod merkle;
pub mod ntt;
pub mod ood;
pub mod pack;
pub mod ring_switch;
pub mod stack_open;
pub(crate) mod tensor_algebra;
pub mod whir;
pub mod whir_config;
mod whir_induce;
mod whir_lanes;
mod xmul;

pub use pack::LOG_PACKING;

// Merkle leaves and the ring switch read words as their bytes, which are the little-endian ones the verifier hashes.
const _: () = assert!(cfg!(target_endian = "little"));
