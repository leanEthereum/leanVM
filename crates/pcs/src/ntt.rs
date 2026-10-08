// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT over `K` (Lin-Chung-Han novel polynomial basis) that WHIR commits with.

pub(crate) mod additive_ntt_f64;
pub use additive_ntt_f64::AdditiveNttF64;
pub(crate) use additive_ntt_f64::RowSink;
