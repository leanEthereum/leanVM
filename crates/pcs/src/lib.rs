// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! - Boolean witnesses are packed into words of `K = GF(2^64)`.
//! - WHIR commits to them and opens them over the cubic extension `E = GF(2^192)`.

#![deny(clippy::float_arithmetic, clippy::cast_precision_loss)]
#![warn(unreachable_pub)]

pub mod merkle;
pub mod ntt;
pub mod ring_switch;
pub mod stack_open;
pub mod verifier;
pub mod whir;
