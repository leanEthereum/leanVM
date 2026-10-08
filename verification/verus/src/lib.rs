//! Verus proofs of annotated leanVM arithmetic and kernel copies, with explicit intrinsic trust contracts.
#![allow(unused_parens, unused_imports, unused_variables, dead_code, clippy::all)]

pub mod bit_fold;
pub mod bits;
pub mod blake2s;
pub mod blake2s_batch;
pub mod clmul;
pub mod fiat_shamir;
pub mod flock_ntt;
pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod intrinsics;
pub mod multilinear;
#[cfg(target_arch = "aarch64")]
pub mod neon;
pub mod ntt;
pub mod ntt_driver;
pub mod ntt_lanes;
pub mod ntt_simd;
pub mod parallel;
pub mod phi8_tower;
pub mod skip_domain;
