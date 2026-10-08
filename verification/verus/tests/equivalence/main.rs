//! Differential checks between executable verified copies, intrinsic models and production.
//!
//! Edge, exhaustive small-domain and deterministic random cases can detect divergence but do not prove
//! source equivalence or guarantee that future copy drift will be caught.

mod bit_fold;
mod bits;
mod blake2s;
mod blake2s_batch;
mod fiat_shamir;
mod flock_ntt;
mod gf2_64;
mod gf2_64x3;
mod gf2_8;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64_bits;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64_gfneon;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64_nttsimd;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86_bits;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86_gfneon;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86_gfx86;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86_nttsimd;
mod multilinear;
mod ntt;
mod ntt_driver;
mod ntt_simd;
mod phi8_tower;
mod skip_domain;
