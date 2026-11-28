//! AArch64 helpers shared by the NEON kernels: a three-way XOR, one `EOR3` with the ARMv8.2 `sha3` feature, two `EOR`s
//! without.

use core::arch::aarch64::*;

/// Three-way XOR of 64-bit-lane vectors.
///
/// # Safety
/// Requires the `sha3` target feature on the EOR3 arm (statically satisfied by
/// the `cfg` gate); the fallback arm has no requirement.
#[cfg(target_feature = "sha3")]
#[inline(always)]
pub unsafe fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    // SAFETY: `sha3` is statically enabled by the cfg gate.
    unsafe { veor3q_u64(a, b, c) }
}

/// Two-`EOR` fallback for targets without the SHA3 extension.
///
/// # Safety
/// No requirements; `unsafe` only to match the EOR3 arm's signature.
#[cfg(not(target_feature = "sha3"))]
#[inline(always)]
pub unsafe fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    // SAFETY: NEON is baseline on aarch64.
    unsafe { veorq_u64(a, veorq_u64(b, c)) }
}
