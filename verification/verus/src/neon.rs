//! The AArch64 helper shared by the NEON kernels, `crates/primitives/src/field/neon.rs`, copied with the same
//! bodies.
#[cfg(verus_keep_ghost)]
use crate::intrinsics::aarch64::*;
use core::arch::aarch64::*;
use vstd::prelude::*;

verus! {

/// Three-way XOR of 64-bit-lane vectors.
///
/// # Safety
/// Requires the `sha3` target feature on the EOR3 arm (statically satisfied by
/// the `cfg` gate); the fallback arm has no requirement.
#[cfg(target_feature = "sha3")]
#[inline(always)]
pub unsafe fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] ^ u64x2(b)[0] ^ u64x2(c)[0],
        u64x2(r)[1] == u64x2(a)[1] ^ u64x2(b)[1] ^ u64x2(c)[1],
{
    // SAFETY: `sha3` is statically enabled by the cfg gate.
    unsafe { veor3q_u64(a, b, c) }
}

/// Two-`EOR` fallback for targets without the SHA3 extension.
///
/// # Safety
/// No requirements; `unsafe` only to match the EOR3 arm's signature.
#[cfg(not(target_feature = "sha3"))]
#[inline(always)]
pub unsafe fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] ^ u64x2(b)[0] ^ u64x2(c)[0],
        u64x2(r)[1] == u64x2(a)[1] ^ u64x2(b)[1] ^ u64x2(c)[1],
{
    proof {
        let (a0, b0, c0, a1, b1, c1) = (u64x2(a)[0], u64x2(b)[0], u64x2(c)[0], u64x2(a)[1], u64x2(b)[1], u64x2(c)[1]);
        assert(a0 ^ (b0 ^ c0) == a0 ^ b0 ^ c0 && a1 ^ (b1 ^ c1) == a1 ^ b1 ^ c1) by (bit_vector);
    }
    // SAFETY: NEON is part of the aarch64 baseline; registers only.
    unsafe { veorq_u64(a, veorq_u64(b, c)) }
}

} // verus!
