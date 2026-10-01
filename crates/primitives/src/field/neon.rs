//! Small AArch64 SIMD helpers shared by the NEON kernels.
//!
//! The ARMv8.2 SHA3 extension, present on every Apple M core and enabled by
//! the workspace's `-C target-cpu=native`, provides `EOR3`, a three-way XOR
//! in one instruction. The binary-field kernels are XOR-dominated, so folding
//! pairs of dependent `EOR`s into single `EOR3`s cuts both instruction count
//! and dependency-chain length in the hot loops. Builds without the extension
//! transparently keep the two-`EOR` form.
//!
//! (`sha3` is the name of the ARMv8.2 feature *block* that carries `EOR3`,
//! not a reference to the hash function. This crate hashes with BLAKE2s.)

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
    // SAFETY: NEON is part of the aarch64 baseline; registers only.
    unsafe { veorq_u64(a, veorq_u64(b, c)) }
}
