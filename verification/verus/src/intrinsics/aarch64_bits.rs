//! Specifications of the AArch64 intrinsics of the bit transposes (the four-register table lookup, the 64-bit
//! lane shifts and AND, the reinterprets between byte and word lanes), and the byte loads and stores of their
//! kernel.
//!
//! A `uint8x16_t` is viewed as its 16 bytes, lane 0 first ([`u8x16`]), a `uint64x2_t` as its two words
//! ([`super::aarch64::u64x2`]). `tests/equivalence/intrinsics_aarch64_bits.rs` runs each against the hardware.
#[cfg(verus_keep_ghost)]
use super::aarch64::u64x2;
#[cfg(verus_keep_ghost)]
use super::transmuted;
use core::arch::aarch64::*;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint8x16(uint8x16_t);

#[verifier::external_type_specification]
pub struct ExUint8x16x4(uint8x16x4_t);

// ---------------------------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------------------------
/// The 16 bytes of a `uint8x16_t`, lane 0 first.
pub open spec fn u8x16(v: uint8x16_t) -> [u8; 16] {
    transmuted::<uint8x16_t, [u8; 16]>(v)
}

/// Byte `k` of a sequence of 64-bit lanes, little-endian.
pub open spec fn u64x2_byte(w: Seq<u64>, k: int) -> u8 {
    (w[k / 8] >> ((8 * (k % 8)) as u64)) as u8
}

// ---------------------------------------------------------------------------------------------
// Lane semantics
// ---------------------------------------------------------------------------------------------
/// Byte `i` of the 64-byte table of `vqtbl4q_u8`, the four registers in order; zero from 64 on.
pub open spec fn tbl4_byte(t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, i: int) -> u8 {
    if i < 16 {
        t0[i]
    } else if i < 32 {
        t1[i - 16]
    } else if i < 48 {
        t2[i - 32]
    } else if i < 64 {
        t3[i - 48]
    } else {
        0
    }
}

/// A logical right shift of a 64-bit lane by `vshrq_n_u64`'s immediate (1 to 64): zero at 64.
pub open spec fn shr_n(a: u64, n: int) -> u64 {
    if 0 <= n < 64 {
        a >> (n as u64)
    } else {
        0
    }
}

/// A left shift of a 64-bit lane by `vshlq_n_u64`'s immediate (0 to 63).
pub open spec fn shl_n(a: u64, n: int) -> u64 {
    if 0 <= n < 64 {
        a << (n as u64)
    } else {
        0
    }
}

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
/// TBL with four table registers: byte `k` is byte `b[k]` of the 64-byte table, or zero if `b[k] >= 64`.
pub assume_specification[ vqtbl4q_u8 ](a: uint8x16x4_t, b: uint8x16_t) -> (r: uint8x16_t)
    ensures
        forall|k: int|
            0 <= k < 16 ==> #[trigger] u8x16(r)[k] == tbl4_byte(
                u8x16(a.0)@,
                u8x16(a.1)@,
                u8x16(a.2)@,
                u8x16(a.3)@,
                u8x16(b)[k] as int,
            ),
;

/// The 16 bytes read as two little-endian words.
pub assume_specification[ vreinterpretq_u64_u8 ](a: uint8x16_t) -> (r: uint64x2_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u64x2_byte(u64x2(r)@, k) == u8x16(a)[k],
;

/// The two words read as 16 bytes, little-endian.
pub assume_specification[ vreinterpretq_u8_u64 ](a: uint64x2_t) -> (r: uint8x16_t)
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == u64x2_byte(u64x2(a)@, k),
;

pub assume_specification[ vandq_u64 ](a: uint64x2_t, b: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == u64x2(a)[0] & u64x2(b)[0],
        u64x2(r)[1] == u64x2(a)[1] & u64x2(b)[1],
;

pub assume_specification<const N: i32>[ vshrq_n_u64::<N> ](a: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == shr_n(u64x2(a)[0], N as int),
        u64x2(r)[1] == shr_n(u64x2(a)[1], N as int),
;

pub assume_specification<const N: i32>[ vshlq_n_u64::<N> ](a: uint64x2_t) -> (r: uint64x2_t)
    ensures
        u64x2(r)[0] == shl_n(u64x2(a)[0], N as int),
        u64x2(r)[1] == shl_n(u64x2(a)[1], N as int),
;

// ---------------------------------------------------------------------------------------------
// Loads and stores of byte arrays
// ---------------------------------------------------------------------------------------------
/// `vld1q_u8` of a 16-byte array.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u8_16(x: &[u8; 16]) -> (r: uint8x16_t)
    ensures
        u8x16(r) == *x,
{
    // SAFETY: the load reads the 16 bytes of `x`.
    unsafe { vld1q_u8(x.as_ptr()) }
}

/// `vld1q_u8` of the 16 bytes of a 64-byte array from `offset` on.
#[verifier::external_body]
#[inline(always)]
pub fn vld1q_u8_at(x: &[u8; 64], offset: usize) -> (r: uint8x16_t)
    requires
        offset <= 48,
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] u8x16(r)[k] == x[offset + k],
{
    // SAFETY: `offset + 16 <= 64`: the load reads within `x`.
    unsafe { vld1q_u8(x.as_ptr().add(offset)) }
}

/// `vst1q_u8` into the 16 bytes of a 64-byte array from `offset` on.
#[verifier::external_body]
#[inline(always)]
pub fn vst1q_u8_at(x: &mut [u8; 64], offset: usize, v: uint8x16_t)
    requires
        offset <= 48,
    ensures
        forall|k: int|
            0 <= k < 64 ==> #[trigger] final(x)[k] == if offset <= k < offset + 16 {
                u8x16(v)[k - offset]
            } else {
                old(x)[k]
            },
{
    // SAFETY: `offset + 16 <= 64`: the store writes within `x`.
    unsafe { vst1q_u8(x.as_mut_ptr().add(offset), v) }
}

// ---------------------------------------------------------------------------------------------
// Executable twins of the lane semantics, for the differential tests
// ---------------------------------------------------------------------------------------------
/// [`tbl4_byte`].
pub fn model_tbl4_byte(t: &[u8], i: u8) -> (r: u8)
    requires
        t.len() == 64,
    ensures
        r == tbl4_byte(t@.subrange(0, 16), t@.subrange(16, 32), t@.subrange(32, 48), t@.subrange(48, 64), i as int),
{
    if i < 64 {
        t[i as usize]
    } else {
        0
    }
}

/// [`u64x2_byte`].
pub fn model_u64x2_byte(w: &[u64], k: usize) -> (r: u8)
    requires
        k < 8 * w.len(),
    ensures
        r == u64x2_byte(w@, k as int),
{
    (w[k / 8] >> (8 * (k % 8)) as u64) as u8
}

/// [`shr_n`].
pub fn model_shr_n(a: u64, n: i32) -> (r: u64)
    ensures
        r == shr_n(a, n as int),
{
    if 0 <= n && n < 64 {
        a >> (n as u64)
    } else {
        0
    }
}

/// [`shl_n`].
pub fn model_shl_n(a: u64, n: i32) -> (r: u64)
    ensures
        r == shl_n(a, n as int),
{
    if 0 <= n && n < 64 {
        a << (n as u64)
    } else {
        0
    }
}

} // verus!
