//! Specifications of the x86-64 intrinsics of the bit transposes (AVX2 byte unpacks, AVX-512 VBMI's byte
//! permute, GFNI's affine map), and the byte loads and stores of their kernels.
//!
//! The views are those of [`super::x86`]: [`m256_bytes`] and [`m512_bytes`] for byte lanes, [`m256`] and
//! [`m512`] for 64-bit words. Each lane function has an executable twin `model_<name>` proven equal to it, which
//! `tests/equivalence/intrinsics_x86_bits.rs` runs against the hardware.
#[cfg(verus_keep_ghost)]
use super::x86::{m128_bytes, m256, m256_bytes, m512, m512_bytes};
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Lane semantics
// ---------------------------------------------------------------------------------------------
/// Byte `k` of `_mm256_unpacklo_epi8(a, b)`: in each 16-byte lane, the low eight bytes of `a` and `b`,
/// interleaved (`a` at the even bytes).
pub open spec fn unpacklo_epi8_lane(a: Seq<u8>, b: Seq<u8>, k: int) -> u8 {
    let j = 16 * (k / 16) + (k % 16) / 2;
    if k % 2 == 0 {
        a[j]
    } else {
        b[j]
    }
}

/// Byte `k` of `_mm256_unpackhi_epi8(a, b)`: in each 16-byte lane, the high eight bytes of `a` and `b`,
/// interleaved (`a` at the even bytes).
pub open spec fn unpackhi_epi8_lane(a: Seq<u8>, b: Seq<u8>, k: int) -> u8 {
    let j = 16 * (k / 16) + 8 + (k % 16) / 2;
    if k % 2 == 0 {
        a[j]
    } else {
        b[j]
    }
}

/// Byte `k` of `_mm512_permutexvar_epi8(idx, a)`: byte `idx[k] & 63` of `a`, across the whole register.
pub open spec fn permutexvar_epi8_lane(idx: Seq<u8>, a: Seq<u8>, k: int) -> u8 {
    a[(idx[k] & 63) as int]
}

/// The parity of a byte: 1 if it has an odd number of set bits, else 0.
pub open spec fn parity8(x: u8) -> u8 {
    let x = x ^ (x >> 4u8);
    let x = x ^ (x >> 2u8);
    (x ^ (x >> 1u8)) & 1
}

/// Bit `i` of a GF2P8AFFINEQB result byte, as a 0 or 1: the parity of matrix row `m & x`, XOR bit `i` of the
/// immediate.
pub open spec fn affine_bit(m: u8, x: u8, imm8: u8, i: u8) -> u8 {
    parity8(m & x) ^ ((imm8 >> i) & 1)
}

/// GF2P8AFFINEQB on one byte `x` with the matrix word `a`: bit `i` of the result is
/// `parity(byte (7 - i) of a  &  x)  XOR  bit i of imm8`.
pub open spec fn affine_byte(a: u64, x: u8, imm8: u8) -> u8 {
    affine_bit((a >> 56u64) as u8, x, imm8, 0) | (affine_bit((a >> 48u64) as u8, x, imm8, 1) << 1u8) | (affine_bit(
        (a >> 40u64) as u8,
        x,
        imm8,
        2,
    ) << 2u8) | (affine_bit((a >> 32u64) as u8, x, imm8, 3) << 3u8) | (affine_bit((a >> 24u64) as u8, x, imm8, 4)
        << 4u8) | (affine_bit((a >> 16u64) as u8, x, imm8, 5) << 5u8) | (affine_bit((a >> 8u64) as u8, x, imm8, 6)
        << 6u8) | (affine_bit(a as u8, x, imm8, 7) << 7u8)
}

/// Byte `k` of `_mm*_gf2p8affine_epi64_epi8::<IMM8>(x, a)`: byte `k` of `x` through the matrix in the 64-bit
/// word of `a` that byte `k` is in.
pub open spec fn gf2p8affine_lane(x: Seq<u8>, a: Seq<u64>, imm8: u8, k: int) -> u8 {
    affine_byte(a[k / 8], x[k], imm8)
}

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
pub assume_specification[ _mm256_unpacklo_epi8 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == unpacklo_epi8_lane(m256_bytes(a)@, m256_bytes(b)@, k),
;

pub assume_specification[ _mm256_unpackhi_epi8 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == unpackhi_epi8_lane(m256_bytes(a)@, m256_bytes(b)@, k),
;

pub assume_specification[ _mm512_permutexvar_epi8 ](idx: __m512i, a: __m512i) -> (r: __m512i)
    ensures
        forall|k: int|
            0 <= k < 64 ==> #[trigger] m512_bytes(r)[k] == permutexvar_epi8_lane(m512_bytes(idx)@, m512_bytes(a)@, k),
;

pub assume_specification<const B: i32>[ _mm256_gf2p8affine_epi64_epi8::<B> ](x: __m256i, a: __m256i) -> (r: __m256i)
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == gf2p8affine_lane(m256_bytes(x)@, m256(a)@, B as u8, k),
;

pub assume_specification<const B: i32>[ _mm512_gf2p8affine_epi64_epi8::<B> ](x: __m512i, a: __m512i) -> (r: __m512i)
    ensures
        forall|k: int| 0 <= k < 64 ==> #[trigger] m512_bytes(r)[k] == gf2p8affine_lane(m512_bytes(x)@, m512(a)@, B as u8, k),
;

// ---------------------------------------------------------------------------------------------
// Loads and stores of byte arrays
// ---------------------------------------------------------------------------------------------
/// `_mm_loadu_si128` of a 16-byte array.
///
/// # Safety
///
/// Requires the `sse2` target feature.
#[verifier::external_body]
#[inline]
#[target_feature(enable = "sse2")]
pub unsafe fn load128_bytes(x: &[u8; 16]) -> (r: __m128i)
    ensures
        m128_bytes(r) == *x,
{
    unsafe { _mm_loadu_si128(x.as_ptr().cast()) }
}

/// `_mm256_loadu_si256` of the 32 bytes of a 64-byte array from `offset` on.
///
/// # Safety
///
/// Requires the `avx` target feature.
#[verifier::external_body]
#[inline]
#[target_feature(enable = "avx")]
pub unsafe fn load256_bytes_at(x: &[u8; 64], offset: usize) -> (r: __m256i)
    requires
        offset <= 32,
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == x[offset + k],
{
    unsafe { _mm256_loadu_si256(x.as_ptr().add(offset).cast()) }
}

/// `_mm256_storeu_si256` into the 32 bytes of a 64-byte array from `offset` on.
///
/// # Safety
///
/// Requires the `avx` target feature.
#[verifier::external_body]
#[inline]
#[target_feature(enable = "avx")]
pub unsafe fn store256_bytes_at(x: &mut [u8; 64], offset: usize, v: __m256i)
    requires
        offset <= 32,
    ensures
        forall|k: int|
            0 <= k < 64 ==> #[trigger] final(x)[k] == if offset <= k < offset + 32 {
                m256_bytes(v)[k - offset]
            } else {
                old(x)[k]
            },
{
    unsafe { _mm256_storeu_si256(x.as_mut_ptr().add(offset).cast(), v) }
}

/// `_mm512_loadu_si512` of a 64-byte array.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[verifier::external_body]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn load512_bytes(x: &[u8; 64]) -> (r: __m512i)
    ensures
        m512_bytes(r) == *x,
{
    unsafe { _mm512_loadu_si512(x.as_ptr().cast()) }
}

/// `_mm512_storeu_si512` into a 64-byte array.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[verifier::external_body]
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn store512_bytes(x: &mut [u8; 64], v: __m512i)
    ensures
        *final(x) == m512_bytes(v),
{
    unsafe { _mm512_storeu_si512(x.as_mut_ptr().cast(), v) }
}

// ---------------------------------------------------------------------------------------------
// Executable twins of the lane semantics, for the differential tests
// ---------------------------------------------------------------------------------------------
/// [`unpacklo_epi8_lane`].
pub fn model_unpacklo_epi8_lane(a: &[u8], b: &[u8], k: usize) -> (r: u8)
    requires
        a.len() == b.len(),
        a.len() % 16 == 0,
        k < a.len(),
    ensures
        r == unpacklo_epi8_lane(a@, b@, k as int),
{
    let j = 16 * (k / 16) + (k % 16) / 2;
    if k % 2 == 0 {
        a[j]
    } else {
        b[j]
    }
}

/// [`unpackhi_epi8_lane`].
pub fn model_unpackhi_epi8_lane(a: &[u8], b: &[u8], k: usize) -> (r: u8)
    requires
        a.len() == b.len(),
        a.len() % 16 == 0,
        k < a.len(),
    ensures
        r == unpackhi_epi8_lane(a@, b@, k as int),
{
    let j = 16 * (k / 16) + 8 + (k % 16) / 2;
    if k % 2 == 0 {
        a[j]
    } else {
        b[j]
    }
}

/// [`permutexvar_epi8_lane`].
pub fn model_permutexvar_epi8_lane(idx: &[u8], a: &[u8], k: usize) -> (r: u8)
    requires
        idx.len() == 64,
        a.len() == 64,
        k < 64,
    ensures
        r == permutexvar_epi8_lane(idx@, a@, k as int),
{
    let x = idx[k];
    assert(x & 63 < 64) by (bit_vector);
    a[(x & 63) as usize]
}

/// [`parity8`].
pub fn model_parity8(x: u8) -> (r: u8)
    ensures
        r == parity8(x),
{
    let x = x ^ (x >> 4u8);
    let x = x ^ (x >> 2u8);
    (x ^ (x >> 1u8)) & 1
}

/// [`affine_bit`].
pub fn model_affine_bit(m: u8, x: u8, imm8: u8, i: u8) -> (r: u8)
    requires
        i < 8,
    ensures
        r == affine_bit(m, x, imm8, i),
{
    model_parity8(m & x) ^ ((imm8 >> i) & 1)
}

/// [`affine_byte`]: result bit `i` from matrix row `7 - i`.
pub fn model_affine_byte(a: u64, x: u8, imm8: u8) -> (r: u8)
    ensures
        r == affine_byte(a, x, imm8),
{
    model_affine_bit((a >> 56u64) as u8, x, imm8, 0) | (model_affine_bit((a >> 48u64) as u8, x, imm8, 1) << 1u8)
        | (model_affine_bit((a >> 40u64) as u8, x, imm8, 2) << 2u8) | (model_affine_bit((a >> 32u64) as u8, x, imm8, 3)
        << 3u8) | (model_affine_bit((a >> 24u64) as u8, x, imm8, 4) << 4u8) | (model_affine_bit(
        (a >> 16u64) as u8,
        x,
        imm8,
        5,
    ) << 5u8) | (model_affine_bit((a >> 8u64) as u8, x, imm8, 6) << 6u8) | (model_affine_bit(a as u8, x, imm8, 7)
        << 7u8)
}

/// [`gf2p8affine_lane`].
pub fn model_gf2p8affine_lane(x: &[u8], a: &[u64], imm8: u8, k: usize) -> (r: u8)
    requires
        x.len() == 8 * a.len(),
        k < x.len(),
    ensures
        r == gf2p8affine_lane(x@, a@, imm8, k as int),
{
    model_affine_byte(a[k / 8], x[k], imm8)
}

} // verus!
