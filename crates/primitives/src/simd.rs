//! The audited unsafe surface of the AVX-512 code: vector constants, reinterprets and memory moves.
//!
//! A register intrinsic is safe inside a `#[target_feature]` function, so a kernel carries the attribute
//! and moves data through these functions, not through raw pointers. The functions are plain, so any
//! code compiled with `avx512f` calls them.

use core::arch::x86_64::*;

use crate::Plain;

/// The vector of eight words, the first in the low qword.
pub const fn from_words(w: [u64; 8]) -> __m512i {
    // SAFETY: both types are 64 bytes and every bit pattern is a valid vector.
    unsafe { core::mem::transmute::<[u64; 8], __m512i>(w) }
}

/// The eight words of a vector, the low qword first.
#[inline(always)]
pub fn to_words(v: __m512i) -> [u64; 8] {
    // SAFETY: both types are 64 bytes and every bit pattern is a valid array.
    unsafe { core::mem::transmute::<__m512i, [u64; 8]>(v) }
}

/// Register `i` of `src`: bytes `64 * i..64 * i + 64`, read unaligned.
#[inline(always)]
pub fn load<T: Plain>(src: &[T], i: usize) -> __m512i {
    assert!(i < size_of_val(src) / 64);
    // SAFETY: the assert keeps the 64 bytes inside `src`, and any bytes of a `Plain` type are readable.
    unsafe { _mm512_loadu_si512(src.as_ptr().cast::<u8>().wrapping_add(64 * i).cast()) }
}

/// Write `v` over register `i` of `dst`: bytes `64 * i..64 * i + 64`, unaligned.
#[inline(always)]
pub fn store<T: Plain>(dst: &mut [T], i: usize, v: __m512i) {
    assert!(i < size_of_val(dst) / 64);
    // SAFETY: the assert keeps the 64 bytes inside `dst`, and any bytes are a valid `Plain` value.
    unsafe { _mm512_storeu_si512(dst.as_mut_ptr().cast::<u8>().add(64 * i).cast(), v) }
}

/// The 8x8 transpose of qwords: qword `j` of `out[p]` is qword `p` of `r[j]`.
#[inline(always)]
pub fn transpose8(r: [__m512i; 8]) -> [__m512i; 8] {
    // SAFETY: the module is compiled only with avx512f enabled, and these intrinsics touch only registers.
    unsafe {
        // Pairs of words, then 128-bit lane picks to finish.
        let (a0, a1) = (_mm512_unpacklo_epi64(r[0], r[1]), _mm512_unpackhi_epi64(r[0], r[1]));
        let (a2, a3) = (_mm512_unpacklo_epi64(r[2], r[3]), _mm512_unpackhi_epi64(r[2], r[3]));
        let (a4, a5) = (_mm512_unpacklo_epi64(r[4], r[5]), _mm512_unpackhi_epi64(r[4], r[5]));
        let (a6, a7) = (_mm512_unpacklo_epi64(r[6], r[7]), _mm512_unpackhi_epi64(r[6], r[7]));
        let b0 = _mm512_shuffle_i64x2::<0x88>(a0, a2);
        let b1 = _mm512_shuffle_i64x2::<0x88>(a1, a3);
        let b2 = _mm512_shuffle_i64x2::<0xDD>(a0, a2);
        let b3 = _mm512_shuffle_i64x2::<0xDD>(a1, a3);
        let b4 = _mm512_shuffle_i64x2::<0x88>(a4, a6);
        let b5 = _mm512_shuffle_i64x2::<0x88>(a5, a7);
        let b6 = _mm512_shuffle_i64x2::<0xDD>(a4, a6);
        let b7 = _mm512_shuffle_i64x2::<0xDD>(a5, a7);
        [
            _mm512_shuffle_i64x2::<0x88>(b0, b4),
            _mm512_shuffle_i64x2::<0x88>(b1, b5),
            _mm512_shuffle_i64x2::<0x88>(b2, b6),
            _mm512_shuffle_i64x2::<0x88>(b3, b7),
            _mm512_shuffle_i64x2::<0xDD>(b0, b4),
            _mm512_shuffle_i64x2::<0xDD>(b1, b5),
            _mm512_shuffle_i64x2::<0xDD>(b2, b6),
            _mm512_shuffle_i64x2::<0xDD>(b3, b7),
        ]
    }
}

/// The bitwise XOR.
#[inline(always)]
pub fn xor(a: __m512i, b: __m512i) -> __m512i {
    // SAFETY: the module is compiled only with avx512f enabled.
    unsafe { _mm512_xor_si512(a, b) }
}

/// The first `n <= 8` words of register `i` of `src`, and zeros after them.
///
/// Only those words must lie inside `src`: a register may hang over its end, or start past it with `n == 0`.
#[inline(always)]
pub fn load_prefix<T: Plain>(src: &[T], i: usize, n: usize) -> __m512i {
    let words = size_of_val(src) / 8;
    assert!(n <= 8 && (n == 0 || (n <= words && i <= (words - n) / 8)));
    // SAFETY: the assert keeps the first `n` words inside `src`, which is readable for any `Plain` bytes.
    // The masked-out words are not accessed.
    unsafe {
        _mm512_maskz_loadu_epi64(
            ((1u16 << n) - 1) as u8,
            src.as_ptr().cast::<u8>().wrapping_add(64 * i).cast(),
        )
    }
}

/// Write the first `n <= 8` words of `v` over register `i` of `dst`, and leave the others as they are.
///
/// Only those words must lie inside `dst`.
#[inline(always)]
pub fn store_prefix<T: Plain>(dst: &mut [T], i: usize, n: usize, v: __m512i) {
    let words = size_of_val(dst) / 8;
    assert!(n <= 8 && (n == 0 || (n <= words && i <= (words - n) / 8)));
    // SAFETY: the assert keeps the first `n` words inside `dst`, and any bytes are a valid `Plain` value.
    unsafe {
        _mm512_mask_storeu_epi64(
            dst.as_mut_ptr().cast::<u8>().wrapping_add(64 * i).cast(),
            ((1u16 << n) - 1) as u8,
            v,
        )
    }
}
