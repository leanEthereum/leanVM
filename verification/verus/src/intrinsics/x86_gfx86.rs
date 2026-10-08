//! Specifications of the x86-64 intrinsics the GF(2^192) kernels (`gf2_64x3::x86_64`) add to [`super::x86`]:
//! 128-bit shifts and shuffles, the AVX2 lane moves and blends, the AVX-512 casts and extracts, and the all-zero
//! value of the accumulator arrays.
//!
//! As in [`super::x86`], each intrinsic's result is given word by word by an open spec function `<intrinsic>_lane`
//! over the [`m128`], [`m256`], [`m512`] views (and [`m256d`] for the one `pd` move), and each non-trivial one has
//! an executable twin `model_<intrinsic>` that `tests/equivalence/intrinsics_x86_gfx86.rs` runs against the hardware.
#[cfg(verus_keep_ghost)]
use super::transmuted;
#[cfg(verus_keep_ghost)]
use super::x86::{m128, m256, m512};
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM256d(__m256d);

// ---------------------------------------------------------------------------------------------
// Views and layout
// ---------------------------------------------------------------------------------------------
/// The four 64-bit words of a 256-bit `pd` register, its bits as they are (no float reading), the low one first.
pub open spec fn m256d(v: __m256d) -> [u64; 4] {
    transmuted::<__m256d, [u64; 4]>(v)
}

/// The value `core::mem::zeroed::<T>()` returns.
///
/// Uninterpreted: the layout axioms below say what it is for the accumulator types the kernels zero.
pub uninterp spec fn zeroed_value<T>() -> T;

/// `core::mem::zeroed` returns [`zeroed_value`].
pub assume_specification<T>[ core::mem::zeroed::<T> ]() -> (r: T)
    ensures
        r == zeroed_value::<T>(),
;

/// Layout: an all-zero array of 512-bit registers has zero words.
pub axiom fn axiom_zeroed_m512<const N: usize>()
    ensures
        forall|i: int, j: int| 0 <= i < N && 0 <= j < 8 ==> #[trigger] m512(zeroed_value::<[__m512i; N]>()[i])[j] == 0,
;

/// Layout: an all-zero pair of arrays of 256-bit registers has zero words.
pub axiom fn axiom_zeroed_m256_pairs<const N: usize>()
    ensures
        forall|h: int, i: int, j: int|
            0 <= h < 2 && 0 <= i < N && 0 <= j < 4 ==> #[trigger] m256(zeroed_value::<[[__m256i; N]; 2]>()[h][i])[j]
                == 0,
;

// ---------------------------------------------------------------------------------------------
// Lane semantics
// ---------------------------------------------------------------------------------------------
/// Doubleword `k` of a sequence of words, little-endian, in the low half of a word.
pub open spec fn dword(a: Seq<u64>, k: int) -> u64 {
    (a[k / 2] >> ((32 * (k % 2)) as u64)) & 0xFFFF_FFFFu64
}

/// The two-bit field `k` of an immediate.
pub open spec fn imm2(imm8: u8, k: int) -> int {
    ((imm8 >> ((2 * k) as u8)) & 3) as int
}

/// Word `i` of `_mm*_shuffle_epi32`: doubleword `j` of each 128-bit lane is doubleword `imm8[2j + 1 : 2j]` of the
/// same lane of `a`.
pub open spec fn shuffle_epi32_lane(a: Seq<u64>, imm8: u8, i: int) -> u64 {
    let l = 4 * (i / 2);
    dword(a, l + imm2(imm8, 2 * (i % 2))) | (dword(a, l + imm2(imm8, 2 * (i % 2) + 1)) << 32u64)
}

/// Word `i` of `_mm256_blend_epi32`: doubleword `k` is that of `b` if bit `k` of the immediate is set, else that
/// of `a`.
pub open spec fn blend_epi32_lane(a: Seq<u64>, b: Seq<u64>, imm8: u8, i: int) -> u64 {
    let lo = if (imm8 >> ((2 * i) as u8)) & 1 == 1 {
        b[i]
    } else {
        a[i]
    };
    let hi = if (imm8 >> ((2 * i + 1) as u8)) & 1 == 1 {
        b[i]
    } else {
        a[i]
    };
    (lo & 0xFFFF_FFFFu64) | (hi & 0xFFFF_FFFF_0000_0000u64)
}

/// Word `i` of `_mm256_permute2x128_si256`: 128-bit half `h` is zero if bit `4h + 3` of the immediate is set,
/// else half `imm8[4h + 1 : 4h]` of the concatenation `a`, `b`.
pub open spec fn permute2x128_lane(a: Seq<u64>, b: Seq<u64>, imm8: u8, i: int) -> u64 {
    let ctl = (imm8 >> ((4 * (i / 2)) as u8)) & 15;
    let s = (ctl & 3) as int;
    if ctl & 8 != 0 {
        0
    } else if s < 2 {
        a[2 * s + i % 2]
    } else {
        b[2 * (s - 2) + i % 2]
    }
}

/// Word `i` of `_mm256_permutevar_pd`: word `bit 1 of b[i]` of the 128-bit lane of `a` that word `i` is in.
pub open spec fn permutevar_pd_lane(a: Seq<u64>, b: Seq<u64>, i: int) -> u64 {
    a[2 * (i / 2) + ((b[i] >> 1u64) & 1) as int]
}

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
pub assume_specification[ _mm_setzero_si128 ]() -> (r: __m128i)
    ensures
        m128(r)[0] == 0,
        m128(r)[1] == 0,
;

pub assume_specification[ _mm_set1_epi64x ](a: i64) -> (r: __m128i)
    ensures
        m128(r)[0] == a as u64,
        m128(r)[1] == a as u64,
;

pub assume_specification<const IMM8: i32>[ _mm_slli_epi64::<IMM8> ](a: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == super::x86::shl_imm(m128(a)[i], IMM8 as int),
;

pub assume_specification<const IMM8: i32>[ _mm_srli_epi64::<IMM8> ](a: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == super::x86::shr_imm(m128(a)[i], IMM8 as int),
;

pub assume_specification<const IMM8: i32>[ _mm_shuffle_epi32::<IMM8> ](a: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == shuffle_epi32_lane(m128(a)@, IMM8 as u8, i),
;

pub assume_specification<const MASK: i32>[ _mm256_shuffle_epi32::<MASK> ](a: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == shuffle_epi32_lane(m256(a)@, MASK as u8, i),
;

pub assume_specification<const MASK: i32>[ _mm512_shuffle_epi32::<MASK> ](a: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == shuffle_epi32_lane(m512(a)@, MASK as u8, i),
;

pub assume_specification<const IMM8: i32>[ _mm256_blend_epi32::<IMM8> ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == blend_epi32_lane(m256(a)@, m256(b)@, IMM8 as u8, i),
;

pub assume_specification<const IMM8: i32>[ _mm256_permute2x128_si256::<IMM8> ](a: __m256i, b: __m256i) -> (r:
    __m256i)
    ensures
        forall|i: int|
            0 <= i < 4 ==> #[trigger] m256(r)[i] == permute2x128_lane(m256(a)@, m256(b)@, IMM8 as u8, i),
;

pub assume_specification[ _mm256_permutevar_pd ](a: __m256d, b: __m256i) -> (r: __m256d)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256d(r)[i] == permutevar_pd_lane(m256d(a)@, m256(b)@, i),
;

pub assume_specification[ _mm256_castpd_si256 ](a: __m256d) -> (r: __m256i)
    ensures
        m256(r) == m256d(a),
;

pub assume_specification[ _mm256_castsi256_si128 ](a: __m256i) -> (r: __m128i)
    ensures
        m128(r)[0] == m256(a)[0],
        m128(r)[1] == m256(a)[1],
;

pub assume_specification<const IMM1: i32>[ _mm256_extracti128_si256::<IMM1> ](a: __m256i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == m256(a)[2 * (IMM1 as u8 & 1) as int + i],
;

pub assume_specification[ _mm512_setzero_si512 ]() -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == 0,
;

pub assume_specification[ _mm512_broadcast_i32x4 ](a: __m128i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == m128(a)[i % 2],
;

pub assume_specification[ _mm512_castsi512_si256 ](a: __m512i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m512(a)[i],
;

/// The upper four words are undefined: nothing is said of them.
pub assume_specification[ _mm512_castsi256_si512 ](a: __m256i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m512(r)[i] == m256(a)[i],
;

pub assume_specification<const IMM1: i32>[ _mm512_extracti64x4_epi64::<IMM1> ](a: __m512i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m512(a)[4 * (IMM1 as u8 & 1) as int + i],
;

// ---------------------------------------------------------------------------------------------
// Executable twins of the lane semantics, for the differential tests
// ---------------------------------------------------------------------------------------------
/// [`dword`].
pub fn model_dword(a: &[u64], k: usize) -> (r: u64)
    requires
        k < 2 * a.len(),
    ensures
        r == dword(a@, k as int),
{
    (a[k / 2] >> ((32 * (k % 2)) as u64)) & 0xFFFF_FFFF
}

/// [`imm2`].
pub fn model_imm2(imm8: u8, k: usize) -> (r: usize)
    requires
        k < 4,
    ensures
        r == imm2(imm8, k as int),
        r < 4,
{
    let s = (2 * k) as u8;
    assert((imm8 >> s) & 3 <= 3) by (bit_vector);
    ((imm8 >> s) & 3) as usize
}

/// [`shuffle_epi32_lane`].
pub fn model_shuffle_epi32_lane(a: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() % 2 == 0,
        a.len() <= 8,
        i < a.len(),
    ensures
        r == shuffle_epi32_lane(a@, imm8, i as int),
{
    let l = 4 * (i / 2);
    model_dword(a, l + model_imm2(imm8, 2 * (i % 2))) | (model_dword(a, l + model_imm2(imm8, 2 * (i % 2) + 1)) << 32u64)
}

/// [`blend_epi32_lane`].
pub fn model_blend_epi32_lane(a: &[u64], b: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() == 4,
        b.len() == 4,
        i < 4,
    ensures
        r == blend_epi32_lane(a@, b@, imm8, i as int),
{
    let lo = if (imm8 >> ((2 * i) as u8)) & 1 == 1 {
        b[i]
    } else {
        a[i]
    };
    let hi = if (imm8 >> ((2 * i + 1) as u8)) & 1 == 1 {
        b[i]
    } else {
        a[i]
    };
    (lo & 0xFFFF_FFFF) | (hi & 0xFFFF_FFFF_0000_0000)
}

/// [`permute2x128_lane`].
pub fn model_permute2x128_lane(a: &[u64], b: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() == 4,
        b.len() == 4,
        i < 4,
    ensures
        r == permute2x128_lane(a@, b@, imm8, i as int),
{
    let ctl = (imm8 >> ((4 * (i / 2)) as u8)) & 15;
    assert(ctl & 3 <= 3) by (bit_vector);
    let s = (ctl & 3) as usize;
    if ctl & 8 != 0 {
        0
    } else if s < 2 {
        a[2 * s + i % 2]
    } else {
        b[2 * (s - 2) + i % 2]
    }
}

/// [`permutevar_pd_lane`].
pub fn model_permutevar_pd_lane(a: &[u64], b: &[u64], i: usize) -> (r: u64)
    requires
        a.len() == 4,
        b.len() == 4,
        i < 4,
    ensures
        r == permutevar_pd_lane(a@, b@, i as int),
{
    let x = b[i];
    assert((x >> 1u64) & 1 <= 1) by (bit_vector);
    a[2 * (i / 2) + ((x >> 1u64) & 1) as usize]
}

} // verus!
