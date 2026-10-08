//! Specifications of the x86-64 intrinsics (SSE2, PCLMULQDQ, BMI2, AVX2, VPCLMULQDQ, AVX-512F).
//!
//! A register is viewed as its 64-bit words, word 0 the least significant ([`m128`], [`m256`], [`m512`]).
//! Each intrinsic's result is given lane by lane by an open spec function `<intrinsic>_lane` over those
//! words, and each has an executable twin `model_<intrinsic>` proven to compute the same lanes, which the
//! differential tests run against the hardware.
#[cfg(verus_keep_ghost)]
use super::transmuted;
#[cfg(verus_keep_ghost)]
use crate::clmul::{bit, clmul};
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM128i(__m128i);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM256i(__m256i);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM512i(__m512i);

// ---------------------------------------------------------------------------------------------
// Views and layout
// ---------------------------------------------------------------------------------------------
/// The two 64-bit words of a 128-bit register, the low one first.
pub open spec fn m128(v: __m128i) -> [u64; 2] {
    transmuted::<__m128i, [u64; 2]>(v)
}

/// The four 64-bit words of a 256-bit register, the low one first.
pub open spec fn m256(v: __m256i) -> [u64; 4] {
    transmuted::<__m256i, [u64; 4]>(v)
}

/// The eight 64-bit words of a 512-bit register, the low one first.
pub open spec fn m512(v: __m512i) -> [u64; 8] {
    transmuted::<__m512i, [u64; 8]>(v)
}

/// The two words of a 128-bit register as one little-endian `u128`.
pub open spec fn m128_u128(v: __m128i) -> u128 {
    (m128(v)[0] as u128) | ((m128(v)[1] as u128) << 64u128)
}

/// The 16 bytes of a 128-bit register, the low one first.
pub open spec fn m128_bytes(v: __m128i) -> [u8; 16] {
    transmuted::<__m128i, [u8; 16]>(v)
}

/// The 32 bytes of a 256-bit register, the low one first.
pub open spec fn m256_bytes(v: __m256i) -> [u8; 32] {
    transmuted::<__m256i, [u8; 32]>(v)
}

/// The 64 bytes of a 512-bit register, the low one first.
pub open spec fn m512_bytes(v: __m512i) -> [u8; 64] {
    transmuted::<__m512i, [u8; 64]>(v)
}

/// Byte `k` of a sequence of words, little-endian.
pub open spec fn word_byte(w: Seq<u64>, k: int) -> u8 {
    (w[k / 8] >> ((8 * (k % 8)) as u64)) as u8
}

/// Layout: the bytes of a 128-bit register are its words, little-endian.
pub broadcast axiom fn axiom_m128_bytes(v: __m128i, k: int)
    requires
        0 <= k < 16,
    ensures
        #[trigger] m128_bytes(v)[k] == word_byte(m128(v)@, k),
;

/// Layout: the bytes of a 256-bit register are its words, little-endian.
pub broadcast axiom fn axiom_m256_bytes(v: __m256i, k: int)
    requires
        0 <= k < 32,
    ensures
        #[trigger] m256_bytes(v)[k] == word_byte(m256(v)@, k),
;

/// Layout: the bytes of a 512-bit register are its words, little-endian.
pub broadcast axiom fn axiom_m512_bytes(v: __m512i, k: int)
    requires
        0 <= k < 64,
    ensures
        #[trigger] m512_bytes(v)[k] == word_byte(m512(v)@, k),
;

/// Layout: a 128-bit register read as a `u128` is its two words, little-endian.
pub broadcast axiom fn axiom_m128_as_u128(v: __m128i)
    ensures
        #[trigger] transmuted::<__m128i, u128>(v) == m128_u128(v),
;

/// Layout: a 256-bit register read as `[[u64; 2]; 2]` is its words in order.
pub axiom fn axiom_m256_as_pairs(v: __m256i)
    ensures
        forall|i: int, j: int|
            0 <= i < 2 && 0 <= j < 2 ==> #[trigger] transmuted::<__m256i, [[u64; 2]; 2]>(v)[i][j] == m256(v)[2 * i
                + j],
;

/// Layout: a 512-bit register read as `[[u64; 2]; 4]` is its words in order.
pub axiom fn axiom_m512_as_pairs(v: __m512i)
    ensures
        forall|i: int, j: int|
            0 <= i < 4 && 0 <= j < 2 ==> #[trigger] transmuted::<__m512i, [[u64; 2]; 4]>(v)[i][j] == m512(v)[2 * i
                + j],
;

/// Layout: `[u64; 8]` read as a 512-bit register has those words.
pub axiom fn axiom_m512_from_words(w: [u64; 8])
    ensures
        m512(transmuted::<[u64; 8], __m512i>(w)) == w,
;

// ---------------------------------------------------------------------------------------------
// Lane semantics, shared by the specifications and their executable twins
// ---------------------------------------------------------------------------------------------
/// The carry-less product of word `ia` of `a` and word `ib` of `b`, as two words (PCLMULQDQ on one lane).
pub open spec fn clmul_words(a: u64, b: u64) -> [u64; 2] {
    let p = clmul(a, b as u128);
    [p as u64, (p >> 64u128) as u64]
}

/// Which word of a 128-bit lane PCLMULQDQ takes from its first operand: bit 0 of the immediate.
pub open spec fn clmul_sel_a(imm8: u8) -> int {
    (imm8 & 1) as int
}

/// Which word of a 128-bit lane PCLMULQDQ takes from its second operand: bit 4 of the immediate.
pub open spec fn clmul_sel_b(imm8: u8) -> int {
    ((imm8 >> 4u8) & 1) as int
}

/// The word selections of the four PCLMULQDQ immediates.
pub proof fn lemma_clmul_sel()
    ensures
        clmul_sel_a(0x00i32 as u8) == 0 && clmul_sel_b(0x00i32 as u8) == 0,
        clmul_sel_a(0x01i32 as u8) == 1 && clmul_sel_b(0x01i32 as u8) == 0,
        clmul_sel_a(0x10i32 as u8) == 0 && clmul_sel_b(0x10i32 as u8) == 1,
        clmul_sel_a(0x11i32 as u8) == 1 && clmul_sel_b(0x11i32 as u8) == 1,
{
    assert((0x00u8 & 1) == 0 && ((0x00u8 >> 4u8) & 1) == 0) by (bit_vector);
    assert((0x01u8 & 1) == 1 && ((0x01u8 >> 4u8) & 1) == 0) by (bit_vector);
    assert((0x10u8 & 1) == 0 && ((0x10u8 >> 4u8) & 1) == 1) by (bit_vector);
    assert((0x11u8 & 1) == 1 && ((0x11u8 >> 4u8) & 1) == 1) by (bit_vector);
}

/// Word `i` of a carry-less multiply of each 128-bit lane (`_mm*_clmulepi64_*`).
pub open spec fn clmul_lane(a: Seq<u64>, b: Seq<u64>, imm8: u8, i: int) -> u64 {
    let l = 2 * (i / 2);
    clmul_words(a[l + clmul_sel_a(imm8)], b[l + clmul_sel_b(imm8)])[i % 2]
}

/// Word `i` of `unpacklo_epi64`: the low words of each 128-bit lane of `a` and `b`, interleaved.
pub open spec fn unpacklo_lane(a: Seq<u64>, b: Seq<u64>, i: int) -> u64 {
    if i % 2 == 0 {
        a[i]
    } else {
        b[i - 1]
    }
}

/// Word `i` of `unpackhi_epi64`: the high words of each 128-bit lane of `a` and `b`, interleaved.
pub open spec fn unpackhi_lane(a: Seq<u64>, b: Seq<u64>, i: int) -> u64 {
    if i % 2 == 0 {
        a[i + 1]
    } else {
        b[i]
    }
}

/// A logical left shift of a word by an immediate: zero from 64 on.
pub open spec fn shl_imm(a: u64, imm8: int) -> u64 {
    if 0 <= imm8 < 64 {
        a << (imm8 as u64)
    } else {
        0
    }
}

/// A logical right shift of a word by an immediate: zero from 64 on.
pub open spec fn shr_imm(a: u64, imm8: int) -> u64 {
    if 0 <= imm8 < 64 {
        a >> (imm8 as u64)
    } else {
        0
    }
}

/// Word `i` of `_mm256_permute4x64_epi64`: word `imm8[2i + 1 : 2i]` of `a`.
pub open spec fn permute4x64_lane(a: Seq<u64>, imm8: u8, i: int) -> u64 {
    a[((imm8 >> ((2 * i) as u8)) & 3) as int]
}

/// Word `i` of `_mm512_shuffle_i64x2`: 128-bit lanes 0 and 1 from `a`, 2 and 3 from `b`, each picked by two
/// bits of the immediate.
pub open spec fn shuffle_i64x2_lane(a: Seq<u64>, b: Seq<u64>, imm8: u8, i: int) -> u64 {
    let q = i / 2;
    let src = ((imm8 >> ((2 * q) as u8)) & 3) as int;
    if q < 2 {
        a[2 * src + i % 2]
    } else {
        b[2 * src + i % 2]
    }
}

/// Word `i` of `_mm512_permutex2var_epi64`: word `idx[i] & 7` of `a`, or of `b` if bit 3 of `idx[i]` is set.
pub open spec fn permutex2var_lane(a: Seq<u64>, idx: Seq<u64>, b: Seq<u64>, i: int) -> u64 {
    let k = (idx[i] & 7) as int;
    if idx[i] & 8 == 0 {
        a[k]
    } else {
        b[k]
    }
}

/// Byte `k` of `_mm*_shuffle_epi8(a, b)`: zero if bit 7 of `b[k]` is set, else byte `b[k] & 15` of the 16-byte
/// lane of `a` that byte `k` is in.
pub open spec fn shuffle_epi8_lane(a: Seq<u8>, b: Seq<u8>, k: int) -> u8 {
    if b[k] & 0x80 != 0 {
        0
    } else {
        a[16 * (k / 16) + (b[k] & 15) as int]
    }
}

/// All ones if bit `k` of the immediate is set, else zero.
pub open spec fn imm_mask(imm8: u8, k: u8) -> u64 {
    if (imm8 >> k) & 1 == 1 {
        !0u64
    } else {
        0u64
    }
}

/// `vpternlogq` on one word: bit `j` of the result is bit `4 a_j + 2 b_j + c_j` of the immediate.
pub open spec fn ternlog(imm8: u8, a: u64, b: u64, c: u64) -> u64 {
    (imm_mask(imm8, 0) & !a & !b & !c) | (imm_mask(imm8, 1) & !a & !b & c) | (imm_mask(imm8, 2) & !a & b & !c) | (
    imm_mask(imm8, 3) & !a & b & c) | (imm_mask(imm8, 4) & a & !b & !c) | (imm_mask(imm8, 5) & a & !b & c) | (
    imm_mask(imm8, 6) & a & b & !c) | (imm_mask(imm8, 7) & a & b & c)
}

/// Bit `j` of `_pdep_u64(a, mask)`: zero where `mask` is clear, else the next unused bit of `a`, counting
/// from bit 0: bit `popcount(mask & (2^j - 1))` of `a`.
pub open spec fn pdep_bit(a: u64, mask: u64, j: nat) -> bool {
    (mask >> (j as u64)) & 1 == 1 && (a >> (ones_below(mask, j) as u64)) & 1 == 1
}

/// The number of set bits of `mask` below bit `j`.
pub open spec fn ones_below(mask: u64, j: nat) -> nat
    decreases j,
{
    if j == 0 {
        0
    } else {
        ones_below(mask, (j - 1) as nat) + if (mask >> ((j - 1) as u64)) & 1 == 1 {
            1nat
        } else {
            0nat
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The specifications
// ---------------------------------------------------------------------------------------------
pub assume_specification[ _mm_cvtsi64_si128 ](a: i64) -> (r: __m128i)
    ensures
        m128(r)[0] == a as u64,
        m128(r)[1] == 0,
;

pub assume_specification[ _mm_cvtsi128_si64 ](a: __m128i) -> (r: i64)
    ensures
        r as u64 == m128(a)[0],
;

pub assume_specification[ _mm_set_epi64x ](e1: i64, e0: i64) -> (r: __m128i)
    ensures
        m128(r)[0] == e0 as u64,
        m128(r)[1] == e1 as u64,
;

pub assume_specification[ _mm_xor_si128 ](a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == m128(a)[i] ^ m128(b)[i],
;

pub assume_specification[ _mm_unpacklo_epi64 ](a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == unpacklo_lane(m128(a)@, m128(b)@, i),
;

pub assume_specification[ _mm_unpackhi_epi64 ](a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == unpackhi_lane(m128(a)@, m128(b)@, i),
;

pub assume_specification<const IMM8: i32>[ _mm_clmulepi64_si128::<IMM8> ](a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == clmul_lane(m128(a)@, m128(b)@, IMM8 as u8, i),
;

pub assume_specification[ _pdep_u64 ](a: u64, mask: u64) -> (r: u64)
    ensures
        forall|j: nat| j < 64 ==> #[trigger] bit(r, j) == pdep_bit(a, mask, j),
;

pub assume_specification[ _mm256_xor_si256 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m256(a)[i] ^ m256(b)[i],
;

pub assume_specification[ _mm256_and_si256 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m256(a)[i] & m256(b)[i],
;

pub assume_specification[ _mm256_add_epi64 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == (m256(a)[i] + m256(b)[i]) as u64,
;

pub assume_specification<const IMM8: i32>[ _mm256_clmulepi64_epi128::<IMM8> ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == clmul_lane(m256(a)@, m256(b)@, IMM8 as u8, i),
;

pub assume_specification[ _mm256_unpacklo_epi64 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == unpacklo_lane(m256(a)@, m256(b)@, i),
;

pub assume_specification[ _mm256_unpackhi_epi64 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == unpackhi_lane(m256(a)@, m256(b)@, i),
;

pub assume_specification<const IMM8: i32>[ _mm256_slli_epi64::<IMM8> ](a: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == shl_imm(m256(a)[i], IMM8 as int),
;

pub assume_specification<const IMM8: i32>[ _mm256_srli_epi64::<IMM8> ](a: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == shr_imm(m256(a)[i], IMM8 as int),
;

pub assume_specification[ _mm256_set1_epi64x ](a: i64) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == a as u64,
;

pub assume_specification[ _mm256_set_epi64x ](e3: i64, e2: i64, e1: i64, e0: i64) -> (r: __m256i)
    ensures
        m256(r)[0] == e0 as u64,
        m256(r)[1] == e1 as u64,
        m256(r)[2] == e2 as u64,
        m256(r)[3] == e3 as u64,
;

pub assume_specification[ _mm256_shuffle_epi8 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == shuffle_epi8_lane(m256_bytes(a)@, m256_bytes(b)@, k),
;

pub assume_specification[ _mm256_broadcastsi128_si256 ](a: __m128i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m128(a)[i % 2],
;

pub assume_specification<const IMM8: i32>[ _mm256_permute4x64_epi64::<IMM8> ](a: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == permute4x64_lane(m256(a)@, IMM8 as u8, i),
;

pub assume_specification[ _mm512_xor_si512 ](a: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == m512(a)[i] ^ m512(b)[i],
;

pub assume_specification<const IMM8: i32>[ _mm512_clmulepi64_epi128::<IMM8> ](a: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == clmul_lane(m512(a)@, m512(b)@, IMM8 as u8, i),
;

pub assume_specification[ _mm512_unpacklo_epi64 ](a: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == unpacklo_lane(m512(a)@, m512(b)@, i),
;

pub assume_specification[ _mm512_unpackhi_epi64 ](a: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == unpackhi_lane(m512(a)@, m512(b)@, i),
;

pub assume_specification<const IMM8: u32>[ _mm512_slli_epi64::<IMM8> ](a: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == shl_imm(m512(a)[i], IMM8 as int),
;

pub assume_specification<const IMM8: u32>[ _mm512_srli_epi64::<IMM8> ](a: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == shr_imm(m512(a)[i], IMM8 as int),
;

pub assume_specification[ _mm512_set1_epi64 ](a: i64) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == a as u64,
;

pub assume_specification[ _mm512_set_epi64 ](
    e7: i64,
    e6: i64,
    e5: i64,
    e4: i64,
    e3: i64,
    e2: i64,
    e1: i64,
    e0: i64,
) -> (r: __m512i)
    ensures
        m512(r)[0] == e0 as u64,
        m512(r)[1] == e1 as u64,
        m512(r)[2] == e2 as u64,
        m512(r)[3] == e3 as u64,
        m512(r)[4] == e4 as u64,
        m512(r)[5] == e5 as u64,
        m512(r)[6] == e6 as u64,
        m512(r)[7] == e7 as u64,
;

pub assume_specification<const IMM8: i32>[ _mm512_shuffle_i64x2::<IMM8> ](a: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == shuffle_i64x2_lane(m512(a)@, m512(b)@, IMM8 as u8, i),
;

pub assume_specification[ _mm512_permutex2var_epi64 ](a: __m512i, idx: __m512i, b: __m512i) -> (r: __m512i)
    ensures
        forall|i: int|
            0 <= i < 8 ==> #[trigger] m512(r)[i] == permutex2var_lane(m512(a)@, m512(idx)@, m512(b)@, i),
;

pub assume_specification<const IMM8: i32>[ _mm512_ternarylogic_epi64::<IMM8> ](
    a: __m512i,
    b: __m512i,
    c: __m512i,
) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == ternlog(IMM8 as u8, m512(a)[i], m512(b)[i], m512(c)[i]),
;

// ---------------------------------------------------------------------------------------------
// Executable twins of the lane semantics, for the differential tests
// ---------------------------------------------------------------------------------------------
/// [`clmul_words`].
pub fn model_clmul_words(a: u64, b: u64) -> (r: [u64; 2])
    ensures
        r == clmul_words(a, b),
{
    let p = crate::gf2_64::software::clmul(a, b);
    let r = [p as u64, (p >> 64u128) as u64];
    assert(r =~= clmul_words(a, b));
    r
}

/// [`clmul_lane`].
pub fn model_clmul_lane(a: &[u64], b: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() == b.len(),
        a.len() % 2 == 0,
        i < a.len(),
    ensures
        r == clmul_lane(a@, b@, imm8, i as int),
{
    let l = 2 * (i / 2);
    let (sa, sb) = ((imm8 & 1) as usize, ((imm8 >> 4u8) & 1) as usize);
    assert((imm8 & 1) <= 1 && ((imm8 >> 4u8) & 1) <= 1) by (bit_vector);
    model_clmul_words(a[l + sa], b[l + sb])[i % 2]
}

/// [`unpacklo_lane`].
pub fn model_unpacklo_lane(a: &[u64], b: &[u64], i: usize) -> (r: u64)
    requires
        a.len() == b.len(),
        a.len() % 2 == 0,
        i < a.len(),
    ensures
        r == unpacklo_lane(a@, b@, i as int),
{
    if i % 2 == 0 {
        a[i]
    } else {
        b[i - 1]
    }
}

/// [`unpackhi_lane`].
pub fn model_unpackhi_lane(a: &[u64], b: &[u64], i: usize) -> (r: u64)
    requires
        a.len() == b.len(),
        a.len() % 2 == 0,
        i < a.len(),
    ensures
        r == unpackhi_lane(a@, b@, i as int),
{
    if i % 2 == 0 {
        a[i + 1]
    } else {
        b[i]
    }
}

/// [`shl_imm`].
pub fn model_shl_imm(a: u64, imm8: u32) -> (r: u64)
    ensures
        r == shl_imm(a, imm8 as int),
{
    if imm8 < 64 {
        a << imm8
    } else {
        0
    }
}

/// [`shr_imm`].
pub fn model_shr_imm(a: u64, imm8: u32) -> (r: u64)
    ensures
        r == shr_imm(a, imm8 as int),
{
    if imm8 < 64 {
        a >> imm8
    } else {
        0
    }
}

/// [`permute4x64_lane`].
pub fn model_permute4x64_lane(a: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() == 4,
        i < 4,
    ensures
        r == permute4x64_lane(a@, imm8, i as int),
{
    let s = (2 * i) as u8;
    assert((imm8 >> s) & 3 <= 3) by (bit_vector);
    a[((imm8 >> s) & 3) as usize]
}

/// [`shuffle_i64x2_lane`].
pub fn model_shuffle_i64x2_lane(a: &[u64], b: &[u64], imm8: u8, i: usize) -> (r: u64)
    requires
        a.len() == 8,
        b.len() == 8,
        i < 8,
    ensures
        r == shuffle_i64x2_lane(a@, b@, imm8, i as int),
{
    let q = i / 2;
    let s = (2 * q) as u8;
    assert((imm8 >> s) & 3 <= 3) by (bit_vector);
    let src = ((imm8 >> s) & 3) as usize;
    if q < 2 {
        a[2 * src + i % 2]
    } else {
        b[2 * src + i % 2]
    }
}

/// [`permutex2var_lane`].
pub fn model_permutex2var_lane(a: &[u64], idx: &[u64], b: &[u64], i: usize) -> (r: u64)
    requires
        a.len() == 8,
        idx.len() == 8,
        b.len() == 8,
        i < 8,
    ensures
        r == permutex2var_lane(a@, idx@, b@, i as int),
{
    let x = idx[i];
    assert(x & 7 <= 7) by (bit_vector);
    let k = (x & 7) as usize;
    if x & 8 == 0 {
        a[k]
    } else {
        b[k]
    }
}

/// [`shuffle_epi8_lane`].
pub fn model_shuffle_epi8_lane(a: &[u8], b: &[u8], k: usize) -> (r: u8)
    requires
        a.len() == b.len(),
        a.len() % 16 == 0,
        k < a.len(),
    ensures
        r == shuffle_epi8_lane(a@, b@, k as int),
{
    if b[k] & 0x80 != 0 {
        0
    } else {
        let x = b[k];
        assert(x & 15 < 16) by (bit_vector);
        a[16 * (k / 16) + (x & 15) as usize]
    }
}

/// [`imm_mask`].
pub fn model_imm_mask(imm8: u8, k: u8) -> (r: u64)
    requires
        0 <= k < 8,
    ensures
        r == imm_mask(imm8, k),
{
    if (imm8 >> k) & 1 == 1 {
        !0u64
    } else {
        0u64
    }
}

/// [`ternlog`].
pub fn model_ternlog(imm8: u8, a: u64, b: u64, c: u64) -> (r: u64)
    ensures
        r == ternlog(imm8, a, b, c),
{
    let m = [
        model_imm_mask(imm8, 0),
        model_imm_mask(imm8, 1),
        model_imm_mask(imm8, 2),
        model_imm_mask(imm8, 3),
        model_imm_mask(imm8, 4),
        model_imm_mask(imm8, 5),
        model_imm_mask(imm8, 6),
        model_imm_mask(imm8, 7),
    ];
    (m[0] & !a & !b & !c) | (m[1] & !a & !b & c) | (m[2] & !a & b & !c) | (m[3] & !a & b & c) | (m[4] & a & !b & !c)
        | (m[5] & a & !b & c) | (m[6] & a & b & !c) | (m[7] & a & b & c)
}

/// [`pdep_bit`], for all 64 bits: the deposit computed bit by bit.
pub fn model_pdep(a: u64, mask: u64) -> (r: u64)
    ensures
        forall|j: nat| j < 64 ==> #[trigger] bit(r, j) == pdep_bit(a, mask, j),
{
    let mut r = 0u64;
    let mut k = 0u64;
    let mut j = 0u64;
    assert forall|t: nat| t < 64 implies !#[trigger] bit(0u64, t) by {
        let tt = t as u64;
        assert((0u64 >> tt) & 1 == 0) by (bit_vector);
    }
    while j < 64
        invariant
            j <= 64,
            k == ones_below(mask, j as nat),
            k <= j,
            forall|t: nat| t < j ==> #[trigger] bit(r, t) == pdep_bit(a, mask, t),
            forall|t: nat| j <= t < 64 ==> !#[trigger] bit(r, t),
        decreases 64 - j,
    {
        let m = (mask >> j) & 1 == 1;
        let set = m && (a >> k) & 1 == 1;
        let ghost r0 = r;
        if set {
            r = r | (1u64 << j);
        }
        proof {
            assert forall|t: nat| t < 64 implies #[trigger] bit(r, t) == if t == j as nat {
                set || bit(r0, t)
            } else {
                bit(r0, t)
            } by {
                let tt = t as u64;
                if set {
                    assert(tt < 64 ==> (((r0 | (1u64 << j)) >> tt) & 1 == 1) == (tt == j || (r0 >> tt) & 1 == 1))
                        by (bit_vector);
                }
            }
            assert(ones_below(mask, (j + 1) as nat) == ones_below(mask, j as nat) + if m {
                1nat
            } else {
                0nat
            });
        }
        if m {
            k = k + 1;
        }
        j = j + 1;
    }
    r
}

} // verus!
