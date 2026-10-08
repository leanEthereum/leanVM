//! Specifications of the AVX2 byte intrinsics `gf2_8::avx2::gf8_mul_vec32` calls, beyond the ones in [`super::x86`].
//!
//! Same conventions: a register is viewed as its bytes ([`m256_bytes`]) or its words ([`m256`]); the signed
//! byte compare is given by [`cmpgt_epi8_lane`], with an executable twin that `tests/equivalence/
//! intrinsics_x86_gfneon.rs` runs against the hardware.
#[cfg(verus_keep_ghost)]
use super::x86::{axiom_m256_bytes, m256, m256_bytes};
use core::arch::x86_64::*;
use vstd::prelude::*;

verus! {

/// Byte `k` of `_mm256_cmpgt_epi8`: all ones where `a > b` as signed bytes, else zero.
pub open spec fn cmpgt_epi8_lane(a: u8, b: u8) -> u8 {
    if (a as i8) > (b as i8) {
        0xFF
    } else {
        0
    }
}

pub assume_specification[ _mm256_setzero_si256 ]() -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == 0,
;

pub assume_specification[ _mm256_set1_epi8 ](a: i8) -> (r: __m256i)
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == a as u8,
;

/// Byte-wise wrapping addition.
pub assume_specification[ _mm256_add_epi8 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == (m256_bytes(a)[k] + m256_bytes(b)[k]) as u8,
;

/// Byte-wise signed compare.
pub assume_specification[ _mm256_cmpgt_epi8 ](a: __m256i, b: __m256i) -> (r: __m256i)
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == cmpgt_epi8_lane(m256_bytes(a)[k], m256_bytes(b)[k]),
;

/// [`cmpgt_epi8_lane`].
pub fn model_cmpgt_epi8_lane(a: u8, b: u8) -> (r: u8)
    ensures
        r == cmpgt_epi8_lane(a, b),
{
    if (a as i8) > (b as i8) {
        0xFF
    } else {
        0
    }
}

// ---------------------------------------------------------------------------------------------
// The word-wise operations, read bytewise
// ---------------------------------------------------------------------------------------------
/// The bytes of a word-wise AND are the ANDs of the bytes.
pub proof fn lemma_m256_and_bytes(a: __m256i, b: __m256i, r: __m256i)
    requires
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m256(a)[i] & m256(b)[i],
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == m256_bytes(a)[k] & m256_bytes(b)[k],
{
    broadcast use axiom_m256_bytes;
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(r)[k] == m256_bytes(a)[k] & m256_bytes(b)[k] by {
        let (x, y) = (m256(a)[k / 8], m256(b)[k / 8]);
        let s = (8 * (k % 8)) as u64;
        assert(m256(r)[k / 8] == x & y);
        assert(s < 64 ==> ((x & y) >> s) as u8 == ((x >> s) as u8) & ((y >> s) as u8)) by (bit_vector);
    }
}

/// The bytes of a word-wise XOR are the XORs of the bytes.
pub proof fn lemma_m256_xor_bytes(a: __m256i, b: __m256i, r: __m256i)
    requires
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m256(a)[i] ^ m256(b)[i],
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == m256_bytes(a)[k] ^ m256_bytes(b)[k],
{
    broadcast use axiom_m256_bytes;
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(r)[k] == m256_bytes(a)[k] ^ m256_bytes(b)[k] by {
        let (x, y) = (m256(a)[k / 8], m256(b)[k / 8]);
        let s = (8 * (k % 8)) as u64;
        assert(m256(r)[k / 8] == x ^ y);
        assert(s < 64 ==> ((x ^ y) >> s) as u8 == ((x >> s) as u8) ^ ((y >> s) as u8)) by (bit_vector);
    }
}

/// The bytes of the zero register are zero.
pub proof fn lemma_m256_zero_bytes(r: __m256i)
    requires
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == 0,
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] m256_bytes(r)[k] == 0,
{
    broadcast use axiom_m256_bytes;
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(r)[k] == 0 by {
        let s = (8 * (k % 8)) as u64;
        assert(m256(r)[k / 8] == 0);
        assert((0u64 >> s) as u8 == 0) by (bit_vector);
    }
}

/// A signed compare of zero against a byte is its top bit, spread over the byte.
pub proof fn lemma_cmpgt_zero(x: u8)
    ensures
        cmpgt_epi8_lane(0, x) == if x >= 128 {
            0xFFu8
        } else {
            0u8
        },
{
    assert((0u8 as i8) > (x as i8) <==> x >= 128) by (bit_vector);
}

} // verus!
