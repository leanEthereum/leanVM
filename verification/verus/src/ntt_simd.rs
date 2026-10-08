//! The SIMD butterfly kernels of the additive NTT, `crates/pcs/src/ntt/additive_ntt_f64.rs`
//! (`butterfly_lanes_avx512`, `butterfly_lanes_avx2`, `butterfly_lanes_neon_8`, `butterfly_lane_pair_neon`),
//! copied with production's bodies and `cfg` gates; `ntt::lane_butterflies` dispatches to them as production
//! does.
//!
//! Each kernel is proven to leave its words of the two rows as the portable path leaves them: word `j` of
//! `top`/`bot` through [`butterfly_spec`] with the twiddle (forward `u' = u + t v, v' = v + u'`, transposed
//! `u' = u + v, v' = v + t u'`, products by `k_mul`), and every other word unchanged ([`butterflied`]). This rests
//! on the intrinsic specifications of `crate::intrinsics`.
//!
//! One rewrite is common to all kernels: production takes `top: *mut F64, bot: *mut F64` and loads and stores
//! through them. Verus cannot tie a pointer to the memory it addresses unless the caller holds a permission for
//! it, and `lane_butterflies` holds `&mut [F64]` borrows, from which no permission can be obtained. So each copy
//! takes the two rows and the offset `at` its pointers point to (`top.as_mut_ptr().add(at)` in production), and
//! loads and stores through the helpers of `intrinsics::x86_nttsimd` / `intrinsics::aarch64_nttsimd`, whose
//! bodies are production's load or store at that offset.
#[cfg(verus_keep_ghost)]
use crate::clmul::clmul;
use crate::gf2_64::F64;
#[cfg(verus_keep_ghost)]
use crate::gf2_64::{k_mod, k_mul, lemma_k_mod, reduce_formula};
#[cfg(verus_keep_ghost)]
use crate::ntt::butterfly_spec;
use vstd::prelude::*;

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
use crate::gf2_64::aarch64::reduce_pair_pmull4;
#[cfg(all(target_arch = "aarch64", verus_keep_ghost))]
use crate::gf2_64::aarch64::u64x2_u128;
#[cfg(all(target_arch = "x86_64", verus_keep_ghost))]
use crate::gf2_64::x86_64::lemma_i64_round_trip;
#[cfg(all(target_arch = "aarch64", verus_keep_ghost))]
use crate::intrinsics::aarch64::*;
#[cfg(target_arch = "aarch64")]
use crate::intrinsics::aarch64_nttsimd::*;
#[cfg(verus_keep_ghost)]
use crate::intrinsics::transmuted;
#[cfg(all(target_arch = "x86_64", verus_keep_ghost))]
use crate::intrinsics::x86::*;
#[cfg(target_arch = "x86_64")]
use crate::intrinsics::x86_nttsimd::*;
#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// Words `lo .. hi` of the rows `(top, bot)`, within both, are those of `(top0, bot0)` through the butterfly with
/// twiddle `t`, and every other word is unchanged.
pub open spec fn butterflied(
    transposed: bool,
    top0: Seq<F64>,
    bot0: Seq<F64>,
    top: Seq<F64>,
    bot: Seq<F64>,
    lo: int,
    hi: int,
    t: u64,
) -> bool {
    &&& 0 <= lo <= hi
    &&& hi <= top0.len()
    &&& hi <= bot0.len()
    &&& top.len() == top0.len()
    &&& bot.len() == bot0.len()
    &&& forall|j: int|
        lo <= j < hi ==> ((#[trigger] top[j]).0, bot[j].0) == butterfly_spec(transposed, top0[j].0, bot0[j].0, t)
    &&& forall|j: int| 0 <= j < top0.len() && !(lo <= j < hi) ==> #[trigger] top[j] == top0[j]
    &&& forall|j: int| 0 <= j < bot0.len() && !(lo <= j < hi) ==> #[trigger] bot[j] == bot0[j]
}

/// Butterflies on consecutive ranges compose: `lo .. mid` then `mid .. hi` is `lo .. hi`.
pub proof fn lemma_butterflied_extend(
    transposed: bool,
    top0: Seq<F64>,
    bot0: Seq<F64>,
    top1: Seq<F64>,
    bot1: Seq<F64>,
    top2: Seq<F64>,
    bot2: Seq<F64>,
    lo: int,
    mid: int,
    hi: int,
    t: u64,
)
    requires
        lo <= mid <= hi,
        butterflied(transposed, top0, bot0, top1, bot1, lo, mid, t),
        butterflied(transposed, top1, bot1, top2, bot2, mid, hi, t),
    ensures
        butterflied(transposed, top0, bot0, top2, bot2, lo, hi, t),
{
    assert forall|j: int| lo <= j < hi implies ((#[trigger] top2[j]).0, bot2[j].0) == butterfly_spec(
        transposed,
        top0[j].0,
        bot0[j].0,
        t,
    ) by {
        if j < mid {
            assert(top2[j] == top1[j] && bot2[j] == bot1[j]);
        } else {
            assert(top1[j] == top0[j] && bot1[j] == bot0[j]);
        }
    }
    assert forall|j: int| 0 <= j < top0.len() && !(lo <= j < hi) implies #[trigger] top2[j] == top0[j] by {
        assert(top2[j] == top1[j]);
    }
    assert forall|j: int| 0 <= j < bot0.len() && !(lo <= j < hi) implies #[trigger] bot2[j] == bot0[j] by {
        assert(bot2[j] == bot1[j]);
    }
}

/// The shape every kernel computes a lane in: the row multiplied by the twiddle, `m`, and the row the product
/// is added to, `acc`, give `sum = acc + m t`; the new rows are `(m, sum)` transposed, `(sum, v + sum)` forward.
pub proof fn lemma_butterfly_lane(
    transposed: bool,
    u: u64,
    v: u64,
    t: u64,
    m: u64,
    acc: u64,
    sum: u64,
    nu: u64,
    nv: u64,
)
    requires
        m == if transposed {
            u ^ v
        } else {
            v
        },
        acc == if transposed {
            v
        } else {
            u
        },
        sum == acc ^ k_mul(m, t),
        nu == if transposed {
            m
        } else {
            sum
        },
        nv == if transposed {
            sum
        } else {
            v ^ sum
        },
    ensures
        (nu, nv) == butterfly_spec(transposed, u, v, t),
{
}

/// The shift-and-XOR reduction of the x86 kernels: with `lo`, `hi` the words of `p`, the spill
/// `hi>>63 ^ hi>>61 ^ hi>>60`, `x = hi ^ spill` and `g(x) = x ^ x<<1 ^ x<<3 ^ x<<4`, `lo ^ g(x)` is `k_mod(p)`.
pub proof fn lemma_shift_reduction(p: u128, lo: u64, hi: u64, x: u64)
    requires
        lo == p as u64,
        hi == (p >> 64u128) as u64,
        x == hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64)),
    ensures
        lo ^ (x ^ (x << 1u64) ^ (x << 3u64) ^ (x << 4u64)) == k_mod(p),
{
    lemma_k_mod(p);
    assert(x == hi ^ (hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64)) by (bit_vector)
        requires
            x == hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64)),
    ;
    assert(lo ^ (x ^ (x << 1u64) ^ (x << 3u64) ^ (x << 4u64)) == lo ^ x ^ (x << 1u64) ^ (x << 3u64) ^ (x << 4u64))
        by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// x86-64: the products in lane order, and the three-way XOR
// ---------------------------------------------------------------------------------------------
/// The products of `_mm*_clmulepi64_epi128::<0x00>` and `::<0x11>` of `m` and a broadcast twiddle, unpacked
/// low with high, are word `i`'s product: `lo[i]` and `hi[i]` are the low and high words of `m[i] * t`.
#[cfg(target_arch = "x86_64")]
pub proof fn lemma_products_in_lane_order(
    m: Seq<u64>,
    tw: Seq<u64>,
    even: Seq<u64>,
    odd: Seq<u64>,
    lo: Seq<u64>,
    hi: Seq<u64>,
    t: u64,
    i: int,
)
    requires
        0 <= i < m.len(),
        m.len() % 2 == 0,
        tw.len() == m.len(),
        forall|k: int| 0 <= k < m.len() ==> #[trigger] tw[k] == t,
        forall|k: int| 0 <= k < m.len() ==> #[trigger] even[k] == clmul_lane(m, tw, 0x00i32 as u8, k),
        forall|k: int| 0 <= k < m.len() ==> #[trigger] odd[k] == clmul_lane(m, tw, 0x11i32 as u8, k),
        forall|k: int| 0 <= k < m.len() ==> #[trigger] lo[k] == unpacklo_lane(even, odd, k),
        forall|k: int| 0 <= k < m.len() ==> #[trigger] hi[k] == unpackhi_lane(even, odd, k),
    ensures
        lo[i] == clmul(m[i], t as u128) as u64,
        hi[i] == (clmul(m[i], t as u128) >> 64u128) as u64,
{
    lemma_clmul_sel();
    if i % 2 == 0 {
        assert(lo[i] == even[i]);
        assert(hi[i] == even[i + 1]);
        assert(tw[i] == t);
    } else {
        assert(lo[i] == odd[i - 1]);
        assert(hi[i] == odd[i]);
        assert(tw[i] == t);
    }
}

/// `vpternlogq` with immediate `0x96` is the three-way XOR.
#[cfg(target_arch = "x86_64")]
pub proof fn lemma_ternlog_xor3(a: u64, b: u64, c: u64)
    ensures
        ternlog(0x96i32 as u8, a, b, c) == a ^ b ^ c,
{
    let m = 0x96u8;
    assert(0x96i32 as u8 == m);
    assert((m >> 0u8) & 1 != 1 && (m >> 1u8) & 1 == 1 && (m >> 2u8) & 1 == 1 && (m >> 3u8) & 1 != 1 && (m >> 4u8) & 1
        == 1 && (m >> 5u8) & 1 != 1 && (m >> 6u8) & 1 != 1 && (m >> 7u8) & 1 == 1) by (bit_vector)
        requires
            m == 0x96u8,
    ;
    assert(ternlog(m, a, b, c) == (0u64 & !a & !b & !c) | (!0u64 & !a & !b & c) | (!0u64 & !a & b & !c) | (0u64 & !a
        & b & c) | (!0u64 & a & !b & !c) | (0u64 & a & !b & c) | (0u64 & a & b & !c) | (!0u64 & a & b & c));
    assert((0u64 & !a & !b & !c) | (!0u64 & !a & !b & c) | (!0u64 & !a & b & !c) | (0u64 & !a & b & c) | (!0u64 & a
        & !b & !c) | (0u64 & a & !b & c) | (0u64 & a & b & !c) | (!0u64 & a & b & c) == a ^ b ^ c) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// AVX-512
// ---------------------------------------------------------------------------------------------
/// The `vpternlogq` immediate of the three-way XOR.
///
/// Moved out of `butterfly_lanes_avx512`, where production declares it: Verus takes no items inside a function.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
const XOR3: i32 = 0x96;

/// Eight F64 butterflies with a shared twiddle, one per 64-bit lane of an AVX-512 register.
///
/// Rewritten for Verus: the rows are `top[at..at + 8]` and `bot[at..at + 8]` instead of two pointers, loaded
/// and stored by [`loadu512_at`] and [`storeu512_at`] (see the module documentation); `XOR3` is a module
/// constant.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX-512F.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
pub unsafe fn butterfly_lanes_avx512<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], at: usize, twiddle: u64)
    requires
        at + 8 <= old(top).len(),
        at + 8 <= old(bot).len(),
    ensures
        butterflied(TRANSPOSED, old(top)@, old(bot)@, final(top)@, final(bot)@, at as int, at + 8, twiddle),
{
    // The lane lemmas unfold these; here they only need to match the intrinsics' postconditions.
    hide(clmul_lane);
    hide(clmul_words);
    hide(unpacklo_lane);
    hide(unpackhi_lane);
    hide(ternlog);
    hide(butterfly_spec);
    let ghost (top0, bot0) = (top@, bot@);
    // SAFETY:
    // - The caller supplies two valid eight-word rows.
    // - This function's target features cover every intrinsic below.
    unsafe {
        // Load both rows and broadcast the twiddle to every lane.
        let u = loadu512_at(top, at);
        let v = loadu512_at(bot, at);
        let tw = _mm512_set1_epi64(twiddle as i64);
        // The row multiplied by the twiddle, and the row the product is added to.
        let (m, acc) = if TRANSPOSED {
            (_mm512_xor_si512(u, v), v)
        } else {
            (v, u)
        };

        // Products m * t: even lanes, then odd lanes, one 128-bit product per 128-bit lane.
        let even = _mm512_clmulepi64_epi128::<0x00>(m, tw);
        let odd = _mm512_clmulepi64_epi128::<0x11>(m, tw);
        // Back to lane order: qword i of lo / hi is the low / high half of lane i's product.
        let lo = _mm512_unpacklo_epi64(even, odd);
        let hi = _mm512_unpackhi_epi64(even, odd);

        // Reduce modulo x^64 + x^4 + x^3 + x + 1 with shifts and three-way XORs.
        // The bits of hi * (x^4 + x^3 + x + 1) that land past x^63.
        let spill = _mm512_ternarylogic_epi64::<XOR3>(
            _mm512_srli_epi64::<63>(hi),
            _mm512_srli_epi64::<61>(hi),
            _mm512_srli_epi64::<60>(hi),
        );
        // Both hi and spill are multiplied by the same constant, so fold them first.
        let x = _mm512_xor_si512(hi, spill);
        // g(x) = x ^ x<<1 ^ x<<3 ^ x<<4, split across two three-way XORs.
        let fx = _mm512_ternarylogic_epi64::<XOR3>(x, _mm512_slli_epi64::<1>(x), _mm512_slli_epi64::<3>(x));
        // acc + m * t, with the product's lo and g(x) folded in one step.
        let sum = _mm512_ternarylogic_epi64::<XOR3>(acc, lo, _mm512_xor_si512(fx, _mm512_slli_epi64::<4>(x)));
        // Forward: u' = u + v * t, then v' = v + u'. Transposed: u' = u + v, then v' = v + u' * t.
        let (new_u, new_v) = if TRANSPOSED {
            (m, sum)
        } else {
            (sum, _mm512_xor_si512(v, sum))
        };
        proof {
            lemma_i64_round_trip(twiddle);
            // The products, in lane order.
            assert forall|i: int| 0 <= i < 8 implies #[trigger] m512(lo)[i] == clmul(m512(m)[i], twiddle as u128) as u64
                && m512(hi)[i] == (clmul(m512(m)[i], twiddle as u128) >> 64u128) as u64 by {
                lemma_products_in_lane_order(
                    m512(m)@,
                    m512(tw)@,
                    m512(even)@,
                    m512(odd)@,
                    m512(lo)@,
                    m512(hi)@,
                    twiddle,
                    i,
                );
            }
            // Their reduction: sum = acc + m t.
            assert forall|i: int| 0 <= i < 8 implies #[trigger] m512(sum)[i] == m512(acc)[i] ^ k_mul(m512(m)[i], twiddle) by {
                let p = clmul(m512(m)[i], twiddle as u128);
                let h = m512(hi)[i];
                lemma_ternlog_xor3(h >> 63u64, h >> 61u64, h >> 60u64);
                let xi = m512(x)[i];
                assert(xi == h ^ ((h >> 63u64) ^ (h >> 61u64) ^ (h >> 60u64)));
                lemma_ternlog_xor3(xi, xi << 1u64, xi << 3u64);
                let fi = m512(fx)[i];
                let ai = m512(acc)[i];
                let li = m512(lo)[i];
                lemma_ternlog_xor3(ai, li, fi ^ (xi << 4u64));
                lemma_shift_reduction(p, li, h, xi);
                assert(ai ^ li ^ (fi ^ (xi << 4u64)) == ai ^ (li ^ (xi ^ (xi << 1u64) ^ (xi << 3u64) ^ (xi << 4u64))))
                    by (bit_vector)
                    requires
                        fi == xi ^ (xi << 1u64) ^ (xi << 3u64),
                ;
            }
            // The new rows.
            assert forall|i: int| 0 <= i < 8 implies #[trigger] m512(new_u)[i] == butterfly_spec(
                TRANSPOSED,
                top0[at + i].0,
                bot0[at + i].0,
                twiddle,
            ).0 && m512(new_v)[i] == butterfly_spec(TRANSPOSED, top0[at + i].0, bot0[at + i].0, twiddle).1 by {
                lemma_butterfly_lane(
                    TRANSPOSED,
                    top0[at + i].0,
                    bot0[at + i].0,
                    twiddle,
                    m512(m)[i],
                    m512(acc)[i],
                    m512(sum)[i],
                    m512(new_u)[i],
                    m512(new_v)[i],
                );
            }
        }
        storeu512_at(top, at, new_u);
        storeu512_at(bot, at, new_v);
        proof {
            assert forall|j: int| at <= j < at + 8 implies ((#[trigger] top@[j]).0, bot@[j].0) == butterfly_spec(
                TRANSPOSED,
                top0[j].0,
                bot0[j].0,
                twiddle,
            ) by {
                assert(m512(new_u)[j - at] == butterfly_spec(TRANSPOSED, top0[j].0, bot0[j].0, twiddle).0);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// AVX2 with VPCLMULQDQ
// ---------------------------------------------------------------------------------------------
/// The spill of every top nibble `n`: `n ^ n>>1 ^ n>>3`.
///
/// Production computes this table in a `const` block local to `butterfly_lanes_avx2`, with a `while` loop over
/// the 16 nibbles. Verus takes no items inside a function, and evaluates no loops in constants, so the copy
/// lists the 16 values; [`lemma_spill_table`] proves they are the formula's, and the equivalence tests run the
/// kernel on every nibble.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub const SPILL: [u8; 16] = [0, 1, 3, 2, 6, 7, 5, 4, 13, 12, 14, 15, 11, 10, 8, 9];

/// Entry `n` of [`SPILL`] is `n ^ n>>1 ^ n>>3`.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub proof fn lemma_spill_table(n: u64)
    requires
        n < 16,
    ensures
        SPILL[n as int] as u64 == n ^ (n >> 1u64) ^ (n >> 3u64),
{
    assert(SPILL[0] == 0u8 && SPILL[1] == 1u8 && SPILL[2] == 3u8 && SPILL[3] == 2u8);
    assert(SPILL[4] == 6u8 && SPILL[5] == 7u8 && SPILL[6] == 5u8 && SPILL[7] == 4u8);
    assert(SPILL[8] == 13u8 && SPILL[9] == 12u8 && SPILL[10] == 14u8 && SPILL[11] == 15u8);
    assert(SPILL[12] == 11u8 && SPILL[13] == 10u8 && SPILL[14] == 8u8 && SPILL[15] == 9u8);
    let s = SPILL[n as int] as u64;
    assert(s == n ^ (n >> 1u64) ^ (n >> 3u64)) by (bit_vector)
        requires
            n < 16,
            n == 0 ==> s == 0,
            n == 1 ==> s == 1,
            n == 2 ==> s == 3,
            n == 3 ==> s == 2,
            n == 4 ==> s == 6,
            n == 5 ==> s == 7,
            n == 6 ==> s == 5,
            n == 7 ==> s == 4,
            n == 8 ==> s == 13,
            n == 9 ==> s == 12,
            n == 10 ==> s == 14,
            n == 11 ==> s == 15,
            n == 12 ==> s == 11,
            n == 13 ==> s == 10,
            n == 14 ==> s == 8,
            n == 15 ==> s == 9,
    ;
}

/// A word whose bytes 1 to 7 are zero is its byte 0.
#[cfg(target_arch = "x86_64")]
pub proof fn lemma_word_of_low_byte(w: u64, b: u8)
    requires
        (w >> 0u64) as u8 == b,
        (w >> 8u64) as u8 == 0,
        (w >> 16u64) as u8 == 0,
        (w >> 24u64) as u8 == 0,
        (w >> 32u64) as u8 == 0,
        (w >> 40u64) as u8 == 0,
        (w >> 48u64) as u8 == 0,
        (w >> 56u64) as u8 == 0,
    ensures
        w == b as u64,
{
    assert(w == b as u64) by (bit_vector)
        requires
            (w >> 0u64) as u8 == b,
            (w >> 8u64) as u8 == 0,
            (w >> 16u64) as u8 == 0,
            (w >> 24u64) as u8 == 0,
            (w >> 32u64) as u8 == 0,
            (w >> 40u64) as u8 == 0,
            (w >> 48u64) as u8 == 0,
            (w >> 56u64) as u8 == 0,
    ;
}

/// The byte shuffle of `butterfly_lanes_avx2`: with `table` the 16-byte [`SPILL`] in both 128-bit lanes and `s`
/// the top nibbles of `hi`, word `i` of the shuffle is the spill `hi>>63 ^ hi>>61 ^ hi>>60` of `hi[i]`.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
pub proof fn lemma_spill_shuffle(hi: __m256i, s: __m256i, t128: __m128i, table: __m256i, spill: __m256i)
    requires
        m128_bytes(t128) == SPILL,
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(table)[i] == m128(t128)[i % 2],
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(s)[i] == shr_imm(m256(hi)[i], 60),
        forall|k: int|
            0 <= k < 32 ==> #[trigger] m256_bytes(spill)[k] == shuffle_epi8_lane(
                m256_bytes(table)@,
                m256_bytes(s)@,
                k,
            ),
    ensures
        forall|i: int|
            0 <= i < 4 ==> #[trigger] m256(spill)[i] == (m256(hi)[i] >> 63u64) ^ (m256(hi)[i] >> 61u64) ^ (m256(
                hi,
            )[i] >> 60u64),
{
    broadcast use axiom_m128_bytes, axiom_m256_bytes;

    // Byte k of the table is byte k % 16 of SPILL.
    assert forall|k: int| 0 <= k < 32 implies #[trigger] m256_bytes(table)[k] == SPILL[k % 16] by {
        assert(m256_bytes(table)[k] == word_byte(m256(table)@, k));
        assert(SPILL[k % 16] == m128_bytes(t128)[k % 16]);
        assert(m128_bytes(t128)[k % 16] == word_byte(m128(t128)@, k % 16));
        assert((k / 8) % 2 == (k % 16) / 8 && k % 8 == (k % 16) % 8);
        assert(m256(table)[k / 8] == m128(t128)[(k / 8) % 2]);
    }
    assert forall|i: int| 0 <= i < 4 implies #[trigger] m256(spill)[i] == (m256(hi)[i] >> 63u64) ^ (m256(hi)[i]
        >> 61u64) ^ (m256(hi)[i] >> 60u64) by {
        let h = m256(hi)[i];
        let n = h >> 60u64;
        assert(m256(s)[i] == n);
        assert(n < 16) by (bit_vector)
            requires
                n == h >> 60u64,
        ;
        // Byte j of word i of the shuffle: SPILL[n] for j = 0, else SPILL[0] = 0.
        assert forall|j: int| 0 <= j < 8 implies #[trigger] m256_bytes(spill)[8 * i + j] == if j == 0 {
            SPILL[n as int]
        } else {
            0u8
        } by {
            let k = 8 * i + j;
            assert(k / 8 == i && k % 8 == j);
            assert(m256_bytes(s)[k] == word_byte(m256(s)@, k));
            let sh = (8 * j) as u64;
            let b = (n >> sh) as u8;
            assert(m256_bytes(s)[k] == b);
            assert(b & 0x80 == 0 && b & 15 == b && b < 16 && (sh == 0 ==> b as u64 == n) && (sh != 0 ==> b == 0)) by (
            bit_vector)
                requires
                    n < 16,
                    sh == 0 || 8 <= sh < 64,
                    b == (n >> sh) as u8,
            ;
            assert((16 * (k / 16) + b as int) % 16 == b as int);
            assert(SPILL[0] == 0u8);
        }
        let w = m256(spill)[i];
        assert forall|j: int| 0 <= j < 8 implies #[trigger] m256_bytes(spill)[8 * i + j] == (w >> ((8 * j) as u64))
            as u8 by {
            let k = 8 * i + j;
            assert(k / 8 == i && k % 8 == j);
            assert(m256_bytes(spill)[k] == word_byte(m256(spill)@, k));
        }
        assert(m256_bytes(spill)[8 * i + 0] == (w >> 0u64) as u8);
        assert(m256_bytes(spill)[8 * i + 1] == (w >> 8u64) as u8);
        assert(m256_bytes(spill)[8 * i + 2] == (w >> 16u64) as u8);
        assert(m256_bytes(spill)[8 * i + 3] == (w >> 24u64) as u8);
        assert(m256_bytes(spill)[8 * i + 4] == (w >> 32u64) as u8);
        assert(m256_bytes(spill)[8 * i + 5] == (w >> 40u64) as u8);
        assert(m256_bytes(spill)[8 * i + 6] == (w >> 48u64) as u8);
        assert(m256_bytes(spill)[8 * i + 7] == (w >> 56u64) as u8);
        lemma_word_of_low_byte(w, SPILL[n as int]);
        lemma_spill_table(n);
        assert((n ^ (n >> 1u64) ^ (n >> 3u64)) == (h >> 63u64) ^ (h >> 61u64) ^ (h >> 60u64)) by (bit_vector)
            requires
                n == h >> 60u64,
        ;
    }
}

/// One lane of the AVX2 reduction: with `lo`, `hi` the words of `p`, `x = hi ^ spill`, and `x2`, `x8`, `x16`
/// doublings by addition (`x + x` is `x << 1`), `lo ^ (x ^ x2) ^ (x8 ^ x16)` is `k_mod(p)`.
#[cfg(target_arch = "x86_64")]
pub proof fn lemma_avx2_lane(p: u128, acc: u64, lo: u64, hi: u64, x: u64, x2: u64, x4: u64, x8: u64, x16: u64, sum: u64)
    requires
        lo == p as u64,
        hi == (p >> 64u128) as u64,
        x == hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64)),
        x2 == (x + x) as u64,
        x4 == (x2 + x2) as u64,
        x8 == (x4 + x4) as u64,
        x16 == (x8 + x8) as u64,
        sum == acc ^ (lo ^ ((x ^ x2) ^ (x8 ^ x16))),
    ensures
        sum == acc ^ k_mod(p),
{
    assert(x2 == x << 1u64 && x8 == x << 3u64 && x16 == x << 4u64) by (bit_vector)
        requires
            x2 == (x + x) as u64,
            x4 == (x2 + x2) as u64,
            x8 == (x4 + x4) as u64,
            x16 == (x8 + x8) as u64,
    ;
    lemma_shift_reduction(p, lo, hi, x);
    assert(acc ^ (lo ^ ((x ^ x2) ^ (x8 ^ x16))) == acc ^ (lo ^ (x ^ (x << 1u64) ^ (x << 3u64) ^ (x << 4u64))))
        by (bit_vector)
        requires
            x2 == x << 1u64,
            x8 == x << 3u64,
            x16 == x << 4u64,
    ;
}

/// Four F64 butterflies with a shared twiddle, for a machine with VPCLMULQDQ but no AVX-512.
///
/// Rewritten for Verus: the rows are `top[at..at + 4]` and `bot[at..at + 4]` instead of two pointers, loaded and
/// stored by [`loadu256_at`] and [`storeu256_at`] (see the module documentation); the nibble table is the module
/// constant [`SPILL`], loaded by [`loadu128_bytes`] (production: `_mm_loadu_si128(SPILL.as_ptr().cast())`).
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX2.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx2",
    not(target_feature = "avx512f")
))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn butterfly_lanes_avx2<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], at: usize, twiddle: u64)
    requires
        at + 4 <= old(top).len(),
        at + 4 <= old(bot).len(),
    ensures
        butterflied(TRANSPOSED, old(top)@, old(bot)@, final(top)@, final(bot)@, at as int, at + 4, twiddle),
{
    // The lane lemmas unfold these; here they only need to match the intrinsics' postconditions.
    hide(clmul_lane);
    hide(clmul_words);
    hide(unpacklo_lane);
    hide(unpackhi_lane);
    hide(shuffle_epi8_lane);
    hide(butterfly_spec);
    let ghost (top0, bot0) = (top@, bot@);
    // SAFETY:
    // - The caller supplies two valid four-word rows.
    // - This function's target features cover every intrinsic below.
    unsafe {
        let u = loadu256_at(top, at);
        let v = loadu256_at(bot, at);
        let tw = _mm256_set1_epi64x(twiddle as i64);

        // The row multiplied by the twiddle, and the row the product is added to.
        let (m, acc) = if TRANSPOSED {
            (_mm256_xor_si256(u, v), v)
        } else {
            (v, u)
        };

        // Products m * t, one 128-bit product per 128-bit lane, then back to lane order.
        let even = _mm256_clmulepi64_epi128::<0x00>(m, tw);
        let odd = _mm256_clmulepi64_epi128::<0x11>(m, tw);
        let lo = _mm256_unpacklo_epi64(even, odd);
        let hi = _mm256_unpackhi_epi64(even, odd);

        // The spill of every top nibble.
        let t128 = loadu128_bytes(&SPILL);
        let table = _mm256_broadcastsi128_si256(t128);
        let nibbles = _mm256_srli_epi64::<60>(hi);
        let spill = _mm256_shuffle_epi8(table, nibbles);
        // Both hi and spill are multiplied by the same constant, so fold them first.
        let x = _mm256_xor_si256(hi, spill);
        let x2 = _mm256_add_epi64(x, x);
        let x8 = {
            let x4 = _mm256_add_epi64(x2, x2);
            _mm256_add_epi64(x4, x4)
        };
        let x16 = _mm256_add_epi64(x8, x8);
        let gx = _mm256_xor_si256(_mm256_xor_si256(x, x2), _mm256_xor_si256(x8, x16));
        let product = _mm256_xor_si256(lo, gx);

        let sum = _mm256_xor_si256(acc, product);
        let (new_u, new_v) = if TRANSPOSED {
            (m, sum)
        } else {
            (sum, _mm256_xor_si256(v, sum))
        };
        proof {
            lemma_i64_round_trip(twiddle);
            lemma_spill_shuffle(hi, nibbles, t128, table, spill);
            // The products, in lane order.
            assert forall|i: int| 0 <= i < 4 implies #[trigger] m256(lo)[i] == clmul(m256(m)[i], twiddle as u128) as u64
                && m256(hi)[i] == (clmul(m256(m)[i], twiddle as u128) >> 64u128) as u64 by {
                lemma_products_in_lane_order(
                    m256(m)@,
                    m256(tw)@,
                    m256(even)@,
                    m256(odd)@,
                    m256(lo)@,
                    m256(hi)@,
                    twiddle,
                    i,
                );
            }
            // Their reduction: sum = acc + m t.
            assert forall|i: int| 0 <= i < 4 implies #[trigger] m256(sum)[i] == m256(acc)[i] ^ k_mul(m256(m)[i], twiddle) by {
                let x2i = m256(x2)[i];
                lemma_avx2_lane(
                    clmul(m256(m)[i], twiddle as u128),
                    m256(acc)[i],
                    m256(lo)[i],
                    m256(hi)[i],
                    m256(x)[i],
                    x2i,
                    (x2i + x2i) as u64,
                    m256(x8)[i],
                    m256(x16)[i],
                    m256(sum)[i],
                );
            }
            // The new rows.
            assert forall|i: int| 0 <= i < 4 implies #[trigger] m256(new_u)[i] == butterfly_spec(
                TRANSPOSED,
                top0[at + i].0,
                bot0[at + i].0,
                twiddle,
            ).0 && m256(new_v)[i] == butterfly_spec(TRANSPOSED, top0[at + i].0, bot0[at + i].0, twiddle).1 by {
                lemma_butterfly_lane(
                    TRANSPOSED,
                    top0[at + i].0,
                    bot0[at + i].0,
                    twiddle,
                    m256(m)[i],
                    m256(acc)[i],
                    m256(sum)[i],
                    m256(new_u)[i],
                    m256(new_v)[i],
                );
            }
        }
        storeu256_at(top, at, new_u);
        storeu256_at(bot, at, new_v);
        proof {
            assert forall|j: int| at <= j < at + 4 implies ((#[trigger] top@[j]).0, bot@[j].0) == butterfly_spec(
                TRANSPOSED,
                top0[j].0,
                bot0[j].0,
                twiddle,
            ) by {
                assert(m256(new_u)[j - at] == butterfly_spec(TRANSPOSED, top0[j].0, bot0[j].0, twiddle).0);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// NEON with PMULL
// ---------------------------------------------------------------------------------------------
/// The two products of a register pair by the twiddle, read back as `uint64x2_t`: their lanes as one `u128` are
/// the carry-less products.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub proof fn lemma_pmull_products(m: uint64x2_t, t: u64, x0: u128, x1: u128)
    requires
        x0 == clmul(u64x2(m)[0], t as u128),
        x1 == clmul(u64x2(m)[1], t as u128),
    ensures
        u64x2_u128(transmuted::<u128, uint64x2_t>(x0)) == x0,
        u64x2_u128(transmuted::<u128, uint64x2_t>(x1)) == x1,
{
    broadcast use axiom_u128_as_u64x2;

    assert(((x0 as u64) as u128) | ((((x0 >> 64u128) as u64) as u128) << 64u128) == x0) by (bit_vector);
    assert(((x1 as u64) as u128) | ((((x1 >> 64u128) as u64) as u128) << 64u128) == x1) by (bit_vector);
}

/// One register pair of a NEON kernel: lane `l` of `(nu, nv)` is lane `l` of `(u, v)` through the butterfly.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub proof fn lemma_neon_pair(
    transposed: bool,
    t: u64,
    u: uint64x2_t,
    v: uint64x2_t,
    m: uint64x2_t,
    acc: uint64x2_t,
    prod: uint64x2_t,
    sum: uint64x2_t,
    nu: uint64x2_t,
    nv: uint64x2_t,
)
    requires
        forall|l: int|
            0 <= l < 2 ==> #[trigger] u64x2(m)[l] == if transposed {
                u64x2(u)[l] ^ u64x2(v)[l]
            } else {
                u64x2(v)[l]
            },
        acc == if transposed {
            v
        } else {
            u
        },
        u64x2(prod)[0] == k_mul(u64x2(m)[0], t),
        u64x2(prod)[1] == k_mul(u64x2(m)[1], t),
        u64x2(sum)[0] == u64x2(acc)[0] ^ u64x2(prod)[0],
        u64x2(sum)[1] == u64x2(acc)[1] ^ u64x2(prod)[1],
        nu == if transposed {
            m
        } else {
            sum
        },
        forall|l: int|
            0 <= l < 2 ==> #[trigger] u64x2(nv)[l] == if transposed {
                u64x2(sum)[l]
            } else {
                u64x2(v)[l] ^ u64x2(sum)[l]
            },
    ensures
        forall|l: int|
            0 <= l < 2 ==> (#[trigger] u64x2(nu)[l], u64x2(nv)[l]) == butterfly_spec(
                transposed,
                u64x2(u)[l],
                u64x2(v)[l],
                t,
            ),
{
    assert forall|l: int| 0 <= l < 2 implies (#[trigger] u64x2(nu)[l], u64x2(nv)[l]) == butterfly_spec(
        transposed,
        u64x2(u)[l],
        u64x2(v)[l],
        t,
    ) by {
        assert(u64x2(m)[l] == if transposed {
            u64x2(u)[l] ^ u64x2(v)[l]
        } else {
            u64x2(v)[l]
        });
        assert(u64x2(nv)[l] == if transposed {
            u64x2(sum)[l]
        } else {
            u64x2(v)[l] ^ u64x2(sum)[l]
        });
        if l == 0 {
            lemma_butterfly_lane(
                transposed,
                u64x2(u)[0],
                u64x2(v)[0],
                t,
                u64x2(m)[0],
                u64x2(acc)[0],
                u64x2(sum)[0],
                u64x2(nu)[0],
                u64x2(nv)[0],
            );
        } else {
            lemma_butterfly_lane(
                transposed,
                u64x2(u)[1],
                u64x2(v)[1],
                t,
                u64x2(m)[1],
                u64x2(acc)[1],
                u64x2(sum)[1],
                u64x2(nu)[1],
                u64x2(nv)[1],
            );
        }
    }
}

/// The reduced products of a register by the twiddle, as [`reduce_pair_pmull4`] returns them from the two PMULLs.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub proof fn lemma_reduced_products(m: uint64x2_t, t: u64, p0: uint64x2_t, p1: uint64x2_t, prod: uint64x2_t)
    requires
        p0 == transmuted::<u128, uint64x2_t>(clmul(u64x2(m)[0], t as u128)),
        p1 == transmuted::<u128, uint64x2_t>(clmul(u64x2(m)[1], t as u128)),
        u64x2(prod)[0] == k_mod(u64x2_u128(p0)),
        u64x2(prod)[1] == k_mod(u64x2_u128(p1)),
    ensures
        u64x2(prod)[0] == k_mul(u64x2(m)[0], t),
        u64x2(prod)[1] == k_mul(u64x2(m)[1], t),
{
    lemma_pmull_products(m, t, clmul(u64x2(m)[0], t as u128), clmul(u64x2(m)[1], t as u128));
}

/// Eight F64 butterflies as four independent NEON lane-pair reductions.
/// Loading all four bottom vectors before reducing them gives the out-of-order
/// core four independent PMULL chains to schedule, while one call amortizes
/// loop control and the duplicated twiddle/reduction constants over 8 lanes.
///
/// Rewritten for Verus: the rows are `top[at..at + 8]` and `bot[at..at + 8]` instead of two pointers, loaded and
/// stored by [`vld1q_u64_at`] and [`vst1q_u64_at`] (see the module documentation).
///
/// # Safety
/// Requires the `aes` target feature.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
pub unsafe fn butterfly_lanes_neon_8<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], at: usize, twiddle: u64)
    requires
        at + 8 <= old(top).len(),
        at + 8 <= old(bot).len(),
    ensures
        butterflied(TRANSPOSED, old(top)@, old(bot)@, final(top)@, final(bot)@, at as int, at + 8, twiddle),
{
    let ghost (top0, bot0) = (top@, bot@);
    // SAFETY: caller guarantees the two eight-element regions; F64 is
    // repr(transparent) over u64 and this function carries the aes feature.
    unsafe {
        let v0 = vld1q_u64_at(bot, at);
        let v1 = vld1q_u64_at(bot, at + 2);
        let v2 = vld1q_u64_at(bot, at + 4);
        let v3 = vld1q_u64_at(bot, at + 6);
        let u0 = vld1q_u64_at(top, at);
        let u1 = vld1q_u64_at(top, at + 2);
        let u2 = vld1q_u64_at(top, at + 4);
        let u3 = vld1q_u64_at(top, at + 6);
        let tw = vdupq_n_u64(twiddle);
        // The rows multiplied by the twiddle, and the rows the products are added to.
        let ((m0, a0), (m1, a1), (m2, a2), (m3, a3)) = if TRANSPOSED {
            (
                (veorq_u64(u0, v0), v0),
                (veorq_u64(u1, v1), v1),
                (veorq_u64(u2, v2), v2),
                (veorq_u64(u3, v3), v3),
            )
        } else {
            ((v0, u0), (v1, u1), (v2, u2), (v3, u3))
        };

        proof {
            broadcast use axiom_u64x2_as_p64x2;
        }
        let p00: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m0), twiddle));
        let p01: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m0),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p10: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m1), twiddle));
        let p11: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m1),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p20: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m2), twiddle));
        let p21: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m2),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p30: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m3), twiddle));
        let p31: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m3),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));

        let r0 = reduce_pair_pmull4(p00, p01);
        let r1 = reduce_pair_pmull4(p10, p11);
        let r2 = reduce_pair_pmull4(p20, p21);
        let r3 = reduce_pair_pmull4(p30, p31);
        proof {
            lemma_reduced_products(m0, twiddle, p00, p01, r0);
            lemma_reduced_products(m1, twiddle, p10, p11, r1);
            lemma_reduced_products(m2, twiddle, p20, p21, r2);
            lemma_reduced_products(m3, twiddle, p30, p31, r3);
        }
        let sum0 = veorq_u64(a0, r0);
        let sum1 = veorq_u64(a1, r1);
        let sum2 = veorq_u64(a2, r2);
        let sum3 = veorq_u64(a3, r3);
        // Forward: u' = u + v * t, then v' = v + u'. Transposed: u' = u + v, then v' = v + u' * t.
        let ((new_u0, new_v0), (new_u1, new_v1), (new_u2, new_v2), (new_u3, new_v3)) = if TRANSPOSED {
            ((m0, sum0), (m1, sum1), (m2, sum2), (m3, sum3))
        } else {
            (
                (sum0, veorq_u64(v0, sum0)),
                (sum1, veorq_u64(v1, sum1)),
                (sum2, veorq_u64(v2, sum2)),
                (sum3, veorq_u64(v3, sum3)),
            )
        };
        proof {
            lemma_neon_pair(TRANSPOSED, twiddle, u0, v0, m0, a0, r0, sum0, new_u0, new_v0);
            lemma_neon_pair(TRANSPOSED, twiddle, u1, v1, m1, a1, r1, sum1, new_u1, new_v1);
            lemma_neon_pair(TRANSPOSED, twiddle, u2, v2, m2, a2, r2, sum2, new_u2, new_v2);
            lemma_neon_pair(TRANSPOSED, twiddle, u3, v3, m3, a3, r3, sum3, new_u3, new_v3);
        }

        vst1q_u64_at(top, at, new_u0);
        vst1q_u64_at(top, at + 2, new_u1);
        vst1q_u64_at(top, at + 4, new_u2);
        vst1q_u64_at(top, at + 6, new_u3);
        vst1q_u64_at(bot, at, new_v0);
        vst1q_u64_at(bot, at + 2, new_v1);
        vst1q_u64_at(bot, at + 4, new_v2);
        vst1q_u64_at(bot, at + 6, new_v3);
        proof {
            assert forall|j: int| at <= j < at + 8 implies ((#[trigger] top@[j]).0, bot@[j].0) == butterfly_spec(
                TRANSPOSED,
                top0[j].0,
                bot0[j].0,
                twiddle,
            ) by {
                let l = (j - at) % 2;
                if j < at + 2 {
                    assert((u64x2(new_u0)[l], u64x2(new_v0)[l]) == butterfly_spec(TRANSPOSED, u64x2(u0)[l], u64x2(v0)[l], twiddle));
                } else if j < at + 4 {
                    assert((u64x2(new_u1)[l], u64x2(new_v1)[l]) == butterfly_spec(TRANSPOSED, u64x2(u1)[l], u64x2(v1)[l], twiddle));
                } else if j < at + 6 {
                    assert((u64x2(new_u2)[l], u64x2(new_v2)[l]) == butterfly_spec(TRANSPOSED, u64x2(u2)[l], u64x2(v2)[l], twiddle));
                } else {
                    assert((u64x2(new_u3)[l], u64x2(new_v3)[l]) == butterfly_spec(TRANSPOSED, u64x2(u3)[l], u64x2(v3)[l], twiddle));
                }
            }
        }
    }
}

/// Two F64 butterflies with a shared twiddle, NEON-resident end to end.
/// The two products issue as PMULL/PMULL2 on the loaded row (no lane
/// extraction) and reduce through the all-PMULL lane-pair fold
/// ([`reduce_pair_pmull4`]), replacing the
/// old 10-op shift-XOR fold chain.
///
/// Rewritten for Verus: the rows are `top[at..at + 2]` and `bot[at..at + 2]` instead of two pointers, loaded and
/// stored by [`vld1q_u64_at`] and [`vst1q_u64_at`] (see the module documentation).
///
/// # Safety
/// Requires the `aes` target feature.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
pub unsafe fn butterfly_lane_pair_neon<const TRANSPOSED: bool>(top: &mut [F64], bot: &mut [F64], at: usize, twiddle: u64)
    requires
        at + 2 <= old(top).len(),
        at + 2 <= old(bot).len(),
    ensures
        butterflied(TRANSPOSED, old(top)@, old(bot)@, final(top)@, final(bot)@, at as int, at + 2, twiddle),
{
    let ghost (top0, bot0) = (top@, bot@);
    // SAFETY: caller guarantees the pointees; F64 is repr(transparent) u64.
    unsafe {
        let u = vld1q_u64_at(top, at);
        let v = vld1q_u64_at(bot, at);
        let m = if TRANSPOSED { veorq_u64(u, v) } else { v };
        // Products m_lane * twiddle: PMULL on the low lanes, PMULL2 on the
        // highs (the dup is loop-invariant and hoisted after inlining).
        let tw = vdupq_n_u64(twiddle);
        proof {
            broadcast use axiom_u64x2_as_p64x2;
        }
        let p0: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(m), twiddle));
        let p1: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(m),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let prod = reduce_pair_pmull4(p0, p1);
        proof {
            lemma_reduced_products(m, twiddle, p0, p1, prod);
        }
        let (new_u, new_v) = if TRANSPOSED {
            (m, veorq_u64(v, prod))
        } else {
            let new_u = veorq_u64(u, prod);
            (new_u, veorq_u64(v, new_u))
        };
        proof {
            let acc = if TRANSPOSED { v } else { u };
            let sum = if TRANSPOSED { new_v } else { new_u };
            lemma_neon_pair(TRANSPOSED, twiddle, u, v, m, acc, prod, sum, new_u, new_v);
        }
        vst1q_u64_at(top, at, new_u);
        vst1q_u64_at(bot, at, new_v);
        proof {
            assert forall|j: int| at <= j < at + 2 implies ((#[trigger] top@[j]).0, bot@[j].0) == butterfly_spec(
                TRANSPOSED,
                top0[j].0,
                bot0[j].0,
                twiddle,
            ) by {
                let l = j - at;
                assert((u64x2(new_u)[l], u64x2(new_v)[l]) == butterfly_spec(TRANSPOSED, u64x2(u)[l], u64x2(v)[l], twiddle));
            }
        }
    }
}

} // verus!
