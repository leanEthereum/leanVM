// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 prover message: fully optimized (shift_reduce + extract_c, scalar).
//!
//! Scalar Rust implementation (no NEON). Three layered optimizations on top of
//! the `round1_extract_c` scaffold:
//!
//! 1. **Geometric small-eq + shift_reduce inner** (3 inner-most rest-dims).
//!    Protocol fixes the three small challenges to
//!    `r_rest[..3] = φ_8([0xF7, 0x53, 0xB5])`, which makes
//!    `eq_small[K] = C_s · α^K` (geometric in the embedded AES root α).
//!    The shift_reduce trick computes
//!    `Σ_K eq_small[K] · φ_8(y_K)  =  C_s · φ_8(reduce(Σ_K y_K << K))`,
//!    replacing 8 F192 mults per lane with 8 u16 XOR-shifts + one F_8
//!    reduction.
//!
//! 2. **Geometric medium-eq + convert table** (4 next rest-dims).
//!    Protocol fixes the four medium challenges to
//!    `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`, which makes
//!    `eq_med[b] = γ^b / D` for `D = ∏(1+γ^{2^{i-1}})`.
//!    A precomputed `convert[b][v] = γ^b · φ_8(v)` table replaces field multiplications with lookups and XORs.
//!
//! 3. **D⁻¹ absorbed into eq_lo.**
//!    Pre-scale `eq_lo[i] ← eq_lo[i] · D⁻¹` once before the loop; this cancels
//!    the `1/D` from the medium-eq factorization, leaving only the `C_s`
//!    factor in the relative output scaling.
//!
//! Net output relationship vs the naive / structural versions:
//!   `C_s · (res_AB[i] + res_C_lifted[i])  ==  naive_p_ab[i] + naive_p_c[i]`
//! with `C_s = φ_8(0x1C)`.
//!
//! This variant is hardcoded for `k_skip = 6` (ell=64, n_chunks=8, N_INNER=7).

use std::sync::OnceLock;

use pcs::ntt::InvNttTableByteSingleGf8;
use primitives::bits::bit_transpose_64bytes;
use primitives::field::gf2_8::gf8_reduce;
use primitives::field::{F8, F192, PHI_8_TABLE_192 as PHI_8_TABLE, phi8_192 as phi8};

#[cfg(test)]
use super::univariate_skip::pack_bits;
use super::univariate_skip::{SplitEq, ntt_extend_vec};
use super::{K_SKIP, N_INNER, PaddingSpec};

// ---------------------------------------------------------------------------
// Protocol constants: fixed by the optimization design.
// ---------------------------------------------------------------------------

const ELL: usize = 64;
const N_CHUNKS: usize = 8;
const N_MEDIUM: usize = 4;

/// The three small-eq challenges (as F_8 values, then embedded via φ_8).
/// Choosing these specific values is what makes `eq_small[K] = C_s · α^K`.
///
/// **Soundness dependency.** These three constants, with the four medium ones
/// returned by [`medium_challenges`], are the seven fixed zerocheck coordinates
/// `a`. `lem:fixed-zerocheck` requires their `2^7` equality WEIGHTS
/// `{eq(a, b)}` to be **F₂-linearly independent** in F₁₉₂, which is strictly
/// stronger than independence of the seven coordinates. Zerocheck soundness
/// relies on it (a witness aligned with the friendly subspace would otherwise
/// let the prover cancel the URM message), and so does WHIR's L0 list-collapse
/// argument (the SZ bound `(m-7)/|F|` for MLE collisions at `r`). Asserted by
/// `tests::friendly_challenges_f2_independent`.
const SMALL_CHAL_F8: [u8; 3] = [0xF7, 0x53, 0xB5];

/// `C_s` as an F_8 value. Verified empirically by the C++ project.
const C_S_F8: u8 = 0x1C;

/// The constant `C_s = φ_8(0x1C) ∈ F_{2^192}`: the relative scaling factor
/// between this optimized output and the naive output.
pub fn c_s() -> F192 {
    phi8(F8(C_S_F8))
}

/// The three F192 small challenges (embeddings of `SMALL_CHAL_F8`): caller
/// must place these at `r_rest[..3]` for the naive cross-check to
/// produce a result related to the optimized output by exactly `C_s`.
pub fn small_challenges() -> [F192; 3] {
    [
        phi8(F8(SMALL_CHAL_F8[0])),
        phi8(F8(SMALL_CHAL_F8[1])),
        phi8(F8(SMALL_CHAL_F8[2])),
    ]
}

/// The four F192 medium challenges `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`.
/// Caller must place these at `r_rest[3..7]` for the naive
/// cross-check.
pub fn medium_challenges() -> [F192; 4] {
    let g1 = medium_generator();
    let g2 = g1.square();
    let g4 = g2.square();
    let g8 = g4.square();
    [
        g1 * (F192::ONE + g1).inv(),
        g2 * (F192::ONE + g2).inv(),
        g4 * (F192::ONE + g4).inv(),
        g8 * (F192::ONE + g8).inv(),
    ]
}

/// Protocol medium-coordinate generator in the tower basis.
const fn medium_generator() -> F192 {
    F192::new(0x243f_6a88_85a3_08d3, 0x1319_8a2e_0370_7344, 0xa409_3822_299f_31d0)
}

/// `D = (1+γ)(1+γ^2)(1+γ^4)(1+γ^8)`; `D⁻¹` cancels the medium-eq normalization.
fn compute_d_inv() -> F192 {
    let g1 = medium_generator();
    let g2 = g1.square();
    let g4 = g2.square();
    let g8 = g4.square();
    ((F192::ONE + g1) * (F192::ONE + g2) * (F192::ONE + g4) * (F192::ONE + g8)).inv()
}

static D_INV_CACHE: OnceLock<F192> = OnceLock::new();
fn d_inv() -> F192 {
    *D_INV_CACHE.get_or_init(compute_d_inv)
}

// ---------------------------------------------------------------------------
// Convert table: γ^b · φ_8(v) for b ∈ [0, 16), v ∈ [0, 256).
// Computed once and cached.
// ---------------------------------------------------------------------------

const N_MEDIUM_VALUES: usize = 16;

/// The convert table as its shape rather than as a flat run: a `u8` cannot index
/// a 256-entry row out of bounds and the row index is bounded by the loop, so
/// the fold's two lookups carry no bounds check and the row stride folds into
/// the address. Flat, each lookup costs a check, a branch and a multiply by the
/// 24-byte element stride, and the branches keep the constant-trip loop around
/// them from unrolling.
#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
type ConvertTable = [[F192; 256]; N_MEDIUM_VALUES];

#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
static CONVERT_TABLE_CACHE: OnceLock<Box<ConvertTable>> = OnceLock::new();

/// `gamma^b` for each medium position `b`.
fn gamma_powers() -> &'static [F192; N_MEDIUM_VALUES] {
    static CACHE: OnceLock<[F192; N_MEDIUM_VALUES]> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut pow = [F192::ONE; N_MEDIUM_VALUES];
        for b in 1..N_MEDIUM_VALUES {
            pow[b] = pow[b - 1] * medium_generator();
        }
        pow
    })
}

#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
fn build_convert_table() -> Box<ConvertTable> {
    let mut table: Box<ConvertTable> = Box::new([[F192::ZERO; 256]; N_MEDIUM_VALUES]);
    for (row, &g_b) in table.iter_mut().zip(gamma_powers()) {
        for (entry, &phi) in row.iter_mut().zip(PHI_8_TABLE.iter()) {
            *entry = g_b * phi;
        }
    }
    table
}

#[cfg(any(
    test,
    not(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))
))]
fn convert_table() -> &'static ConvertTable {
    CONVERT_TABLE_CACHE.get_or_init(build_convert_table)
}

// ---------------------------------------------------------------------------
// Shift_reduce inner kernel (AB only: extract_c handles C separately).
//
// For one medium-position b_med and the 8 small-positions K ∈ 0..8:
//   1. Look up NTT-extended A,B at chunk `chunk_byte_base + (b_med*8 + K)*8`.
//   2. y_K[lane] = ntt_a[lane] · ntt_b[lane]  (in F_8).
//   3. acc[lane] ^= (y_K[lane] as u16) << K   (no reduction yet).
// At the end, reduce each acc[lane] back to a u8 in F_8.
//
// Output `out[lane]` is the F_8 representative of Σ_K x^K · y_K[lane] mod p.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Fused NEON inner kernel: inv_NTT apply + F_8 mul + shift_reduce, all in
// NEON registers (no Vec<F8> round-trip).
//
// `xor_apply_byte_into_8_regs::<BH, ODD>` handles one byte position (b ≥ 1).
// `BH` (= b >> 1) selects which chunk-index XOR to apply; `ODD` (= b & 1)
// switches on the within-chunk half-swap. Both const-generic so the compiler
// dead-code-eliminates the if-branch and folds the chunk-index XORs.
//
// `fused_apply_one_k::<K>` runs one full K-row: the initial b=0 plain load,
// 7 calls to the byte helper for b=1..7 (with the specific protocol BH/ODD
// pattern), one 16-lane F_8 mul per output chunk, and finally widen-shift-XOR
// into the per-(K, lane) 16-bit accumulators.
// ---------------------------------------------------------------------------

#[cfg(target_arch = "aarch64")]
// `0 ^ BH` is the i = 0 case of the `i ^ BH` row-select pattern below; spelling
// it out keeps the four loads visibly parallel.
#[allow(clippy::identity_op)]
#[inline(always)]
unsafe fn xor_apply_byte_into_8_regs<const BH: usize>(
    table_base: *const u8,
    a_byte: u8,
    b_byte: u8,
    da0: &mut core::arch::aarch64::uint8x16_t,
    da1: &mut core::arch::aarch64::uint8x16_t,
    da2: &mut core::arch::aarch64::uint8x16_t,
    da3: &mut core::arch::aarch64::uint8x16_t,
    db0: &mut core::arch::aarch64::uint8x16_t,
    db1: &mut core::arch::aarch64::uint8x16_t,
    db2: &mut core::arch::aarch64::uint8x16_t,
    db3: &mut core::arch::aarch64::uint8x16_t,
) {
    use core::arch::aarch64::*;
    unsafe {
        let ra = table_base.add(a_byte as usize * 64);
        let rb = table_base.add(b_byte as usize * 64);
        let va0 = vld1q_u8(ra.add((0 ^ BH) * 16));
        let va1 = vld1q_u8(ra.add((1 ^ BH) * 16));
        let va2 = vld1q_u8(ra.add((2 ^ BH) * 16));
        let va3 = vld1q_u8(ra.add((3 ^ BH) * 16));
        let vb0 = vld1q_u8(rb.add((0 ^ BH) * 16));
        let vb1 = vld1q_u8(rb.add((1 ^ BH) * 16));
        let vb2 = vld1q_u8(rb.add((2 ^ BH) * 16));
        let vb3 = vld1q_u8(rb.add((3 ^ BH) * 16));
        *da0 = veorq_u8(*da0, va0);
        *da1 = veorq_u8(*da1, va1);
        *da2 = veorq_u8(*da2, va2);
        *da3 = veorq_u8(*da3, va3);
        *db0 = veorq_u8(*db0, vb0);
        *db1 = veorq_u8(*db1, vb1);
        *db2 = veorq_u8(*db2, vb2);
        *db3 = veorq_u8(*db3, vb3);
    }
}

/// Process one K-row: 8 byte positions of `a` and `b` via the inv_NTT table,
/// F_8 multiply, widen-shift by K, XOR into the four `(acc_lo, acc_hi)` pairs.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn fused_apply_one_k<const K: i32>(
    table_base: *const u8,
    a_row: *const u8,
    b_row: *const u8,
    acc0_lo: &mut core::arch::aarch64::uint16x8_t,
    acc0_hi: &mut core::arch::aarch64::uint16x8_t,
    acc1_lo: &mut core::arch::aarch64::uint16x8_t,
    acc1_hi: &mut core::arch::aarch64::uint16x8_t,
    acc2_lo: &mut core::arch::aarch64::uint16x8_t,
    acc2_hi: &mut core::arch::aarch64::uint16x8_t,
    acc3_lo: &mut core::arch::aarch64::uint16x8_t,
    acc3_hi: &mut core::arch::aarch64::uint16x8_t,
) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_8::neon::gf8_mul_vec16;
    unsafe {
        // `π_b(i') = i' ⊕ 8b` is a chunk-index XOR by `b >> 1`, which is a free
        // load offset, and for odd `b` a swap of each chunk's two 8-byte halves.
        // That swap is an involution and distributes over XOR, and it commutes
        // with the chunk reindexing, so the eight positions need one swap of the
        // accumulators between the odd group and the even group rather than one
        // per register per odd position: `E ⊕ S(O)` with the odds accumulated
        // plainly first. Four times fewer `ext`, and `ext` was the largest
        // single share of this body's vector work.
        let ra1 = table_base.add(*a_row.add(1) as usize * 64);
        let rb1 = table_base.add(*b_row.add(1) as usize * 64);
        let mut da0 = vld1q_u8(ra1);
        let mut da1 = vld1q_u8(ra1.add(16));
        let mut da2 = vld1q_u8(ra1.add(32));
        let mut da3 = vld1q_u8(ra1.add(48));
        let mut db0 = vld1q_u8(rb1);
        let mut db1 = vld1q_u8(rb1.add(16));
        let mut db2 = vld1q_u8(rb1.add(32));
        let mut db3 = vld1q_u8(rb1.add(48));

        // The rest of the odd positions, b = 3, 5, 7.
        macro_rules! apply {
            ($bh:literal, $b:literal) => {
                xor_apply_byte_into_8_regs::<$bh>(
                    table_base,
                    *a_row.add($b),
                    *b_row.add($b),
                    &mut da0,
                    &mut da1,
                    &mut da2,
                    &mut da3,
                    &mut db0,
                    &mut db1,
                    &mut db2,
                    &mut db3,
                )
            };
        }
        apply!(1, 3);
        apply!(2, 5);
        apply!(3, 7);

        // One swap for the whole odd group.
        da0 = vextq_u8::<8>(da0, da0);
        da1 = vextq_u8::<8>(da1, da1);
        da2 = vextq_u8::<8>(da2, da2);
        da3 = vextq_u8::<8>(da3, da3);
        db0 = vextq_u8::<8>(db0, db0);
        db1 = vextq_u8::<8>(db1, db1);
        db2 = vextq_u8::<8>(db2, db2);
        db3 = vextq_u8::<8>(db3, db3);

        // The even positions, b = 0, 2, 4, 6, which need no swap.
        apply!(0, 0);
        apply!(1, 2);
        apply!(2, 4);
        apply!(3, 6);

        // F_8 multiply lane-wise (4 × 16 lanes = 64 total).
        let y0 = gf8_mul_vec16(da0, db0);
        let y1 = gf8_mul_vec16(da1, db1);
        let y2 = gf8_mul_vec16(da2, db2);
        let y3 = gf8_mul_vec16(da3, db3);

        // Widen-shift by K, XOR into the 16-bit accumulators.
        *acc0_lo = veorq_u16(*acc0_lo, vshll_n_u8::<K>(vget_low_u8(y0)));
        *acc0_hi = veorq_u16(*acc0_hi, vshll_n_u8::<K>(vget_high_u8(y0)));
        *acc1_lo = veorq_u16(*acc1_lo, vshll_n_u8::<K>(vget_low_u8(y1)));
        *acc1_hi = veorq_u16(*acc1_hi, vshll_n_u8::<K>(vget_high_u8(y1)));
        *acc2_lo = veorq_u16(*acc2_lo, vshll_n_u8::<K>(vget_low_u8(y2)));
        *acc2_hi = veorq_u16(*acc2_hi, vshll_n_u8::<K>(vget_high_u8(y2)));
        *acc3_lo = veorq_u16(*acc3_lo, vshll_n_u8::<K>(vget_low_u8(y3)));
        *acc3_hi = veorq_u16(*acc3_hi, vshll_n_u8::<K>(vget_high_u8(y3)));
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn shift_reduce_inner_ab_fused_neon(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_8::neon::gf8_reduce_vec16;

    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    let table_base = inv_table.data_ptr();

    unsafe {
        let mut acc0_lo = vdupq_n_u16(0);
        let mut acc0_hi = vdupq_n_u16(0);
        let mut acc1_lo = vdupq_n_u16(0);
        let mut acc1_hi = vdupq_n_u16(0);
        let mut acc2_lo = vdupq_n_u16(0);
        let mut acc2_hi = vdupq_n_u16(0);
        let mut acc3_lo = vdupq_n_u16(0);
        let mut acc3_hi = vdupq_n_u16(0);

        // 8 K-iterations: each consumes N_CHUNKS = 8 packed witness bytes
        // for `a` and `b`. K is a const generic so `vshll_n_u8::<K>` specializes.
        macro_rules! do_k {
            ($k:literal) => {{
                let off = byte_base_b + $k * N_CHUNKS;
                fused_apply_one_k::<$k>(
                    table_base,
                    a_packed.as_ptr().add(off),
                    b_packed.as_ptr().add(off),
                    &mut acc0_lo,
                    &mut acc0_hi,
                    &mut acc1_lo,
                    &mut acc1_hi,
                    &mut acc2_lo,
                    &mut acc2_hi,
                    &mut acc3_lo,
                    &mut acc3_hi,
                );
            }};
        }
        do_k!(0);
        do_k!(1);
        do_k!(2);
        do_k!(3);
        do_k!(4);
        do_k!(5);
        do_k!(6);
        do_k!(7);

        // Reduce 16-bit accs → 16-byte F_8 results (4 × 16 lanes).
        let r0 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc0_lo), vreinterpretq_u8_u16(acc0_hi));
        let r1 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc1_lo), vreinterpretq_u8_u16(acc1_hi));
        let r2 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc2_lo), vreinterpretq_u8_u16(acc2_hi));
        let r3 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc3_lo), vreinterpretq_u8_u16(acc3_hi));

        let p = out.as_mut_ptr();
        vst1q_u8(p, r0);
        vst1q_u8(p.add(16), r1);
        vst1q_u8(p.add(32), r2);
        vst1q_u8(p.add(48), r3);
    }
}

/// Dispatch helper: picks the fused NEON kernel when available, otherwise scalar.
#[inline]
fn shift_reduce_inner_ab(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    #[cfg(target_arch = "aarch64")]
    {
        shift_reduce_inner_ab_fused_neon(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
    {
        // SAFETY: gfni and avx512bw are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_gfni_512(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out) };
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", not(target_feature = "avx512bw")))]
    {
        // SAFETY: gfni is statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_gfni(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out) };
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "gfni"))))]
    {
        shift_reduce_inner_ab_scalar(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out);
    }
}

/// The GFNI kernel one register wide: `ELL` is 64, so the whole column is one
/// ZMM and the combine issues a quarter of the instructions the 128-bit arm
/// does. Byte unpacking and `packus` both work within 128-bit lanes and are
/// exact inverses there, so the widened accumulators may sit in a different
/// order than the narrow arm's and still narrow back to the same bytes.
///
/// # Safety
/// Requires the `gfni` and `avx512bw` target features.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
#[target_feature(enable = "gfni", enable = "avx512f", enable = "avx512bw")]
unsafe fn shift_reduce_inner_ab_gfni_512(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    use core::arch::x86_64::*;

    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];

    // SAFETY: the target features are carried by the function; the loads and
    // stores stay within a_col/b_col/out, each exactly `ELL` bytes.
    unsafe {
        let (mut acc_lo, mut acc_hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
        let zero = _mm512_setzero_si512();

        for k in 0..8 {
            let chunk_off = byte_base_b + k * N_CHUNKS;
            inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
            inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
            let y = _mm512_gf2p8mul_epi8(
                _mm512_loadu_si512(a_col.as_ptr().cast()),
                _mm512_loadu_si512(b_col.as_ptr().cast()),
            );
            let shift = _mm_cvtsi32_si128(k as i32);
            acc_lo = _mm512_xor_si512(acc_lo, _mm512_sll_epi16(_mm512_unpacklo_epi8(y, zero), shift));
            acc_hi = _mm512_xor_si512(acc_hi, _mm512_sll_epi16(_mm512_unpackhi_epi8(y, zero), shift));
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm512_set1_epi16(0xff);
        let fold = |p: __m512i| -> __m512i {
            let h = _mm512_srli_epi16::<8>(p);
            _mm512_xor_si512(
                _mm512_and_si512(p, mask_ff),
                _mm512_xor_si512(
                    _mm512_xor_si512(h, _mm512_slli_epi16::<1>(h)),
                    _mm512_xor_si512(_mm512_slli_epi16::<3>(h), _mm512_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m512i| _mm512_and_si512(fold(fold(p)), mask_ff);
        _mm512_storeu_si512(
            out.as_mut_ptr().cast(),
            _mm512_packus_epi16(reduce(acc_lo), reduce(acc_hi)),
        );
    }
}

/// x86 GFNI kernel: same structure as the scalar fallback (SSE2 `apply` into
/// `a_col`/`b_col`, then vectorized combine), with the per-lane F_8 products
/// done 16-at-a-time by `gf2p8mulb` (`_mm_gf2p8mul_epi8`).
///
/// flock's F_8 is GF(2^8) mod x^8 + x^4 + x^3 + x + 1 (= 0x11B) in standard
/// bit order: exactly the field `gf2p8mulb` implements, so the instruction
/// IS the field mul. `gf2p8mulb` returns the reduced product, and reduction
/// commutes with the `Σ_K x^K · y_K` accumulation (the shifted sum is ≤ 15
/// bits), so one `gf8_reduce` per lane at the end still matches the scalar
/// path bit-for-bit.
///
/// # Safety
/// Requires the `gfni` target feature (plus SSE2, baseline on x86_64).
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", not(target_feature = "avx512bw")))]
#[target_feature(enable = "gfni", enable = "sse2")]
unsafe fn shift_reduce_inner_ab_gfni(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    use core::arch::x86_64::*;

    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];

    // SAFETY: gfni+sse2 are carried by the function's target features; the
    // pointer loads/stores stay within a_col/b_col/out (each 64 bytes).
    unsafe {
        // 8 u16x8 accumulators = 64 u16 lanes, matching the inv-NTT output.
        let mut acc = [_mm_setzero_si128(); 8];

        for k in 0..8 {
            let chunk_off = byte_base_b + k * N_CHUNKS;
            inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
            inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
            let a_ptr = a_col.as_ptr() as *const __m128i;
            let b_ptr = b_col.as_ptr() as *const __m128i;
            let shift = _mm_cvtsi32_si128(k as i32);
            let zero = _mm_setzero_si128();
            for v in 0..4 {
                let y = _mm_gf2p8mul_epi8(_mm_loadu_si128(a_ptr.add(v)), _mm_loadu_si128(b_ptr.add(v)));
                // Widen the 16 product bytes to u16 and XOR-accumulate << k.
                let lo = _mm_unpacklo_epi8(y, zero);
                let hi = _mm_unpackhi_epi8(y, zero);
                acc[2 * v] = _mm_xor_si128(acc[2 * v], _mm_sll_epi16(lo, shift));
                acc[2 * v + 1] = _mm_xor_si128(acc[2 * v + 1], _mm_sll_epi16(hi, shift));
            }
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high
        // byte h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 ≡ x^4+x^3+x+1).
        let mask_ff = _mm_set1_epi16(0xff);
        let fold = |p: __m128i| -> __m128i {
            let h = _mm_srli_epi16::<8>(p);
            _mm_xor_si128(
                _mm_and_si128(p, mask_ff),
                _mm_xor_si128(
                    _mm_xor_si128(h, _mm_slli_epi16::<1>(h)),
                    _mm_xor_si128(_mm_slli_epi16::<3>(h), _mm_slli_epi16::<4>(h)),
                ),
            )
        };
        let out_ptr = out.as_mut_ptr() as *mut __m128i;
        for v in 0..4 {
            // Two folds bring 15-bit accumulators down to 8 bits; the second
            // fold's high byte is ≤ 0x0f so lanes stay < 256 for packus.
            let r_lo = _mm_and_si128(fold(fold(acc[2 * v])), mask_ff);
            let r_hi = _mm_and_si128(fold(fold(acc[2 * v + 1])), mask_ff);
            _mm_storeu_si128(out_ptr.add(v), _mm_packus_epi16(r_lo, r_hi));
        }
    }
}

/// Kept under `#[allow(dead_code)]` because the dispatcher only reaches it when
/// neither NEON nor GFNI is available, which is not any platform we build on
/// today. It stays as that fallback AND as the cross-check oracle for
/// `neon_fused_inner_matches_scalar_inner` / `gfni_inner_matches_scalar_inner`.
#[allow(dead_code)]
fn shift_reduce_inner_ab_scalar(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];
    let mut acc: [u16; 64] = [0u16; 64];
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    for k in 0..8 {
        let chunk_off = byte_base_b + k * N_CHUNKS;
        inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
        inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
        for lane in 0..ELL {
            let y = (a_col[lane] * b_col[lane]).0 as u16;
            acc[lane] ^= y << k;
        }
    }
    for lane in 0..ELL {
        out[lane] = gf8_reduce(acc[lane]);
    }
}

// ---------------------------------------------------------------------------
// Convert: per lane, the medium bytes to F192, weighted by eq and summed.
//
//   partial[lane] += eq_lo * sum_b gamma^b * phi_8(byte_b[lane])
//
// The map from the 16 bytes of a lane to F192 is GF(2)-linear.
// ---------------------------------------------------------------------------

/// The per-`x_hi` sums of one worker, one per lane for `A B` and for `C`.
#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
struct Convert {
    ab: [F192; ELL],
    c: [F192; ELL],
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
impl Convert {
    fn new() -> Self {
        Self {
            ab: [F192::ZERO; ELL],
            c: [F192::ZERO; ELL],
        }
    }

    /// Add one `x_outer`'s medium bytes, one 64-lane row per medium position, at weight `eq_lo`.
    #[inline(always)]
    fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
        let convert = convert_table();
        for lane in 0..ELL {
            let mut cf_ab = F192::ZERO;
            let mut cf_c = F192::ZERO;
            for ((row, ab), c) in convert.iter().zip(ab).zip(c) {
                cf_ab += row[ab[lane] as usize];
                cf_c += row[c[lane] as usize];
            }
            self.ab[lane] += cf_ab * eq_lo;
            self.c[lane] += cf_c * eq_lo;
        }
    }

    fn values(&self) -> ([F192; ELL], [F192; ELL]) {
        (self.ab, self.c)
    }
}

/// The per-`x_hi` sums of one worker, byte-sliced: register `o` holds byte `o` of every lane's sum.
///
/// The weight `eq_lo` rides the GFNI matrices, rebuilt for each `x_outer`:
///
/// ```text
///     w[b][s] = (gamma^b * eq_lo) * phi_8(2^s)        phi_8(2^s) lies in the GF(2^64) base field
/// ```
///
/// So an `x_outer` costs 16 products and 16 mixed products, not a product per lane.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
struct Convert {
    ab: [core::arch::x86_64::__m512i; 24],
    c: [core::arch::x86_64::__m512i; 24],
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
impl Convert {
    fn new() -> Self {
        // SAFETY: an all-zero bit pattern is a valid register value.
        unsafe { core::mem::zeroed() }
    }

    /// Add one `x_outer`'s medium bytes, one 64-lane row per medium position, at weight `eq_lo`.
    #[inline(always)]
    fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe { self.accumulate_gfni(ab, c, eq_lo) }
    }

    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    fn accumulate_gfni(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
        use crate::zerocheck::bit_fold::gfni::weight_matrices;
        use core::arch::x86_64::*;
        use primitives::field::{F64, mul_base8, mul4};

        // phi_8 of the unit bytes, as base-field scalars.
        static PHI_UNITS: OnceLock<[F64; 8]> = OnceLock::new();
        let units = PHI_UNITS.get_or_init(|| {
            std::array::from_fn(|s| {
                let phi = PHI_8_TABLE[1 << s];
                assert!(phi.c1 == 0 && phi.c2 == 0, "phi_8 lands in the base field");
                F64(phi.c0)
            })
        });

        // Matrices of medium position b: the weights (gamma^b eq_lo) phi_8(2^s).
        let gamma = gamma_powers();
        let mut matrices = [[0u64; 24]; N_MEDIUM_VALUES];
        for (quad, m) in gamma.as_chunks::<4>().0.iter().zip(matrices.as_chunks_mut::<4>().0) {
            let t = mul4(*quad, [eq_lo; 4]);
            for (t, m) in t.iter().zip(m) {
                *m = weight_matrices(&mul_base8(*t, *units));
            }
        }

        // Eight output bytes at a time keep sixteen accumulators in registers.
        for g in 0..3 {
            let mut acc_ab: [__m512i; 8] = std::array::from_fn(|l| self.ab[8 * g + l]);
            let mut acc_c: [__m512i; 8] = std::array::from_fn(|l| self.c[8 * g + l]);
            for ((ab, c), m) in ab.iter().zip(c).zip(&matrices) {
                // SAFETY: each row is 64 bytes.
                let (xa, xc) = unsafe {
                    (
                        _mm512_loadu_si512(ab.as_ptr().cast()),
                        _mm512_loadu_si512(c.as_ptr().cast()),
                    )
                };
                for l in 0..8 {
                    let a = _mm512_set1_epi64(m[8 * g + l] as i64);
                    acc_ab[l] = _mm512_xor_si512(acc_ab[l], _mm512_gf2p8affine_epi64_epi8::<0>(xa, a));
                    acc_c[l] = _mm512_xor_si512(acc_c[l], _mm512_gf2p8affine_epi64_epi8::<0>(xc, a));
                }
            }
            self.ab[8 * g..8 * g + 8].copy_from_slice(&acc_ab);
            self.c[8 * g..8 * g + 8].copy_from_slice(&acc_c);
        }
    }

    fn values(&self) -> ([F192; ELL], [F192; ELL]) {
        use crate::zerocheck::bit_fold::gfni::store_f192;
        let (mut ab, mut c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe {
            store_f192(&self.ab, &mut ab);
            store_f192(&self.c, &mut c);
        }
        (ab, c)
    }
}

// ---------------------------------------------------------------------------
// Main optimized round-1 prover message.
// ---------------------------------------------------------------------------

/// Per-worker scratch and local accumulators.
struct WorkerState {
    partials: Convert,
    chunk_ab_bytes: [[u8; 64]; 1 << N_MEDIUM],
    chunk_c_bytes: [[u8; 64]; 1 << N_MEDIUM],
    local_res_ab: [F192; ELL],
    local_res_c_s: [F192; ELL],
}

impl WorkerState {
    /// The two accumulators, once every claimed `x_hi` has been folded in.
    fn into_results(self) -> ([F192; ELL], [F192; ELL]) {
        (self.local_res_ab, self.local_res_c_s)
    }

    fn new() -> Self {
        Self {
            partials: Convert::new(),
            chunk_ab_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            chunk_c_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            local_res_ab: [F192::ZERO; ELL],
            local_res_c_s: [F192::ZERO; ELL],
        }
    }
}

/// One `x_outer` step: shift-reduce + bit-transpose the `n_b_med` medium
/// sub-windows, then fold them per lane through the convert table.
///
/// `FULL` specializes the trip count to the constant `1 << N_MEDIUM`, which is
/// the case for every non-boundary window; the unroll depends on it.
#[inline(always)]
fn accumulate_x_outer<const FULL: bool>(
    n_b_med: usize,
    chunk_byte_base: usize,
    eq_lo_val: F192,
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    state: &mut WorkerState,
) {
    let n_b_med = if FULL { 1 << N_MEDIUM } else { n_b_med };

    for b_med in 0..n_b_med {
        shift_reduce_inner_ab(
            a_packed,
            b_packed,
            inv_table,
            chunk_byte_base,
            b_med,
            &mut state.chunk_ab_bytes[b_med],
        );
        let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
        let c_in: &[u8; 64] = (&c_packed[byte_base_b..byte_base_b + 64])
            .try_into()
            .expect("64 c-bytes per medium position");
        bit_transpose_64bytes(c_in, &mut state.chunk_c_bytes[b_med]);
    }

    // Bounded so the trip count is the constant the protocol size gives it.
    let n_b_med = n_b_med.min(N_MEDIUM_VALUES);
    state.partials.accumulate(
        &state.chunk_ab_bytes[..n_b_med],
        &state.chunk_c_bytes[..n_b_med],
        eq_lo_val,
    );
}

/// Process one outer value.
#[inline]
fn process_one_x_hi(
    x_hi: usize,
    big_lo_size: usize,
    n_lo_and_inner: usize,
    within_outer_mask: usize,
    b_med_counts: &[u8],
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    eq_lo_scaled: &[F192],
    eq_hi_val: F192,
    state: &mut WorkerState,
) {
    state.partials = Convert::new();

    let n_lo = n_lo_and_inner - N_INNER;

    for x_outer_lo in 0..big_lo_size {
        let x_outer = x_outer_lo | (x_hi << n_lo);
        let within_hash_outer = x_outer & within_outer_mask;
        let n_b_med = b_med_counts[within_hash_outer] as usize;
        if n_b_med == 0 {
            continue;
        }

        let chunk_byte_base = ((x_outer_lo << N_INNER) | (x_hi << n_lo_and_inner)) * N_CHUNKS;
        let eq_lo_val = eq_lo_scaled[x_outer_lo];

        if n_b_med == (1 << N_MEDIUM) {
            accumulate_x_outer::<true>(
                n_b_med,
                chunk_byte_base,
                eq_lo_val,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                state,
            );
        } else {
            accumulate_x_outer::<false>(
                n_b_med,
                chunk_byte_base,
                eq_lo_val,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                state,
            );
        }
    }

    // Outer fold by eq_hi.
    let (partial_ab, partial_c) = state.partials.values();
    for lane in 0..ELL {
        state.local_res_ab[lane] += eq_hi_val * partial_ab[lane];
        state.local_res_c_s[lane] += eq_hi_val * partial_c[lane];
    }
}

/// Build the `b_med_counts` table from a [`PaddingSpec`] for use by
/// [`process_one_x_hi`].
///
/// Returns `(within_outer_mask, b_med_counts)`:
///   - `within_outer_mask` masks `x_outer` to the bits identifying the
///     within-block window.
///   - `b_med_counts[w]` is how many of the 16 b_med 512-bit sub-windows of
///     window `w` we should process. Entries past the useful prefix are 0
///     (full skip): kernels just `continue` past those x_outer_lo iterations.
fn build_b_med_counts(padding: &PaddingSpec) -> (usize, Vec<u8>) {
    const STRIDE: usize = 1 << (K_SKIP + N_INNER); // 8192 bits per within-window
    const B_MED_WINDOW: usize = 1 << (K_SKIP + 3); // 512 bits per b_med
    const N_B_MED_MAX: usize = 1 << N_MEDIUM;

    // For k_log < K_SKIP + N_INNER (= 13) the within-window granularity is
    // coarser than the block itself: skipping at this granularity would be
    // incorrect, so we fall back to "no skip". All hash modules use
    // k_log ∈ {14, 15, 16}.
    if padding.k_log < K_SKIP + N_INNER {
        return (0, vec![N_B_MED_MAX as u8]);
    }
    let within_outer_bits = padding.k_log - K_SKIP - N_INNER;
    let within_outer_count = 1usize << within_outer_bits;
    let within_outer_mask = within_outer_count - 1;
    let useful = padding.useful_bits_per_block;
    let counts: Vec<u8> = (0..within_outer_count)
        .map(|w| {
            let block_start = w * STRIDE;
            if block_start >= useful {
                0u8
            } else {
                let bits_left = useful - block_start;
                let processed = bits_left.div_ceil(B_MED_WINDOW);
                processed.min(N_B_MED_MAX) as u8
            }
        })
        .collect();
    (within_outer_mask, counts)
}

/// The round-1 prover message, padding-aware: the AB and C Λ-vectors, which the
/// caller sends as one sum.
///
/// Skips 512-bit b_med sub-windows that fall entirely in the zero padding of
/// every witness block per `padding`, which is byte-identical to the dense
/// path when those bits are honestly zero.
pub fn round1_shift_reduce_extract_c_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
    padding: &PaddingSpec,
) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(k_skip, K_SKIP, "optimized variant is k_skip=6 only");
    assert!(
        m >= k_skip + N_INNER,
        "m must be ≥ k_skip + N_INNER ({}) for the shift_reduce optimization",
        k_skip + N_INNER
    );
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r_rest.len(), m - k_skip);
    assert_eq!(inv_table.k, k_skip);

    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let big_lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    let n_lo_and_inner = eq.n_lo + N_INNER;

    let d_inv_val = d_inv();
    let eq_lo_scaled: Vec<F192> = eq.lo.iter().map(|v| *v * d_inv_val).collect();
    let eq_hi = &eq.hi;

    let (within_outer_mask, b_med_counts) = build_b_med_counts(padding);

    // One `WorkerState` per worker (it carries multi-KB scratch), folded over the
    // `x_hi` values that worker claims and combined at the end.
    let (res_ab, res_c_s) = parallel::fold_reduce(
        hi_size,
        WorkerState::new,
        |state, x_hi| {
            let eq_hi_val = eq_hi[x_hi];
            process_one_x_hi(
                x_hi,
                big_lo_size,
                n_lo_and_inner,
                within_outer_mask,
                &b_med_counts,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                &eq_lo_scaled,
                eq_hi_val,
                state,
            );
        },
        |mut a, b| {
            for i in 0..ELL {
                a.local_res_ab[i] += b.local_res_ab[i];
                a.local_res_c_s[i] += b.local_res_c_s[i];
            }
            a
        },
    )
    .into_results();

    let res_c_lifted = ntt_extend_vec(&res_c_s, inv_table);
    (res_ab.to_vec(), res_c_lifted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zerocheck::univariate_skip::round1_naive;
    use pcs::ntt::AdditiveNttGf8;
    use primitives::test_rng::Rng;

    /// The convert stage against the table definition, over full and boundary windows.
    #[test]
    fn convert_matches_table() {
        let mut rng = Rng::new(0xC0_4E27);
        let mut partials = Convert::new();
        let (mut want_ab, mut want_c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
        // Two full windows of 16 medium positions, then a boundary window of 7.
        for n in [16, 16, 7] {
            let ab: Vec<[u8; 64]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64() as u8)).collect();
            let c: Vec<[u8; 64]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64() as u8)).collect();
            let eq = rng.ext();
            partials.accumulate(&ab, &c, eq);
            for lane in 0..ELL {
                let conv = |rows: &[[u8; 64]]| {
                    rows.iter()
                        .zip(convert_table())
                        .fold(F192::ZERO, |acc, (r, t)| acc + t[r[lane] as usize])
                };
                want_ab[lane] += conv(&ab) * eq;
                want_c[lane] += conv(&c) * eq;
            }
        }
        assert_eq!(partials.values(), (want_ab, want_c));
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "gfni"))]
    #[test]
    fn gfni_inner_matches_scalar_inner() {
        let mut seed = 0xDEADBEEFu64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u8
        };
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
        let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);

        // One medium-position worth of packed bytes: 8 K-rows × N_CHUNKS.
        let n_bytes = 8 * N_CHUNKS;
        for _ in 0..16 {
            let a_packed: Vec<u8> = (0..n_bytes).map(|_| next()).collect();
            let b_packed: Vec<u8> = (0..n_bytes).map(|_| next()).collect();

            let mut out_scalar = [0u8; 64];
            shift_reduce_inner_ab_scalar(&a_packed, &b_packed, &inv_table, 0, 0, &mut out_scalar);
            let mut out_gfni = [0u8; 64];
            shift_reduce_inner_ab(&a_packed, &b_packed, &inv_table, 0, 0, &mut out_gfni);
            assert_eq!(out_scalar, out_gfni);
        }
    }

    /// **Soundness assumption.** Zerocheck and the WHIR PCS opening at L0 both
    /// depend on the seven "friendly" constants `a`, three small
    /// (`φ_8(SMALL_CHAL_F8[k])`, k ∈ 0..3) and four medium
    /// (`γ^{2^i}/(1+γ^{2^i})`, i ∈ 0..4), satisfying the hypothesis of
    /// `lem:fixed-zerocheck` (doc/leanvm/body/03-proving-primitives.tex): the
    /// `2^7` equality WEIGHTS `{eq(a, b) : b ∈ {0,1}^7}` are **F₂-linearly
    /// independent** in F₁₉₂, i.e. they have rank 128.
    ///
    /// That is what the proof consumes, and it is strictly stronger than
    /// independence of the seven `a_i` themselves: a single relation among their
    /// products (say `a_1 a_2 = a_3`) drops the weight rank below 128 while
    /// leaving the coordinates independent. Asserting only rank 7 of the `a_i`
    /// would pass while the lemma's hypothesis failed.
    ///
    /// Zerocheck needs it so that the prover's URM message cannot be trivially
    /// canceled by a malicious witness aligned with the friendly subspace. WHIR's
    /// L0 list-collapse argument (which leans on the zerocheck `(r, v)` claim as
    /// an OOD-equivalent) needs it too: without it the SZ bound `(m-7)/|F|` for
    /// collisions between distinct candidate codewords' MLEs at `r` no longer
    /// holds, and a cheating prover could engineer a witness so two candidates'
    /// MLEs agree at the friendly point with probability 1.
    #[test]
    fn friendly_challenges_f2_independent() {
        let a: Vec<F192> = small_challenges()
            .iter()
            .chain(medium_challenges().iter())
            .copied()
            .collect();
        assert_eq!(a.len(), N_INNER, "expected 3 small + 4 medium friendly values");

        // One row per b: eq(a, b) = prod_i (b_i ? a_i : 1 + a_i).
        let mut rows: Vec<[u64; 3]> = (0..1usize << N_INNER)
            .map(|b| {
                let w = a.iter().enumerate().fold(F192::ONE, |acc, (i, &ai)| {
                    acc * if (b >> i) & 1 == 1 { ai } else { F192::ONE + ai }
                });
                [w.c0, w.c1, w.c2]
            })
            .collect();

        // Row-reduce over F₂: per column from MSB down, find a pivot row, swap it
        // into place, and XOR it into every other row with that bit set.
        let mut rank = 0usize;
        for col in (0..192).rev() {
            let (limb, mask) = (col / 64, 1u64 << (col % 64));
            if let Some(p) = (rank..rows.len()).find(|&i| rows[i][limb] & mask != 0) {
                rows.swap(rank, p);
                for i in 0..rows.len() {
                    if i != rank && rows[i][limb] & mask != 0 {
                        for l in 0..3 {
                            rows[i][l] ^= rows[rank][l];
                        }
                    }
                }
                rank += 1;
            }
        }
        assert_eq!(
            rank,
            1 << N_INNER,
            "the 2^7 friendly equality weights must be F₂-linearly independent in F₁₉₂; \
             zerocheck and WHIR L0 soundness depend on it (lem:fixed-zerocheck)"
        );
    }

    /// Build the equality tail with protocol-fixed constants followed by the
    /// outer randomness used by the optimized URM.
    fn build_protocol_r_rest(m: usize, outer: &[F192]) -> Vec<F192> {
        assert_eq!(outer.len(), m - K_SKIP - N_INNER);
        small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain(outer.iter().copied())
            .collect()
    }

    fn make_inv_table() -> InvNttTableByteSingleGf8 {
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
        InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l)
    }

    /// **The defining cross-check**: `C_s · (opt_AB + opt_C) == naive_AB + naive_C`,
    /// element-wise on Λ. Verifies all three optimization layers compose
    /// correctly: geometric small eq, geometric medium eq, and the D⁻¹
    /// pre-scaling.
    #[test]
    fn matches_naive_with_c_s_factor() {
        let c_s = c_s();
        for &m in &[13usize, 14, 15] {
            let mut rng = Rng::new(100 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c = rng.bits(1 << m);
            let outer = rng.ext_vec(m - K_SKIP - N_INNER);
            let r = build_protocol_r_rest(m, &outer);
            let table = make_inv_table();

            let (naive_ab, naive_c) = round1_naive(&a, &b, &c, m, K_SKIP, &r);
            let (opt_ab, opt_c) = round1_shift_reduce_extract_c_packed_padded(
                &pack_bits(&a),
                &pack_bits(&b),
                &pack_bits(&c),
                m,
                K_SKIP,
                &r,
                &table,
                &PaddingSpec::dense(m),
            );

            // Combined: C_s · (opt_AB + opt_C) == naive_AB + naive_C
            for i in 0..ELL {
                let lhs = naive_ab[i] + naive_c[i];
                let rhs = c_s * (opt_ab[i] + opt_c[i]);
                assert_eq!(
                    lhs, rhs,
                    "combined mismatch at m={m}, i={i}:\n  naive={lhs:?}\n  C_s·opt={rhs:?}"
                );
            }

            // Stronger: the AB and C pieces match independently (the AB-only
            // shift_reduce and the C bit_transpose both drop the same C_s).
            for i in 0..ELL {
                assert_eq!(naive_ab[i], c_s * opt_ab[i], "AB mismatch at i={i}");
                assert_eq!(naive_c[i], c_s * opt_c[i], "C mismatch at i={i}");
            }
        }
    }

    /// **Padding skip is byte-identical to the dense path.** On a witness
    /// where bits `[useful_bits, 2^k_log)` of every block are honestly zero,
    /// the padded URM must produce the exact same `(round1_ab, round1_c)`
    /// vectors as the dense URM: every chunk we skip would have contributed
    /// a literal zero to the dense sum (the convert table maps φ_8(0) = 0).
    ///
    /// Covers the supported hash padding shapes, including a fully skipped chunk.
    #[test]
    fn padded_matches_dense_with_zero_padding() {
        use crate::zerocheck::PaddingSpec;
        use crate::zerocheck::univariate_skip::pack_bits;

        // (k_log, useful_bits, n_blocks_log): pick n_blocks_log so
        // m = k_log + n_blocks_log is small enough to keep the test fast
        // while still exercising the kernel's parallel + boundary paths.
        let cases = [
            (14usize, 16_000usize, 0usize), // BLAKE2s, m=14
            (15, 31_401, 0),                // SHA-2,  m=15
            (16, 42_560, 0),                // Keccak, m=16
            (16, 42_560, 3),                // Keccak, m=19 (multiple hashes)
        ];

        for (k_log, useful_bits, n_blocks_log) in cases {
            let m = k_log + n_blocks_log;
            assert!(m >= K_SKIP + N_INNER);

            let mut rng = Rng::new(0xBEEF_DEAD_u64.wrapping_add((k_log * 31 + m) as u64));
            let n_blocks = 1usize << n_blocks_log;
            let total_bits = 1usize << m;
            let block_size = 1usize << k_log;

            // Random witness, but force bits [useful_bits, 2^k_log) of every
            // block to zero (mirrors the hash-module witness layout).
            let mut a = rng.bits(total_bits);
            let mut b = rng.bits(total_bits);
            let mut c = rng.bits(total_bits);
            for blk in 0..n_blocks {
                for j in useful_bits..block_size {
                    let idx = blk * block_size + j;
                    a[idx] = false;
                    b[idx] = false;
                    c[idx] = false;
                }
            }

            let outer = rng.ext_vec(m - K_SKIP - N_INNER);
            let r = build_protocol_r_rest(m, &outer);
            let table = make_inv_table();
            let a_p = pack_bits(&a);
            let b_p = pack_bits(&b);
            let c_p = pack_bits(&c);

            let dense = PaddingSpec::dense(m);
            let (dense_ab, dense_c) =
                round1_shift_reduce_extract_c_packed_padded(&a_p, &b_p, &c_p, m, K_SKIP, &r, &table, &dense);
            let padding = PaddingSpec {
                k_log,
                useful_bits_per_block: useful_bits,
            };
            let (padded_ab, padded_c) =
                round1_shift_reduce_extract_c_packed_padded(&a_p, &b_p, &c_p, m, K_SKIP, &r, &table, &padding);

            assert_eq!(
                dense_ab, padded_ab,
                "AB mismatch: k_log={k_log}, useful={useful_bits}, m={m}"
            );
            assert_eq!(
                dense_c, padded_c,
                "C mismatch: k_log={k_log}, useful={useful_bits}, m={m}"
            );
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_fused_inner_matches_scalar_inner() {
        // The new register-fused NEON kernel: verify against the same scalar
        // oracle as the intermediate one.
        let mut rng = Rng::new(0xF050D);
        let m = 14;
        let table = make_inv_table();
        let a_bits = rng.bits(1 << m);
        let b_bits = rng.bits(1 << m);
        let a_packed = super::super::univariate_skip::pack_bits(&a_bits);
        let b_packed = super::super::univariate_skip::pack_bits(&b_bits);

        for &(chunk_byte_base, b_med) in &[(0usize, 0usize), (64, 5), (1024, 7), (4096, 15)] {
            let needed = chunk_byte_base + b_med * N_CHUNKS * 8 + 8 * N_CHUNKS;
            if needed > a_packed.len() {
                continue;
            }
            let mut out_scalar = [0u8; 64];
            let mut out_fused = [0u8; 64];
            shift_reduce_inner_ab_scalar(&a_packed, &b_packed, &table, chunk_byte_base, b_med, &mut out_scalar);
            shift_reduce_inner_ab_fused_neon(&a_packed, &b_packed, &table, chunk_byte_base, b_med, &mut out_fused);
            assert_eq!(
                out_scalar, out_fused,
                "fused-neon disagrees with scalar at (base={chunk_byte_base}, b_med={b_med})"
            );
        }
    }
}
