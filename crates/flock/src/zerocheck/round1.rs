// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The zerocheck's round-1 prover message, the univariate skip.
//!
//! The round-1 message is `(P^{AB}, P^C)`, each a length-`2^k_skip` vector
//! of F192 values. They are evaluations on the NTT domain `Λ` of the
//! polynomial (over λ) defined by
//!
//!   P^{AB}(λ) = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(â(λ, x) · b̂(λ, x))
//!   P^C(λ)   = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(ĉ(λ, x))
//!
//! where â(λ, x), b̂(λ, x), ĉ(λ, x) ∈ F₂⁸ are the values at λ of the
//! univariate polynomial whose evaluations on `S = {0,…,2^k_skip − 1}` are
//! the boolean witness values `a(s, x), b(s, x), c(s, x)`. The polynomial is
//! recovered via `inv_NTT_S`; we then evaluate on `Λ = {2^k_skip, …}` via
//! `fwd_NTT_Λ`.
//!
//! The naive oracle keeps the constant F₈ factor `C_s = φ₈(0x1C)` in the eq-on-S weights;
//! the optimized sweep below drops it and the caller restores it before the message
//! goes on the wire.
//!
//! The sweep is fully optimized (shift_reduce + extract_c).
//! Scalar Rust, with NEON, AVX2 and GFNI kernels for the inner sweep.
//! Three layered optimizations:
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
//! The sweep is fixed at `K_SKIP = 6` (ell=64, n_chunks=8, N_INNER=7).

use super::{K_SKIP, N_INNER, PaddingSpec};
use crate::zerocheck::ntt::InvNttTableByteSingleGf8;
#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use primitives::bit_fold::avx2;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use primitives::bit_fold::gfni::{store_f192, weight_matrices};
use primitives::bits::bit_transpose_64bytes;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "gfni")))]
use primitives::field::gf2_8::avx2::gf8_mul_vec32;
use primitives::field::gf2_8::gf8_reduce;
#[cfg(target_arch = "aarch64")]
use primitives::field::gf2_8::neon::{gf8_mul_vec16, gf8_reduce_vec16};
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use primitives::field::mul4;
use primitives::field::{F8, F192, PHI_8_TABLE_192, phi8_192};
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use primitives::field::{F64, mul_base8};
use primitives::multilinear::SplitEq;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
))]
use std::sync::LazyLock;
use std::sync::OnceLock;

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

/// `C_s` as an F_8 value, pinned by the cross-check against the naive round.
const C_S_F8: u8 = 0x1C;

/// The constant `C_s = φ_8(0x1C) ∈ F_{2^192}`: the relative scaling factor
/// between this optimized output and the naive output.
pub(crate) fn c_s() -> F192 {
    phi8_192(F8(C_S_F8))
}

/// The three F192 small challenges (embeddings of `SMALL_CHAL_F8`): caller
/// must place these at `r_rest[..3]` for the naive cross-check to
/// produce a result related to the optimized output by exactly `C_s`.
pub(crate) fn small_challenges() -> [F192; 3] {
    [
        phi8_192(F8(SMALL_CHAL_F8[0])),
        phi8_192(F8(SMALL_CHAL_F8[1])),
        phi8_192(F8(SMALL_CHAL_F8[2])),
    ]
}

/// The four F192 medium challenges `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`.
/// Caller must place these at `r_rest[3..7]` for the naive
/// cross-check.
pub(crate) fn medium_challenges() -> [F192; 4] {
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

/// Most high variables of a split eq table capped on its high side: few high weights keep the outer products cheap.
pub(crate) const EQ_HIGH_VARS: usize = 7;

/// Extend a length-`ell` F192 vector from the input domain S to the extension
/// domain Λ using bit-plane decomposition: for each of the 192 bit positions
/// of F192, run the bit-input NTT (`inv_NTT_S` then `fwd_NTT_Λ` via the
/// precomputed table) on that bit-plane, scale by γ^b, and accumulate.
///
/// Ports `ntt_extend_vec` (scalar form). The NTT is F_2-linear and
/// φ_8 commutes with that linearity, which is what makes the bit-by-bit
/// decomposition equal to the direct F_8-valued NTT extension.
pub(crate) fn ntt_extend_vec(in_s: &[F192], inv_table: &InvNttTableByteSingleGf8) -> Vec<F192> {
    let ell = inv_table.ell;
    assert_eq!(in_s.len(), ell);
    assert_eq!(ell, 1usize << inv_table.k);

    let mut out = vec![F192::ZERO; ell];
    let n_chunks = inv_table.n_chunks;

    let mut input_bits = vec![0u8; n_chunks];
    let mut out_bytes = vec![F8::ZERO; ell];

    for b in 0..192 {
        // Pack bit b of each in_s[z] into z-indexed LSB-first byte form.
        input_bits.iter_mut().for_each(|x| *x = 0);
        for z in 0..ell {
            let bit = match b / 64 {
                0 => (in_s[z].c0 >> b) & 1,
                1 => (in_s[z].c1 >> (b - 64)) & 1,
                2 => (in_s[z].c2 >> (b - 128)) & 1,
                _ => unreachable!(),
            };
            if bit != 0 {
                input_bits[z / 8] |= 1u8 << (z % 8);
            }
        }

        // Bit-input NTT.
        inv_table.apply(&input_bits, &mut out_bytes);

        let basis = match b / 64 {
            0 => F192::new(1u64 << b, 0, 0),
            1 => F192::new(0, 1u64 << (b - 64), 0),
            2 => F192::new(0, 0, 1u64 << (b - 128)),
            _ => unreachable!(),
        };
        for lambda in 0..ell {
            out[lambda] += basis * phi8_192(out_bytes[lambda]);
        }
    }

    out
}

// Convert table: γ^b · φ_8(v) for b ∈ [0, 16), v ∈ [0, 256).
// Computed once and cached.

const N_MEDIUM_VALUES: usize = 16;

/// The convert table as its shape rather than as a flat run: a `u8` cannot index
/// a 256-entry row out of bounds and the row index is bounded by the loop, so
/// the fold's two lookups carry no bounds check and the row stride folds into
/// the address. Flat, each lookup costs a check, a branch and a multiply by the
/// 24-byte element stride, and the branches keep the constant-trip loop around
/// them from unrolling.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
type ConvertTable = [[F192; 256]; N_MEDIUM_VALUES];

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
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

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn build_convert_table() -> Box<ConvertTable> {
    let _table = tracing::info_span!("Round1 convert table setup", table_bytes = core::mem::size_of::<ConvertTable>()).entered();
    let mut table: Box<ConvertTable> = Box::new([[F192::ZERO; 256]; N_MEDIUM_VALUES]);
    for (row, &g_b) in table.iter_mut().zip(gamma_powers()) {
        for (entry, &phi) in row.iter_mut().zip(PHI_8_TABLE_192.iter()) {
            *entry = g_b * phi;
        }
    }
    table
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn convert_table() -> &'static ConvertTable {
    CONVERT_TABLE_CACHE.get_or_init(build_convert_table)
}

// Shift_reduce inner kernel (AB only: extract_c handles C separately).
//
// For one medium-position b_med and the 8 small-positions K ∈ 0..8:
//   1. Look up NTT-extended A,B at chunk `chunk_byte_base + (b_med*8 + K)*8`.
//   2. y_K[lane] = ntt_a[lane] · ntt_b[lane]  (in F_8).
//   3. acc[lane] ^= (y_K[lane] as u16) << K   (no reduction yet).
// At the end, reduce each acc[lane] back to a u8 in F_8.
//
// Output `out[lane]` is the F_8 representative of Σ_K x^K · y_K[lane] mod p.

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

/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `BH < 4`.
#[cfg(target_arch = "aarch64")]
// `0 ^ BH` is the i = 0 case of the `i ^ BH` row-select pattern below; spelling
// it out keeps the four loads visibly parallel.
#[allow(clippy::identity_op)]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
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
    // SAFETY: NEON is part of the aarch64 baseline; `table_base` is the caller's `256 * 64`-byte table, so row
    // `byte * 64` plus a chunk offset `(i ^ BH) * 16 < 64` (`BH < 4`) stays inside it.
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
///
/// # Safety
/// `table_base` points to a `256 * 64`-byte table, and `a_row` and `b_row` to `N_CHUNKS` readable bytes each.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "Separate NEON accumulators preserve the register layout of the fused kernel."
)]
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
    // SAFETY: NEON is part of the aarch64 baseline; the caller guarantees `N_CHUNKS` readable bytes at `a_row` and
    // `b_row` and a `256 * 64`-byte table, and every load is a table row plus an offset below 64.
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
#[cfg_attr(leanvm_round1_neon_tiled, allow(dead_code))]
#[inline(always)]
fn shift_reduce_inner_ab_fused_neon(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    let table_base = inv_table.data_ptr();

    // SAFETY: NEON is part of the aarch64 baseline. The table is `256 * 64` bytes, its `k` being `K_SKIP` (asserted
    // at the entry point). The row windows `byte_base_b + K * N_CHUNKS .. + N_CHUNKS` for `K < 8` lie in both packed
    // tables, whose lengths the entry point asserts against the windows it walks. `out` is 64 bytes.
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

// Temporary quarter-first schedule experiment. The table and arithmetic are
// identical to the baseline; only the order of independent lane work changes.
#[cfg(all(target_arch = "aarch64", leanvm_round1_neon_tiled))]
#[inline(always)]
fn shift_reduce_inner_ab_tiled_neon(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    let table_base = inv_table.data_ptr();
    // SAFETY: the production entry point checks the same table and witness
    // lengths as the baseline fused kernel. Quarter < 4 and b < 8 keep every
    // permuted load within its 64-byte table row; stores cover exactly out.
    unsafe {
        for quarter in 0..4 {
            let mut acc_lo = vdupq_n_u16(0);
            let mut acc_hi = vdupq_n_u16(0);
            macro_rules! step {
                ($k:literal) => {{
                    let off = byte_base_b + $k * N_CHUNKS;
                    let row = |input: &[u8], b: usize| {
                        let index = *input.as_ptr().add(off + b) as usize;
                        vld1q_u8(table_base.add(index * ELL + (quarter ^ (b >> 1)) * 16))
                    };
                    let apply = |input: &[u8]| {
                        let mut value = row(input, 1);
                        value = veorq_u8(value, row(input, 3));
                        value = veorq_u8(value, row(input, 5));
                        value = veorq_u8(value, row(input, 7));
                        value = vextq_u8::<8>(value, value);
                        value = veorq_u8(value, row(input, 0));
                        value = veorq_u8(value, row(input, 2));
                        value = veorq_u8(value, row(input, 4));
                        veorq_u8(value, row(input, 6))
                    };
                    let y = gf8_mul_vec16(apply(a_packed), apply(b_packed));
                    acc_lo = veorq_u16(acc_lo, vshll_n_u8::<$k>(vget_low_u8(y)));
                    acc_hi = veorq_u16(acc_hi, vshll_n_u8::<$k>(vget_high_u8(y)));
                }};
            }
            step!(0); step!(1); step!(2); step!(3);
            step!(4); step!(5); step!(6); step!(7);
            let reduced = gf8_reduce_vec16(vreinterpretq_u8_u16(acc_lo), vreinterpretq_u8_u16(acc_hi));
            vst1q_u8(out.as_mut_ptr().add(quarter * 16), reduced);
        }
    }
}

/// Dispatch helper: picks the widest SIMD kernel this target has, otherwise scalar.
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
        #[cfg(leanvm_round1_neon_tiled)]
        shift_reduce_inner_ab_tiled_neon(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out);
        #[cfg(not(leanvm_round1_neon_tiled))]
        shift_reduce_inner_ab_fused_neon(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out);
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
    {
        // SAFETY: gfni and avx512bw are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_gfni_512(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out) };
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(target_feature = "gfni", target_feature = "avx512bw"))
    ))]
    {
        // SAFETY: avx2, and gfni where the kernel uses it, are statically enabled at compile time.
        unsafe { shift_reduce_inner_ab_avx2(a_packed, b_packed, inv_table, chunk_byte_base, b_med, out) };
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2"))))]
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
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    let chunk = |k: usize| byte_base_b + k * N_CHUNKS..byte_base_b + (k + 1) * N_CHUNKS;

    // SAFETY: the target features are carried by the function; the store covers exactly `out`.
    unsafe {
        let (mut acc_lo, mut acc_hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
        let zero = _mm512_setzero_si512();

        for k in 0..8 {
            let y = _mm512_gf2p8mul_epi8(
                inv_table.apply_zmm(a_packed[chunk(k)].try_into().expect("one chunk")),
                inv_table.apply_zmm(b_packed[chunk(k)].try_into().expect("one chunk")),
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

/// The 512-bit kernel two registers wide. With GFNI the products are
/// `gf2p8mulb`; without it, the shift-and-add of `gf2_8::avx2::gf8_mul_vec32`.
///
/// # Safety
/// Requires the `avx2` target feature, and `gfni` where the target has it.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(all(target_feature = "gfni", target_feature = "avx512bw"), allow(dead_code))]
#[target_feature(enable = "avx2")]
unsafe fn shift_reduce_inner_ab_avx2(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    // `inv_table.apply` overwrites every lane, so these need no re-zeroing per K.
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];

    // SAFETY: the target features are carried by the function or enabled at
    // compile time; the loads and stores stay within a_col/b_col/out, each
    // exactly `ELL` bytes.
    unsafe {
        let mut acc = [[_mm256_setzero_si256(); 2]; 2];
        let zero = _mm256_setzero_si256();

        for k in 0..8 {
            let chunk_off = byte_base_b + k * N_CHUNKS;
            inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], &mut a_col);
            inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], &mut b_col);
            let shift = _mm_cvtsi32_si128(k as i32);
            for (h, [lo, hi]) in acc.iter_mut().enumerate() {
                let a = _mm256_loadu_si256(a_col.as_ptr().add(32 * h).cast());
                let b = _mm256_loadu_si256(b_col.as_ptr().add(32 * h).cast());
                #[cfg(target_feature = "gfni")]
                let y = _mm256_gf2p8mul_epi8(a, b);
                #[cfg(not(target_feature = "gfni"))]
                let y = gf8_mul_vec32(a, b);
                *lo = _mm256_xor_si256(*lo, _mm256_sll_epi16(_mm256_unpacklo_epi8(y, zero), shift));
                *hi = _mm256_xor_si256(*hi, _mm256_sll_epi16(_mm256_unpackhi_epi8(y, zero), shift));
            }
        }

        // Vectorized gf8_reduce over u16 lanes: two-step fold of the high byte
        // h with h ^ (h<<1) ^ (h<<3) ^ (h<<4)  (x^8 = x^4+x^3+x+1).
        let mask_ff = _mm256_set1_epi16(0xff);
        let fold = |p: __m256i| -> __m256i {
            let h = _mm256_srli_epi16::<8>(p);
            _mm256_xor_si256(
                _mm256_and_si256(p, mask_ff),
                _mm256_xor_si256(
                    _mm256_xor_si256(h, _mm256_slli_epi16::<1>(h)),
                    _mm256_xor_si256(_mm256_slli_epi16::<3>(h), _mm256_slli_epi16::<4>(h)),
                ),
            )
        };
        // Two folds bring 15-bit accumulators down to 8 bits; the second fold's
        // high byte is at most 0x0f, so lanes stay below 256 for `packus`.
        let reduce = |p: __m256i| _mm256_and_si256(fold(fold(p)), mask_ff);
        for (h, [lo, hi]) in acc.into_iter().enumerate() {
            _mm256_storeu_si256(
                out.as_mut_ptr().add(32 * h).cast(),
                _mm256_packus_epi16(reduce(lo), reduce(hi)),
            );
        }
    }
}

/// Kept under `#[allow(dead_code)]` because the dispatcher only reaches it when
/// neither NEON nor AVX2 is available, which is not any platform we build
/// on today. It stays as that fallback AND as the cross-check oracle for
/// `neon_fused_inner_matches_scalar_inner` / `x86_inner_matches_scalar_inner`.
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

// Convert: per lane, the medium bytes to F192, weighted by eq and summed.
//
//   partial[lane] += eq_lo * sum_b gamma^b * phi_8(byte_b[lane])
//
// The map from the 16 bytes of a lane to F192 is GF(2)-linear.

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
    const fn new() -> Self {
        Self {
            ab: [F192::ZERO; ELL],
            c: [F192::ZERO; ELL],
        }
    }

    /// Add one `x_outer`'s medium bytes, one 64-lane row per medium position, at weight `eq_lo`.
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
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

    /// Add one `x_outer`'s medium bytes, one 64-lane row per medium position, at weight `eq_lo`.
    ///
    /// The rows convert byte-sliced against fixed maps, then each lane takes its product by `eq_lo`.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[inline(always)]
    fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
        static MAPS: LazyLock<ConvertMaps<avx2::Best>> = LazyLock::new(convert_maps::<avx2::Best>);
        let maps = &*MAPS;
        for (acc, rows) in [(&mut self.ab, ab), (&mut self.c, c)] {
            // SAFETY: the function is compiled only with AVX2 enabled.
            let cf = unsafe { convert_avx2::<avx2::Best>(rows, maps) };
            for (acc, cf) in acc.as_chunks_mut::<4>().0.iter_mut().zip(cf.as_chunks::<4>().0) {
                for (acc, p) in acc.iter_mut().zip(mul4(*cf, [eq_lo; 4])) {
                    *acc += p;
                }
            }
        }
    }

    const fn values(&self) -> ([F192; ELL], [F192; ELL]) {
        (self.ab, self.c)
    }
}

/// The maps of each medium position `b`: the weights `gamma^b * phi_8(2^s)`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
type ConvertMaps<P> = [[<P as avx2::Product>::Map; avx2::OUT_BYTES]; N_MEDIUM_VALUES];

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
fn convert_maps<P: avx2::Product>() -> ConvertMaps<P> {
    let units: [F192; 8] = std::array::from_fn(|s| PHI_8_TABLE_192[1 << s]);
    gamma_powers().map(|g| P::maps(&units.map(|u| g * u)))
}

/// `sum_b gamma^b * phi_8(rows[b][lane])` for every lane, byte-sliced.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
#[target_feature(enable = "avx2")]
fn convert_avx2<P: avx2::Product>(rows: &[[u8; 64]], maps: &ConvertMaps<P>) -> [F192; ELL] {
    let mut out = [F192::ZERO; ELL];
    for (h, out) in out.as_chunks_mut::<{ avx2::HALF }>().0.iter_mut().enumerate() {
        let mut acc = [_mm256_setzero_si256(); avx2::OUT_BYTES];
        // Eight output bytes at a time keep their accumulators in registers.
        for (o, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            for (row, m) in rows.iter().zip(maps) {
                // SAFETY: each half-row is 32 bytes.
                let x = unsafe { _mm256_loadu_si256(row[avx2::HALF * h..].as_ptr().cast()) };
                avx2::accumulate8::<P>(acc, P::input(x), &m[8 * o..]);
            }
        }
        avx2::store_f192(&acc, out);
    }
    out
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
    const fn new() -> Self {
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
        // phi_8 of the unit bytes, as base-field scalars.
        static PHI_UNITS: OnceLock<[F64; 8]> = OnceLock::new();
        let units = PHI_UNITS.get_or_init(|| {
            std::array::from_fn(|s| {
                let phi = PHI_8_TABLE_192[1 << s];
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
        let (mut ab, mut c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
        // SAFETY: the module is compiled only with these target features enabled.
        unsafe {
            store_f192(&self.ab, &mut ab);
            store_f192(&self.c, &mut c);
        }
        (ab, c)
    }
}

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
    const fn into_results(self) -> ([F192; ELL], [F192; ELL]) {
        (self.local_res_ab, self.local_res_c_s)
    }

    const fn new() -> Self {
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
#[expect(
    clippy::too_many_arguments,
    reason = "The proof kernel keeps its independent inputs explicit."
)]
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

/// Process one outer value, up to `n_windows` windows of the cube.
#[inline]
#[expect(
    clippy::too_many_arguments,
    reason = "The proof kernel keeps its independent inputs explicit."
)]
fn process_one_x_hi(
    x_hi: usize,
    big_lo_size: usize,
    n_windows: usize,
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
    let lo_len = big_lo_size.min(n_windows - x_hi * big_lo_size);

    for (x_outer_lo, &eq_lo_val) in eq_lo_scaled.iter().enumerate().take(lo_len) {
        let x_outer = x_outer_lo | (x_hi << n_lo);
        let within_hash_outer = x_outer & within_outer_mask;
        let n_b_med = b_med_counts[within_hash_outer] as usize;
        if n_b_med == 0 {
            continue;
        }

        let chunk_byte_base = ((x_outer_lo << N_INNER) | (x_hi << n_lo_and_inner)) * N_CHUNKS;

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
/// path when those bits are honestly zero. The identical tail of blocks is
/// summed once, its last group weighted by the tail's eq mass.
pub(crate) fn round1_shift_reduce_extract_c_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
    padding: &PaddingSpec,
) -> (Vec<F192>, Vec<F192>) {
    // The bits of one `x_outer` window, the smallest cube.
    const WINDOW_LOG: usize = K_SKIP + N_INNER;
    assert!(
        m >= K_SKIP + N_INNER,
        "m must be ≥ K_SKIP + N_INNER ({}) for the shift_reduce optimization",
        K_SKIP + N_INNER
    );
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r_rest.len(), m - K_SKIP);
    assert_eq!(inv_table.k, K_SKIP);

    let _cube = tracing::info_span!(
        "Round1 cube",
        m,
        k_log = padding.k_log,
        useful_bits = padding.useful_bits_per_block,
        live_blocks = padding.live_blocks,
        cube_bytes = total_bytes,
    )
    .entered();
    let eq_span = tracing::info_span!("Round1 eq and shape").entered();
    let tail = padding.tail(m, WINDOW_LOG, WINDOW_LOG, r_rest);
    let n_windows = tail.map_or(1 << (m - WINDOW_LOG), |t| t.head >> WINDOW_LOG);

    let eq = SplitEq::with_high_vars(&r_rest[N_INNER..], EQ_HIGH_VARS);
    let big_lo_size = eq.low.len();
    let hi_size = n_windows.div_ceil(big_lo_size);
    let n_lo_and_inner = eq.low_log() + N_INNER;

    let d_inv_val = d_inv();
    let eq_lo_scaled: Vec<F192> = eq.low.iter().map(|v| *v * d_inv_val).collect();
    let eq_hi = &eq.high;

    let (within_outer_mask, b_med_counts) = build_b_med_counts(padding);
    drop(eq_span);

    // Count the periodic padding pattern, not the hot-loop iterations. These
    // counts describe this head only; the recursive tail has its own cube span.
    let pattern_repeats = n_windows / b_med_counts.len();
    let pattern_remainder = n_windows % b_med_counts.len();
    let count = |predicate: fn(u8) -> usize| {
        pattern_repeats * b_med_counts.iter().map(|&n| predicate(n)).sum::<usize>()
            + b_med_counts[..pattern_remainder].iter().map(|&n| predicate(n)).sum::<usize>()
    };
    let sweep_span = tracing::info_span!(
        "Round1 fused sweep",
        windows = n_windows,
        full_windows = count(|n| usize::from(n == 16)),
        partial_windows = count(|n| usize::from(n > 0 && n < 16)),
        skipped_windows = count(|n| usize::from(n == 0)),
        medium_windows = count(usize::from),
        eq_lo = big_lo_size,
        eq_hi = hi_size,
        tail_group_log = tail.map_or(0, |t| t.group_log),
        ntt_table_bytes = 256 * ELL,
        worker_bytes = core::mem::size_of::<WorkerState>(),
        neon = cfg!(target_arch = "aarch64"),
        gfni = cfg!(target_feature = "gfni"),
        avx512bw = cfg!(target_feature = "avx512bw"),
        avx512vbmi = cfg!(target_feature = "avx512vbmi"),
    )
    .entered();
    // AB lookup/multiply/shift, C extraction, medium conversion and outer
    // reduction are fused here. Do not add per-window clocks to separate them.

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
                n_windows,
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
    drop(sweep_span);

    let c_span = tracing::info_span!("Round1 C extension", lanes = ELL, bit_planes = 192).entered();
    let mut res_c_lifted = ntt_extend_vec(&res_c_s, inv_table);
    drop(c_span);
    let mut res_ab = res_ab.to_vec();
    if let Some(tail) = tail {
        let _tail = tracing::info_span!("Round1 tail", group_log = tail.group_log, head_bits = tail.head).entered();
        let [a, b, c] = [a_packed, b_packed, c_packed].map(|p| tail.group(p));
        let (group_ab, group_c) = round1_shift_reduce_extract_c_packed_padded(
            a,
            b,
            c,
            tail.group_log,
            &r_rest[..tail.r_inner],
            inv_table,
            &padding.without_tail(),
        );
        let _output = tracing::info_span!("Round1 tail output", lanes = ELL).entered();
        for (x, y) in res_ab.iter_mut().zip(group_ab) {
            *x += tail.weight * y;
        }
        for (x, y) in res_c_lifted.iter_mut().zip(group_c) {
            *x += tail.weight * y;
        }
    }
    (res_ab, res_c_lifted)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::zerocheck::PaddingSpec;
    use crate::zerocheck::ntt::AdditiveNttGf8;
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    // Temporary attribution harness. ROUND1_INPUT_DIR replays captured witness
    // bytes and challenges; otherwise required shape fields select synthetic data.
    // Component working sets are deliberately separate; their timings must not
    // be subtracted from or added up to predict the fused production sweep.
    #[test]
    #[ignore = "temporary native-hardware Round1 attribution; requires captured input or traced shape"]
    fn diagnostic_round1_components() {
        use std::hint::black_box;
        use std::time::Instant;

        let required = |name: &str| -> usize {
            std::env::var(name).unwrap_or_else(|_| panic!("set {name} from a Round1 class trace")).parse().unwrap()
        };
        let optional = |name: &str, default: usize| -> usize {
            std::env::var(name).map_or(default, |v| v.parse().unwrap())
        };
        let input_dir = std::env::var_os("ROUND1_INPUT_DIR").map(std::path::PathBuf::from);
        let (m, padding) = if let Some(dir) = &input_dir {
            let shape = std::fs::read_to_string(dir.join("shape.txt")).expect("read captured shape");
            let shape: Vec<usize> = shape.split_whitespace().map(|v| v.parse().unwrap()).collect();
            assert_eq!(shape.len(), 4, "capture shape is m k_log useful_bits live_blocks");
            (shape[0], PaddingSpec { k_log: shape[1], useful_bits_per_block: shape[2], live_blocks: shape[3] })
        } else {
            (required("ROUND1_M"), PaddingSpec {
                k_log: required("ROUND1_K_LOG"),
                useful_bits_per_block: required("ROUND1_USEFUL_BITS"),
                live_blocks: required("ROUND1_LIVE_BLOCKS"),
            })
        };
        let repeats = optional("ROUND1_REPEATS", 5);
        let sample_limit = optional("ROUND1_SAMPLE_WINDOWS", 256);
        assert!(m >= K_SKIP + N_INNER && padding.k_log <= m);
        assert!(padding.useful_bits_per_block <= 1 << padding.k_log);
        assert!(repeats > 0 && sample_limit > 0);
        let bytes = (1usize << m) / 8;
        let (a, b, c, r) = if let Some(dir) = &input_dir {
            let load = |name| std::fs::read(dir.join(name)).expect("read Round1 capture");
            let raw_r = load("r.bin");
            assert_eq!(raw_r.len(), (m - K_SKIP) * 24, "captured challenge length");
            let r: Vec<_> = raw_r.chunks_exact(24).map(|bytes| {
                let limb = |i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap());
                F192::new(limb(0), limb(8), limb(16))
            }).collect();
            (load("a.bin"), load("b.bin"), load("c.bin"), r)
        } else {
            let mut rng = Rng::new(0x524f_554e_4431);
            let block_bytes = (1usize << padding.k_log) / 8;
            assert!(block_bytes > 0);
            let mut a = pack_bits(&rng.bits(1 << m));
            let mut b = pack_bits(&rng.bits(1 << m));
            for packed in [&mut a, &mut b] {
                for block in packed.chunks_exact_mut(block_bytes) {
                    let full = padding.useful_bits_per_block / 8;
                    let bits = padding.useful_bits_per_block % 8;
                    if bits > 0 {
                        block[full] &= (1u8 << bits) - 1;
                    }
                    block[full + usize::from(bits > 0)..].fill(0);
                }
                if padding.live_blocks < bytes / block_bytes {
                    let tail_start = padding.live_blocks * block_bytes;
                    for start in ((tail_start + block_bytes)..bytes).step_by(block_bytes) {
                        packed.copy_within(tail_start..tail_start + block_bytes, start);
                    }
                }
            }
            let c: Vec<u8> = a.iter().zip(&b).map(|(a, b)| a & b).collect();
            let r = build_protocol_r_rest(m, &rng.ext_vec(m - K_SKIP - N_INNER));
            (a, b, c, r)
        };
        for input in [&a, &b, &c] {
            assert_eq!(input.len(), bytes, "packed input length");
        }
        let table = make_inv_table();
        let tail = padding.tail(m, K_SKIP + N_INNER, K_SKIP + N_INNER, &r);
        let windows = tail.map_or(1 << (m - K_SKIP - N_INNER), |t| t.head >> (K_SKIP + N_INNER));
        let (mask, counts) = build_b_med_counts(&padding);
        let eq = SplitEq::with_high_vars(&r[N_INNER..], EQ_HIGH_VARS);
        let eq_lo: Vec<_> = eq.low.iter().map(|v| *v * d_inv()).collect();
        let samples = windows.min(sample_limit);
        assert!(samples > 0, "class has no head windows; benchmark its traced tail cube instead");
        let weights: Vec<_> = (0..samples).map(|w| eq_lo[w % eq_lo.len()]).collect();
        let nmedium: Vec<_> = (0..samples).map(|w| counts[w & mask] as usize).collect();
        let medium_count: usize = nmedium.iter().sum();
        let mut expanded = Vec::with_capacity(medium_count);
        let mut ab_rows = vec![[[0u8; ELL]; N_MEDIUM_VALUES]; samples];
        let mut c_rows = ab_rows.clone();
        for w in 0..samples {
            for med in 0..nmedium[w] {
                let offset = w * 1024 + med * 64;
                let mut columns = [[[F8::ZERO; ELL]; 8]; 2];
                for (input, cols) in [&a, &b].into_iter().zip(&mut columns) {
                    for (k, col) in cols.iter_mut().enumerate() {
                        let row = &input[offset + 8 * k..offset + 8 * k + 8];
                        table.apply(row, col);
                        let mut oracle = [F8::ZERO; ELL];
                        table.apply_scalar(row, &mut oracle);
                        assert_eq!(*col, oracle, "NTT w={w} med={med} k={k}");
                    }
                }
                let mut scalar = [0; ELL];
                shift_reduce_inner_ab_scalar(&a, &b, &table, w * 1024, med, &mut scalar);
                shift_reduce_inner_ab(&a, &b, &table, w * 1024, med, &mut ab_rows[w][med]);
                assert_eq!(ab_rows[w][med], scalar, "fused AB w={w} med={med}");
                assert_eq!(diagnostic_gf8_shift(&columns), scalar, "isolated GF8 w={w} med={med}");
                expanded.push(columns);
                let input: &[u8; 64] = c[offset..offset + 64].try_into().unwrap();
                bit_transpose_64bytes(input, &mut c_rows[w][med]);
                for lane in 0..ELL {
                    let expected = (0..8).fold(0, |acc, k| acc | (((input[k * 8 + lane / 8] >> (lane % 8)) & 1) << k));
                    assert_eq!(c_rows[w][med][lane], expected, "C extract");
                }
            }
        }
        let mut converted = Convert::new();
        let mut oracle = [[F192::ZERO; ELL]; 2];
        for w in 0..samples {
            converted.accumulate(&ab_rows[w][..nmedium[w]], &c_rows[w][..nmedium[w]], weights[w]);
            for lane in 0..ELL {
                for med in 0..nmedium[w] {
                    oracle[0][lane] += gamma_powers()[med] * phi8_192(F8(ab_rows[w][med][lane])) * weights[w];
                }
            }
            for lane in 0..ELL {
                for med in 0..nmedium[w] {
                    oracle[1][lane] += gamma_powers()[med] * phi8_192(F8(c_rows[w][med][lane])) * weights[w];
                }
            }
        }
        assert_eq!(converted.values(), (oracle[0], oracle[1]), "medium conversion plus eq_lo");
        let reference = diagnostic_round1_reference([&a, &b, &c], m, &r, &table, &padding);
        assert_eq!(
            round1_shift_reduce_extract_c_packed_padded(&a, &b, &c, m, &r, &table, &padding),
            reference,
            "full production sweep including tail and C extension",
        );
        let measure = |label: &str, units: usize, f: &mut dyn FnMut()| {
            f(); // warm caches and lazy tables outside the timed interval
            let start = Instant::now();
            for _ in 0..repeats {
                f();
            }
            eprintln!("round1_diag component={label} units_per_repeat={units} repeats={repeats} elapsed_ns={}", start.elapsed().as_nanos());
        };
        eprintln!("round1_diag m={m} k_log={} useful_bits={} live_blocks={} head_windows={windows} sample_windows={samples} sample_medium={medium_count} worker_bytes={} synthetic={} neon_tiled={}",
            padding.k_log, padding.useful_bits_per_block, padding.live_blocks, core::mem::size_of::<WorkerState>(),
            input_dir.is_none(), cfg!(all(target_arch = "aarch64", leanvm_round1_neon_tiled)));
        measure("production_round1", windows, &mut || {
            black_box(round1_shift_reduce_extract_c_packed_padded(black_box(&a), black_box(&b), black_box(&c), m, &r, &table, &padding));
        });
        measure("ntt_lookup", medium_count * 16, &mut || {
            let mut out = [F8::ZERO; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    for input in [&a, &b] {
                        for k in 0..8 {
                            let off = w * 1024 + med * 64 + k * 8;
                            table.apply(black_box(&input[off..off + 8]), &mut out);
                            black_box(&out);
                        }
                    }
                }
            }
        });
        measure("gf8_multiply_shift_reduce", medium_count, &mut || {
            for cols in &expanded {
                black_box(diagnostic_gf8_shift(black_box(cols)));
            }
        });
        measure("fused_ab", medium_count, &mut || {
            let mut out = [0; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    shift_reduce_inner_ab(black_box(&a), black_box(&b), &table, w * 1024, med, &mut out);
                    black_box(&out);
                }
            }
        });
        measure("c_extract", medium_count, &mut || {
            let mut out = [0; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    let off = w * 1024 + med * 64;
                    bit_transpose_64bytes(black_box(c[off..off + 64].try_into().unwrap()), &mut out);
                    black_box(&out);
                }
            }
        });
        measure("medium_convert_eq_lo", nmedium.iter().filter(|&&n| n > 0).count(), &mut || {
            let mut out = Convert::new();
            for w in 0..samples {
                if nmedium[w] == 0 {
                    continue;
                }
                out.accumulate(black_box(&ab_rows[w][..nmedium[w]]), black_box(&c_rows[w][..nmedium[w]]), black_box(weights[w]));
            }
            black_box(out.values());
        });
        measure("outer_reduce", windows.div_ceil(eq_lo.len()), &mut || {
            let mut out = [[F192::ZERO; ELL]; 2];
            for &hi in eq.high.iter().take(windows.div_ceil(eq_lo.len())) {
                let (partial_ab, partial_c) = black_box(&converted).values();
                for lane in 0..ELL {
                    out[0][lane] += black_box(hi) * black_box(partial_ab[lane]);
                    out[1][lane] += black_box(hi) * black_box(partial_c[lane]);
                }
            }
            black_box(out);
        });
        measure("c_extension", 192, &mut || {
            black_box(ntt_extend_vec(black_box(&oracle[1]), &table));
        });
    }

    // Independent scalar medium conversion and direct eq_lo*eq_hi weighting.
    // Reuses the already scalar-checked NTT table and the existing C extension,
    // but not WorkerState, Convert, process_one_x_hi or the fused AB kernel.
    fn diagnostic_round1_reference(
        packed: [&[u8]; 3],
        m: usize,
        r: &[F192],
        table: &InvNttTableByteSingleGf8,
        padding: &PaddingSpec,
    ) -> (Vec<F192>, Vec<F192>) {
        let tail = padding.tail(m, K_SKIP + N_INNER, K_SKIP + N_INNER, r);
        let windows = tail.map_or(1 << (m - K_SKIP - N_INNER), |t| t.head >> (K_SKIP + N_INNER));
        let (mask, counts) = build_b_med_counts(padding);
        let eq = SplitEq::with_high_vars(&r[N_INNER..], EQ_HIGH_VARS);
        let mut ab = vec![F192::ZERO; ELL];
        let mut c = vec![F192::ZERO; ELL];
        for w in 0..windows {
            let weight = eq.low[w % eq.low.len()] * eq.high[w / eq.low.len()] * d_inv();
            let mut medium_ab = [F192::ZERO; ELL];
            let mut medium_c = [F192::ZERO; ELL];
            for med in 0..counts[w & mask] as usize {
                let mut row_ab = [0; ELL];
                shift_reduce_inner_ab_scalar(packed[0], packed[1], table, w * 1024, med, &mut row_ab);
                let input = &packed[2][w * 1024 + med * 64..w * 1024 + med * 64 + 64];
                for lane in 0..ELL {
                    let byte = (0..8).fold(0, |acc, k| acc | (((input[k * 8 + lane / 8] >> (lane % 8)) & 1) << k));
                    medium_ab[lane] += gamma_powers()[med] * phi8_192(F8(row_ab[lane]));
                    medium_c[lane] += gamma_powers()[med] * phi8_192(F8(byte));
                }
            }
            for lane in 0..ELL {
                ab[lane] += weight * medium_ab[lane];
                c[lane] += weight * medium_c[lane];
            }
        }
        let mut c = ntt_extend_vec(&c, table);
        if let Some(tail) = tail {
            let (tail_ab, tail_c) = diagnostic_round1_reference(
                packed.map(|p| tail.group(p)), tail.group_log, &r[..tail.r_inner], table, &padding.without_tail(),
            );
            for lane in 0..ELL {
                ab[lane] += tail.weight * tail_ab[lane];
                c[lane] += tail.weight * tail_c[lane];
            }
        }
        (ab, c)
    }

    /// Same GF8 multiply/widen/shift/reduce arithmetic with already-expanded
    /// columns. The input traffic and register schedule differ from fusion.
    #[inline(never)]
    fn diagnostic_gf8_shift(columns: &[[[F8; ELL]; 8]; 2]) -> [u8; ELL] {
        let mut out = [0; ELL];
        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: NEON is baseline and each column contains 64 bytes.
            unsafe {
                let mut acc = [[vdupq_n_u16(0); 2]; 4];
                macro_rules! step {
                    ($k:literal) => {
                        for (h, [lo, hi]) in acc.iter_mut().enumerate() {
                            let a = vld1q_u8(columns[0][$k].as_ptr().cast::<u8>().add(16 * h));
                            let b = vld1q_u8(columns[1][$k].as_ptr().cast::<u8>().add(16 * h));
                            let y = gf8_mul_vec16(a, b);
                            *lo = veorq_u16(*lo, vshll_n_u8::<$k>(vget_low_u8(y)));
                            *hi = veorq_u16(*hi, vshll_n_u8::<$k>(vget_high_u8(y)));
                        }
                    };
                }
                step!(0); step!(1); step!(2); step!(3);
                step!(4); step!(5); step!(6); step!(7);
                for (h, [lo, hi]) in acc.into_iter().enumerate() {
                    vst1q_u8(out.as_mut_ptr().add(16 * h), gf8_reduce_vec16(vreinterpretq_u8_u16(lo), vreinterpretq_u8_u16(hi)));
                }
            }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
        {
            // SAFETY: features are enabled at compile time; all loads/stores
            // cover exactly one 64-byte column.
            unsafe {
                let (mut lo, mut hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
                let zero = _mm512_setzero_si512();
                for k in 0..8 {
                    let y = _mm512_gf2p8mul_epi8(
                        _mm512_loadu_si512(columns[0][k].as_ptr().cast()),
                        _mm512_loadu_si512(columns[1][k].as_ptr().cast()),
                    );
                    let shift = _mm_cvtsi32_si128(k as i32);
                    lo = _mm512_xor_si512(lo, _mm512_sll_epi16(_mm512_unpacklo_epi8(y, zero), shift));
                    hi = _mm512_xor_si512(hi, _mm512_sll_epi16(_mm512_unpackhi_epi8(y, zero), shift));
                }
                let mask = _mm512_set1_epi16(255);
                let fold = |p: __m512i| {
                    let h = _mm512_srli_epi16::<8>(p);
                    _mm512_xor_si512(_mm512_and_si512(p, mask), _mm512_xor_si512(
                        _mm512_xor_si512(h, _mm512_slli_epi16::<1>(h)),
                        _mm512_xor_si512(_mm512_slli_epi16::<3>(h), _mm512_slli_epi16::<4>(h))))
                };
                let reduce = |p| _mm512_and_si512(fold(fold(p)), mask);
                _mm512_storeu_si512(out.as_mut_ptr().cast(), _mm512_packus_epi16(reduce(lo), reduce(hi)));
            }
        }
        #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))))]
        {
            for lane in 0..ELL {
                let acc = (0..8).fold(0u16, |acc, k| acc ^ (((columns[0][k][lane] * columns[1][k][lane]).0 as u16) << k));
                out[lane] = gf8_reduce(acc);
            }
        }
        out
    }

    /// Compute the round-1 prover message naively (no shift-reduce, no fused
    /// inner, no deferred reduction: direct algorithmic translation of the
    /// protocol formula).
    ///
    /// Returns `(p_ab, p_c)`, each a length-`2^K_SKIP` F192 vector of evaluations
    /// on Λ.
    ///
    /// Preconditions:
    /// - `a.len() == b.len() == c.len() == 2^m`
    /// - `r_rest.len() == m - K_SKIP`
    ///
    /// Index convention: for index `i ∈ 0..2^m`, the low `K_SKIP` bits address
    /// the *skip* variables (`y_skip ∈ S`), the high `m - K_SKIP` bits address
    /// the *rest* variables (`y_rest`).
    pub(crate) fn round1_naive(
        a: &[bool],
        b: &[bool],
        c: &[bool],
        m: usize,
        r_rest: &[F192],
    ) -> (Vec<F192>, Vec<F192>) {
        assert!(K_SKIP <= m, "K_SKIP must be ≤ m");
        assert_eq!(a.len(), 1usize << m);
        assert_eq!(b.len(), 1usize << m);
        assert_eq!(c.len(), 1usize << m);
        assert_eq!(r_rest.len(), m - K_SKIP);

        let ell = 1usize << K_SKIP;
        let n_chunks_x = 1usize << (m - K_SKIP);

        // NTT for evaluating-on-Λ via inv-on-S then fwd-on-Λ.
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(ell as u8));

        let eq_full = eq_table(r_rest);

        let mut p_ab = vec![F192::ZERO; ell];
        let mut p_c = vec![F192::ZERO; ell];

        let mut a_col = vec![F8::ZERO; ell];
        let mut b_col = vec![F8::ZERO; ell];
        let mut c_col = vec![F8::ZERO; ell];

        for (x_rest, &weight) in eq_full.iter().enumerate().take(n_chunks_x) {
            let base = x_rest * ell;
            for s in 0..ell {
                a_col[s] = F8(a[base + s] as u8);
                b_col[s] = F8(b[base + s] as u8);
                c_col[s] = F8(c[base + s] as u8);
            }
            // Extend the row polynomial from S to Λ.
            ntt_s.inverse(&mut a_col);
            ntt_l.forward(&mut a_col);
            ntt_s.inverse(&mut b_col);
            ntt_l.forward(&mut b_col);
            ntt_s.inverse(&mut c_col);
            ntt_l.forward(&mut c_col);

            let eq_x = weight;
            for i in 0..ell {
                let ab = a_col[i] * b_col[i];
                p_ab[i] += eq_x * phi8_192(ab);
                p_c[i] += eq_x * phi8_192(c_col[i]);
            }
        }

        (p_ab, p_c)
    }

    /// Pack a bit vector LSB-first into bytes.
    pub(crate) fn pack_bits(bits: &[bool]) -> Vec<u8> {
        let n_bytes = bits.len().div_ceil(8);
        // Each output byte depends on 8 contiguous input bits: disjoint, so
        // process bytes in parallel.
        parallel::map_collect(n_bytes, |byte_idx| {
            let mut byte = 0u8;
            let base = byte_idx * 8;
            for j in 0..8 {
                let bit_idx = base + j;
                if bit_idx < bits.len() && bits[bit_idx] {
                    byte |= 1u8 << j;
                }
            }
            byte
        })
    }

    #[test]
    fn convert_matches_definition() {
        // Compare converted field values with their weighted sum over full and partial windows.
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
                        .zip(gamma_powers())
                        .fold(F192::ZERO, |acc, (row, &gamma)| acc + gamma * phi8_192(F8(row[lane])))
                };
                want_ab[lane] += conv(&ab) * eq;
                want_c[lane] += conv(&c) * eq;
            }
        }
        assert_eq!(partials.values(), (want_ab, want_c));
    }

    /// Every AVX2 product this target compiles converts as the definition does, not only the dispatched one.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn convert_avx2_matches_definition() {
        fn check<P: avx2::Product>(rng: &mut Rng) {
            let maps = convert_maps::<P>();
            for n in [16, 7] {
                let rows: Vec<[u8; 64]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64() as u8)).collect();
                // SAFETY: the crate is built with AVX2.
                let got = unsafe { convert_avx2::<P>(&rows, &maps) };
                let want: [F192; ELL] = std::array::from_fn(|lane| {
                    rows.iter()
                        .zip(gamma_powers())
                        .fold(F192::ZERO, |acc, (row, &gamma)| acc + gamma * phi8_192(F8(row[lane])))
                });
                assert_eq!(got, want, "n={n}");
            }
        }
        let mut rng = Rng::new(0xA7_C04E);
        check::<avx2::Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check::<avx2::Gfni>(&mut rng);
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn x86_inner_matches_scalar_inner() {
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
            let mut out_simd = [0u8; 64];
            shift_reduce_inner_ab(&a_packed, &b_packed, &inv_table, 0, 0, &mut out_simd);
            assert_eq!(out_scalar, out_simd, "dispatched");
            #[cfg(target_feature = "avx2")]
            {
                // SAFETY: the crate is built with AVX2, and with GFNI where the kernel uses it.
                unsafe { shift_reduce_inner_ab_avx2(&a_packed, &b_packed, &inv_table, 0, 0, &mut out_simd) };
                assert_eq!(out_scalar, out_simd, "avx2");
            }
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
                        let pivot = rows[rank];
                        for (limb, value) in rows[i].iter_mut().zip(pivot) {
                            *limb ^= value;
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

            let (naive_ab, naive_c) = round1_naive(&a, &b, &c, m, &r);
            let (opt_ab, opt_c) = round1_shift_reduce_extract_c_packed_padded(
                &pack_bits(&a),
                &pack_bits(&b),
                &pack_bits(&c),
                m,
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
                round1_shift_reduce_extract_c_packed_padded(&a_p, &b_p, &c_p, m, &r, &table, &dense);
            let padding = PaddingSpec {
                k_log,
                useful_bits_per_block: useful_bits,
                live_blocks: usize::MAX,
            };
            let (padded_ab, padded_c) =
                round1_shift_reduce_extract_c_packed_padded(&a_p, &b_p, &c_p, m, &r, &table, &padding);

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
        let a_packed = pack_bits(&a_bits);
        let b_packed = pack_bits(&b_bits);

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
            #[cfg(leanvm_round1_neon_tiled)]
            {
                shift_reduce_inner_ab_tiled_neon(&a_packed, &b_packed, &table, chunk_byte_base, b_med, &mut out_fused);
                assert_eq!(out_scalar, out_fused, "quarter-first NEON at (base={chunk_byte_base}, b_med={b_med})");
            }
        }
    }
}
