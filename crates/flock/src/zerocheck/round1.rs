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
//! The sweep groups the equality weights into three factors:
//!
//! 1. **Geometric small-eq** (3 innermost rest dimensions).
//!    The fixed challenges `r_rest[..3] = φ_8([0xF7, 0x53, 0xB5])` give
//!    `eq_small[K] = C_s · α^K`. Plonky3's packed AES field computes
//!    `Σ_K α^K · y_K`; the caller restores the common factor `C_s`.
//!
//! 2. **Geometric medium-eq + convert table** (4 next rest-dims).
//!    Protocol fixes the four medium challenges to
//!    `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`, which makes
//!    `eq_med[b] = γ^b / D` for `D = ∏(1+γ^{2^{i-1}})`.
//!    A precomputed `convert[b][v] = γ^b · φ_8(v)` table replaces field multiplications with lookups and XORs.
//!    On ARM, conversion visits all lanes for a bounded group of four medium rows before
//!    advancing to the next group. Two stack-resident lane arrays retain the unweighted
//!    sums across groups; the equality weight is applied only after the complete window,
//!    including a partial final group. This traversal leaves the packed AB sweep and C
//!    transpose unchanged.
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

use primitives::PrimeCharacteristicRing;

use super::{K_SKIP, N_INNER, PaddingSpec};
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
use p3_binary_dft::RijndaelLde;
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
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use primitives::mul_base8;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use primitives::mul4;
use primitives::multilinear::SplitEq;
use primitives::{F8, F64, F192, PHI_8_TABLE_192, phi8_192};
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
    phi8_192(F8::from_byte(C_S_F8))
}

/// The three F192 small challenges (embeddings of `SMALL_CHAL_F8`): caller
/// must place these at `r_rest[..3]` for the naive cross-check to
/// produce a result related to the optimized output by exactly `C_s`.
pub(crate) fn small_challenges() -> [F192; 3] {
    [
        phi8_192(F8::from_byte(SMALL_CHAL_F8[0])),
        phi8_192(F8::from_byte(SMALL_CHAL_F8[1])),
        phi8_192(F8::from_byte(SMALL_CHAL_F8[2])),
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
        g1 * (F192::ONE + g1).invert_or_zero(),
        g2 * (F192::ONE + g2).invert_or_zero(),
        g4 * (F192::ONE + g4).invert_or_zero(),
        g8 * (F192::ONE + g8).invert_or_zero(),
    ]
}

/// Protocol medium-coordinate generator in the tower basis.
const fn medium_generator() -> F192 {
    F192::new([
        F64::new(0x243f_6a88_85a3_08d3),
        F64::new(0x1319_8a2e_0370_7344),
        F64::new(0xa409_3822_299f_31d0),
    ])
}

/// `D = (1+γ)(1+γ^2)(1+γ^4)(1+γ^8)`; `D⁻¹` cancels the medium-eq normalization.
fn compute_d_inv() -> F192 {
    let g1 = medium_generator();
    let g2 = g1.square();
    let g4 = g2.square();
    let g8 = g4.square();
    ((F192::ONE + g1) * (F192::ONE + g2) * (F192::ONE + g4) * (F192::ONE + g8)).invert_or_zero()
}

static D_INV_CACHE: OnceLock<F192> = OnceLock::new();
fn d_inv() -> F192 {
    *D_INV_CACHE.get_or_init(compute_d_inv)
}

/// Most high variables of a split eq table capped on its high side: few high weights keep the outer products cheap.
pub(crate) const EQ_HIGH_VARS: usize = 7;

/// Extend a length-`ell` F192 vector from S to Λ with the original GF8
/// butterflies lifted through φ₈. Only the returned vector is allocated;
/// the Boolean A/B lookup table remains the bulk-row path.
pub(crate) fn ntt_extend_vec(in_s: &[F192], inv_table: &RijndaelLde) -> Vec<F192> {
    assert_eq!(in_s.len(), inv_table.row_len());
    let mut out = in_s.to_vec();
    // The protocol's AES embedding lies in the base field.
    let embed = |byte| phi8_192(byte).coefficients()[0];
    inv_table
        .source()
        .map(embed)
        .transform_algebra::<F192, true>(&mut out, 1);
    inv_table
        .target()
        .map(embed)
        .transform_algebra::<F192, false>(&mut out, 1);
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

// For each medium position, extend its eight small-position rows through
// the NTT lookup table, multiply them in F8, and sum with weights x^K.
// The output is the F8 representative that the protocol embeds into F192.

/// Sum eight weighted rows through Plonky3's packed AES field.
#[inline(always)]
fn shift_reduce_inner_ab(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &RijndaelLde,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    let byte_base = chunk_byte_base + b_med * N_CHUNKS * 8;
    let weights = std::array::from_fn::<_, 8, _>(|k| F8::from_byte(1 << k));
    let mut columns = [F8::ZERO; ELL];
    inv_table.weighted_product_sum(
        &a_packed[byte_base..byte_base + 8 * N_CHUNKS],
        &b_packed[byte_base..byte_base + 8 * N_CHUNKS],
        &weights,
        &mut columns,
    );
    for (byte, value) in out.iter_mut().zip(columns) {
        *byte = value.to_byte();
    }
}

#[cfg(test)]
fn shift_reduce_inner_ab_scalar(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &RijndaelLde,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    let mut a_col = [F8::ZERO; ELL];
    let mut b_col = [F8::ZERO; ELL];
    let mut sum = [F8::ZERO; ELL];
    let byte_base = chunk_byte_base + b_med * N_CHUNKS * 8;
    for k in 0..8 {
        let offset = byte_base + k * N_CHUNKS;
        inv_table.apply(&a_packed[offset..offset + N_CHUNKS], &mut a_col);
        inv_table.apply(&b_packed[offset..offset + N_CHUNKS], &mut b_col);
        for lane in 0..ELL {
            sum[lane] += a_col[lane] * b_col[lane] * F8::from_byte(1 << k);
        }
    }
    *out = sum.map(F8::to_byte);
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
        #[cfg(target_arch = "aarch64")]
        {
            // Keep a bounded group of conversion rows active while amortizing
            // scratch updates across its medium positions.
            let mut converted_ab = [F192::ZERO; ELL];
            let mut converted_c = [F192::ZERO; ELL];
            for ((rows, ab), c) in convert.chunks(4).zip(ab.chunks(4)).zip(c.chunks(4)) {
                for lane in 0..ELL {
                    let mut cf_ab = F192::ZERO;
                    let mut cf_c = F192::ZERO;
                    for ((row, ab), c) in rows.iter().zip(ab).zip(c) {
                        cf_ab += row[ab[lane] as usize];
                        cf_c += row[c[lane] as usize];
                    }
                    converted_ab[lane] += cf_ab;
                    converted_c[lane] += cf_c;
                }
            }
            use primitives::{ExtensionField, Field, PackedFieldExtension, PackedValue};
            type Packing = <F192 as ExtensionField<F64>>::ExtensionPacking;
            const WIDTH: usize = <<F64 as Field>::Packing as PackedValue>::WIDTH;
            let weight = Packing::from(eq_lo);
            for start in (0..ELL).step_by(WIDTH) {
                let range = start..start + WIDTH;
                let ab = Packing::from_ext_slice(&converted_ab[range.clone()]) * weight;
                let c = Packing::from_ext_slice(&converted_c[range.clone()]) * weight;
                let ab = Packing::from_ext_slice(&self.ab[range.clone()]) + ab;
                let c = Packing::from_ext_slice(&self.c[range.clone()]) + c;
                ab.to_ext_slice(&mut self.ab[range.clone()]);
                c.to_ext_slice(&mut self.c[range]);
            }
        }
        #[cfg(not(target_arch = "aarch64"))]
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
                assert!(
                    phi.coefficients()[1].to_bits() == 0 && phi.coefficients()[2].to_bits() == 0,
                    "phi_8 lands in the base field"
                );
                F64::new(phi.coefficients()[0].to_bits())
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
    inv_table: &RijndaelLde,
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
    inv_table: &RijndaelLde,
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
    inv_table: &RijndaelLde,
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
    assert_eq!(inv_table.log_domain_size(), K_SKIP);

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

    let mut res_c_lifted = ntt_extend_vec(&res_c_s, inv_table);
    let mut res_ab = res_ab.to_vec();
    if let Some(tail) = tail {
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
    use p3_binary_dft::BasisNtt as AdditiveNttGf8;
    use primitives::PrimeCharacteristicRing;
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    /// Direct monomial Lagrange interpolation, independent of the NTT
    /// recurrence, its LCH basis, and the collapsed Boolean lookup table.
    fn lagrange_extension_matrix(k: usize, beta_s: F8, beta_l: F8) -> Vec<Vec<F192>> {
        let ell = 1usize << k;
        let s: Vec<F8> = (0..ell).map(|j| beta_s + F8::from_byte(j as u8)).collect();
        let denominators: Vec<F8> = s
            .iter()
            .enumerate()
            .map(|(j, &s_j)| {
                s.iter()
                    .enumerate()
                    .filter(|&(h, _)| h != j)
                    .fold(F8::ONE, |acc, (_, &s_h)| acc * (s_j + s_h))
                    .invert_or_zero()
            })
            .collect();
        (0..ell)
            .map(|i| {
                let x = beta_l + F8::from_byte(i as u8);
                let numerator = s.iter().fold(F8::ONE, |acc, &s_h| acc * (x + s_h));
                s.iter()
                    .zip(&denominators)
                    .map(|(&s_j, &denominator)| phi8_192(numerator * (x + s_j).invert_or_zero() * denominator))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn lifted_extension_matches_lagrange_arbitrary_e() {
        let mut rng = Rng::new(0x0011_f7ed);
        // All supported table sizes, including the byte-packing boundary and
        // the two halves of the full GF8 domain. Reversing/offsetting the
        // cosets also checks that we lift the supplied transforms' twiddles.
        for k in 3..=7 {
            for beta_s in [F8::ZERO, F8::from_byte(0xff)] {
                let beta_l = beta_s + F8::from_byte(1u8 << k);
                let ntt_s = AdditiveNttGf8::polynomial(k, beta_s);
                let ntt_l = AdditiveNttGf8::polynomial(k, beta_l);
                let table = RijndaelLde::new(ntt_s.log_domain_size(), ntt_s.shift(), ntt_l.shift());
                let matrix = lagrange_extension_matrix(k, beta_s, beta_l);
                for _ in 0..4 {
                    let input = rng.ext_vec(1 << k);
                    let expected: Vec<F192> = matrix
                        .iter()
                        .map(|row| {
                            row.iter()
                                .zip(&input)
                                .fold(F192::ZERO, |acc, (&weight, &value)| acc + weight * value)
                        })
                        .collect();
                    assert_eq!(ntt_extend_vec(&input, &table), expected, "k={k}, beta_s={beta_s:?}");
                }
            }
        }
    }

    #[test]
    fn lifted_extension_preserves_tower_basis() {
        for k in 3..=7 {
            let ell = 1usize << k;
            let ntt_s = AdditiveNttGf8::polynomial(k, F8::ZERO);
            let ntt_l = AdditiveNttGf8::polynomial(k, F8::from_byte(ell as u8));
            let table = RijndaelLde::new(ntt_s.log_domain_size(), ntt_s.shift(), ntt_l.shift());
            let matrix = lagrange_extension_matrix(k, F8::ZERO, F8::from_byte(ell as u8));
            // Each of the 192 tower-coordinate bits, including both limb
            // boundaries, and every evaluation position at each supported size.
            for bit in 0..192 {
                let mut limbs = [0u64; 3];
                limbs[bit / 64] = 1u64 << (bit % 64);
                let basis = F192::new([F64::new(limbs[0]), F64::new(limbs[1]), F64::new(limbs[2])]);
                let position = bit % ell;
                let mut input = vec![F192::ZERO; ell];
                input[position] = basis;
                let expected: Vec<F192> = matrix.iter().map(|row| basis * row[position]).collect();
                assert_eq!(ntt_extend_vec(&input, &table), expected, "k={k}, bit={bit}");
            }
        }
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
        let ntt_s = AdditiveNttGf8::polynomial(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::polynomial(K_SKIP, F8::from_byte(ell as u8));

        let eq_full = eq_table(r_rest);

        let mut p_ab = vec![F192::ZERO; ell];
        let mut p_c = vec![F192::ZERO; ell];

        let mut a_col = vec![F8::ZERO; ell];
        let mut b_col = vec![F8::ZERO; ell];
        let mut c_col = vec![F8::ZERO; ell];

        for (x_rest, &weight) in eq_full.iter().enumerate().take(n_chunks_x) {
            let base = x_rest * ell;
            for s in 0..ell {
                a_col[s] = F8::from_byte(a[base + s] as u8);
                b_col[s] = F8::from_byte(b[base + s] as u8);
                c_col[s] = F8::from_byte(c[base + s] as u8);
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
        // Repeated full windows followed by every possible boundary length.
        for n in [16, 16].into_iter().chain(0..16) {
            let ab: Vec<[u8; 64]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64() as u8)).collect();
            let c: Vec<[u8; 64]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64() as u8)).collect();
            let eq = rng.ext();
            partials.accumulate(&ab, &c, eq);
            for lane in 0..ELL {
                let conv = |rows: &[[u8; 64]]| {
                    rows.iter().zip(gamma_powers()).fold(F192::ZERO, |acc, (row, &gamma)| {
                        acc + gamma * phi8_192(F8::from_byte(row[lane]))
                    })
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
                    rows.iter().zip(gamma_powers()).fold(F192::ZERO, |acc, (row, &gamma)| {
                        acc + gamma * phi8_192(F8::from_byte(row[lane]))
                    })
                });
                assert_eq!(got, want, "n={n}");
            }
        }
        let mut rng = Rng::new(0xA7_C04E);
        check::<avx2::Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check::<avx2::Gfni>(&mut rng);
    }

    #[test]
    fn packed_inner_matches_scalar_inner() {
        let mut seed = 0xDEADBEEFu64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u8
        };
        let ntt_s = AdditiveNttGf8::polynomial(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::polynomial(K_SKIP, F8::from_byte(1u8 << K_SKIP));
        let inv_table = RijndaelLde::new(ntt_s.log_domain_size(), ntt_s.shift(), ntt_l.shift());

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
                [
                    w.coefficients()[0].to_bits(),
                    w.coefficients()[1].to_bits(),
                    w.coefficients()[2].to_bits(),
                ]
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

    fn make_inv_table() -> RijndaelLde {
        let ntt_s = AdditiveNttGf8::polynomial(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::polynomial(K_SKIP, F8::from_byte(1u8 << K_SKIP));
        RijndaelLde::new(ntt_s.log_domain_size(), ntt_s.shift(), ntt_l.shift())
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

    #[test]
    fn packed_inner_respects_row_offsets() {
        // Byte offsets and medium positions must select the same rows as the scalar oracle.
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
            let mut out_packed = [0u8; 64];
            shift_reduce_inner_ab_scalar(&a_packed, &b_packed, &table, chunk_byte_base, b_med, &mut out_scalar);
            shift_reduce_inner_ab(&a_packed, &b_packed, &table, chunk_byte_base, b_med, &mut out_packed);
            assert_eq!(
                out_scalar, out_packed,
                "packed sweep disagrees with scalar at (base={chunk_byte_base}, b_med={b_med})"
            );
        }
    }
}
