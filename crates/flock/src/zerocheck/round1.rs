// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 prover message for the univariate skip, at a uniformly random
//! zerocheck point.
//!
//! The message is
//!
//! ```text
//! P^{AB}(λ) = Σ_x eq(r_rest, x) · φ₈(â(λ, x) · b̂(λ, x))
//! P^{C}(λ)  = Σ_x eq(r_rest, x) · φ₈(ĉ(λ, x))
//! ```
//!
//! over the `2^K_SKIP` points of the coset Λ. `â(λ, x)`, `b̂(λ, x)` and
//! `ĉ(λ, x)` all live in F₂⁸ (Λ sits inside the φ₈ image), so everything up to
//! the eq weighting is byte arithmetic; only the weighting is in F₁₉₂.
//!
//! Weighting one byte per lane per witness position with a multiplication would
//! be one F₁₉₂ multiply per `(lane, position)` pair. φ₈ is F₂-linear, so
//! `e · φ₈(v)` is instead read out of a 256-entry table for that `e`, and the
//! table is shared by every lane and every window: the low [`N_INNER`]
//! coordinates of `r_rest` give `2^N_INNER` weights, hence one row per weight,
//! and a multiplication survives only once per window, for the coordinates
//! above them. That is Four Russians over the bit-valued map, the same trick
//! Binius64 folds words with.
//!
//! C is accumulated on the input domain S rather than on Λ (it is linear, so
//! nothing forces it through the NTT per position) and lifted once at the end
//! by [`ntt_extend_vec`]. Its values are single bits, so a window's worth of
//! them transposes to one byte per lane and folds through the plain subset sums
//! of the same weights.

use pcs::ntt::InvNttTableByteSingleGf8;
use primitives::bits::bit_transpose_64bytes;
use primitives::field::{F8, F192, PHI_8_TABLE_192 as PHI_8_TABLE};

use super::univariate_skip::{SplitEq, build_eq, ntt_extend_vec};
use super::{K_SKIP, PaddingSpec};

/// Λ has `2^K_SKIP` points, one per lane of every kernel below.
const ELL: usize = 1 << K_SKIP;
/// Packed witness bytes per skip block, i.e. per witness position.
const N_CHUNKS: usize = ELL / 8;

/// Equality coordinates folded by table lookup instead of by multiplication.
/// One F₁₉₂ multiply then covers `2^N_INNER` witness positions, and the AB
/// table is `2^N_INNER · 6` KiB, which wants to stay inside L1. Measured: 4
/// beats both 5 and 6, the table leaving L1 costing more than the multiplies it
/// saves.
pub const N_INNER: usize = 4;
/// Witness positions per window.
const WINDOW: usize = 1 << N_INNER;
/// Windows hold this many transposed C bytes, one per 8 positions.
const C_GROUPS: usize = WINDOW / 8;

/// `ab[w][v] = eq_inner[w] · φ₈(v)`, one row per position in the window.
type AbTable = [[F192; 256]; WINDOW];
/// `c[g][mask] = Σ_{t ∈ mask} eq_inner[8g + t]`, one row per transposed C byte.
type CTable = [[F192; 256]; C_GROUPS];

/// The 256 subset sums of eight elements: `out[mask] = Σ_{j ∈ mask} basis[j]`.
fn subset_sums(basis: &[F192; 8], out: &mut [F192; 256]) {
    out[0] = F192::ZERO;
    for (j, &g) in basis.iter().enumerate() {
        let (built, rest) = out.split_at_mut(1 << j);
        for (dst, src) in rest[..1 << j].iter_mut().zip(built.iter()) {
            *dst = *src + g;
        }
    }
}

/// Both fold tables for one proof, from the `2^N_INNER` inner equality weights.
fn build_tables(eq_inner: &[F192]) -> (Box<AbTable>, Box<CTable>) {
    debug_assert_eq!(eq_inner.len(), WINDOW);
    let mut ab: Box<AbTable> = Box::new([[F192::ZERO; 256]; WINDOW]);
    for (w, row) in ab.iter_mut().enumerate() {
        // φ₈ is F₂-linear, so the row is the subset sums of the eight images of
        // the byte basis, and only those eight cost a multiplication.
        let basis: [F192; 8] = std::array::from_fn(|j| eq_inner[w] * PHI_8_TABLE[1 << j]);
        subset_sums(&basis, row);
    }
    let mut c: Box<CTable> = Box::new([[F192::ZERO; 256]; C_GROUPS]);
    for (g, row) in c.iter_mut().enumerate() {
        let basis: [F192; 8] = std::array::from_fn(|t| eq_inner[8 * g + t]);
        subset_sums(&basis, row);
    }
    (ab, c)
}

// ---------------------------------------------------------------------------
// Per-position Λ products.
// ---------------------------------------------------------------------------

/// `out[lane] = a[lane] · b[lane]` in F₂⁸, over all `ELL` lanes.
#[inline]
fn mul_lanes(a: &[F8; ELL], b: &[F8; ELL], out: &mut [u8; ELL]) {
    #[cfg(target_arch = "aarch64")]
    {
        use core::arch::aarch64::*;
        use primitives::field::gf2_8::neon::gf8_mul_vec16;
        // SAFETY: aarch64 statically guarantees NEON; the four 16-byte loads and
        // stores cover exactly `ELL` = 64 bytes of each array.
        unsafe {
            for v in 0..ELL / 16 {
                let x = vld1q_u8(a.as_ptr().add(v * 16).cast());
                let y = vld1q_u8(b.as_ptr().add(v * 16).cast());
                vst1q_u8(out.as_mut_ptr().add(v * 16), gf8_mul_vec16(x, y));
            }
        }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f"))]
    {
        use core::arch::x86_64::*;
        // SAFETY: gfni and avx512f are enabled at compile time; `ELL` = 64 is
        // exactly one ZMM of bytes in each array.
        unsafe {
            let x = _mm512_loadu_si512(a.as_ptr().cast());
            let y = _mm512_loadu_si512(b.as_ptr().cast());
            _mm512_storeu_si512(out.as_mut_ptr().cast(), _mm512_gf2p8mul_epi8(x, y));
        }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", not(target_feature = "avx512f")))]
    {
        use core::arch::x86_64::*;
        // SAFETY: gfni is enabled at compile time and SSE2 is baseline on
        // x86_64; the loads and stores cover exactly `ELL` bytes.
        unsafe {
            for v in 0..ELL / 16 {
                let x = _mm_loadu_si128(a.as_ptr().add(v * 16).cast());
                let y = _mm_loadu_si128(b.as_ptr().add(v * 16).cast());
                _mm_storeu_si128(out.as_mut_ptr().add(v * 16).cast(), _mm_gf2p8mul_epi8(x, y));
            }
        }
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "gfni"))))]
    {
        for lane in 0..ELL {
            out[lane] = (a[lane] * b[lane]).0;
        }
    }
}

// ---------------------------------------------------------------------------
// Prover.
// ---------------------------------------------------------------------------

/// Per-worker scratch: multi-KiB, so it is built once per worker rather than
/// per window.
struct WorkerState {
    a_col: [F8; ELL],
    b_col: [F8; ELL],
    /// A whole window's table indices, staged before the lane loop reads them:
    /// the fold then touches each lane's accumulator once per window instead of
    /// once per position, which is most of its memory traffic.
    ab_idx: [[u8; ELL]; WINDOW],
    c_idx: [[u8; ELL]; C_GROUPS],
    /// Everything one `x_hi` claims, before its own equality multiplication.
    partial_ab: [F192; ELL],
    partial_c: [F192; ELL],
    res_ab: [F192; ELL],
    res_c_s: [F192; ELL],
}

impl WorkerState {
    fn new() -> Self {
        Self {
            a_col: [F8::ZERO; ELL],
            b_col: [F8::ZERO; ELL],
            ab_idx: [[0u8; ELL]; WINDOW],
            c_idx: [[0u8; ELL]; C_GROUPS],
            partial_ab: [F192::ZERO; ELL],
            partial_c: [F192::ZERO; ELL],
            res_ab: [F192::ZERO; ELL],
            res_c_s: [F192::ZERO; ELL],
        }
    }
}

/// One window of `WINDOW` witness positions, weighted by `eq_lo_val`.
///
/// `n_pos` is how many of them carry data; the rest are the zero padding every
/// witness block ends with, and a zero position contributes `row[0] = 0`, so
/// stopping early is byte-identical to running the whole window.
#[inline(always)]
fn accumulate_window<const FULL: bool>(
    n_pos: usize,
    byte_base: usize,
    eq_lo_val: F192,
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    ab_tab: &AbTable,
    c_tab: &CTable,
    state: &mut WorkerState,
) {
    let n_pos = if FULL { WINDOW } else { n_pos.min(WINDOW) };
    let n_groups = n_pos.div_ceil(8);

    for w in 0..n_pos {
        let off = byte_base + w * N_CHUNKS;
        inv_table.apply(&a_packed[off..off + N_CHUNKS], &mut state.a_col);
        inv_table.apply(&b_packed[off..off + N_CHUNKS], &mut state.b_col);
        mul_lanes(&state.a_col, &state.b_col, &mut state.ab_idx[w]);
    }
    for g in 0..n_groups {
        let off = byte_base + g * 8 * N_CHUNKS;
        let block: &[u8; 64] = c_packed[off..off + 64].try_into().expect("64 C bytes per group");
        // Transposed, lane `l`'s byte packs the group's 8 positions, which is
        // exactly the index `c_tab` wants.
        bit_transpose_64bytes(block, &mut state.c_idx[g]);
    }

    // Eight lanes at a time: one lane's fold is a serial XOR chain as deep as
    // the window, so lanes are where the independent work is.
    for base in (0..ELL).step_by(8) {
        let mut ab = [F192::ZERO; 8];
        for w in 0..n_pos {
            let (row, idx) = (&ab_tab[w], &state.ab_idx[w]);
            for (acc, k) in ab.iter_mut().zip(0..8) {
                *acc += row[idx[base + k] as usize];
            }
        }
        let mut cc = [F192::ZERO; 8];
        for g in 0..n_groups {
            let (row, idx) = (&c_tab[g], &state.c_idx[g]);
            for (acc, k) in cc.iter_mut().zip(0..8) {
                *acc += row[idx[base + k] as usize];
            }
        }
        for k in 0..8 {
            state.partial_ab[base + k] += ab[k] * eq_lo_val;
            state.partial_c[base + k] += cc[k] * eq_lo_val;
        }
    }
}

/// Everything one `x_hi` of the [`SplitEq`] claims.
#[allow(clippy::too_many_arguments)]
fn process_one_x_hi(
    x_hi: usize,
    lo_size: usize,
    n_lo: usize,
    within_mask: usize,
    pos_counts: &[u8],
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    eq_lo: &[F192],
    eq_hi_val: F192,
    ab_tab: &AbTable,
    c_tab: &CTable,
    state: &mut WorkerState,
) {
    state.partial_ab.iter_mut().for_each(|v| *v = F192::ZERO);
    state.partial_c.iter_mut().for_each(|v| *v = F192::ZERO);

    for x_lo in 0..lo_size {
        let n_pos = pos_counts[(x_lo | (x_hi << n_lo)) & within_mask] as usize;
        if n_pos == 0 {
            continue;
        }
        let base = ((x_lo << N_INNER) | (x_hi << (n_lo + N_INNER))) * N_CHUNKS;
        let eq = eq_lo[x_lo];
        if n_pos == WINDOW {
            accumulate_window::<true>(
                n_pos, base, eq, a_packed, b_packed, c_packed, inv_table, ab_tab, c_tab, state,
            );
        } else {
            accumulate_window::<false>(
                n_pos, base, eq, a_packed, b_packed, c_packed, inv_table, ab_tab, c_tab, state,
            );
        }
    }

    for lane in 0..ELL {
        state.res_ab[lane] += eq_hi_val * state.partial_ab[lane];
        state.res_c_s[lane] += eq_hi_val * state.partial_c[lane];
    }
}

/// `(within_mask, pos_counts)`: how many of a window's `WINDOW` positions carry
/// data, indexed by the window's offset within one witness block.
///
/// A witness block is `2^k_log` bits of which the low `useful_bits_per_block`
/// carry data, so a window entirely past that prefix is skipped outright and a
/// straddling one stops at the position the prefix ends in.
fn build_position_counts(padding: &PaddingSpec) -> (usize, Vec<u8>) {
    /// Bits per window.
    const STRIDE: usize = 1 << (K_SKIP + N_INNER);
    /// Bits per witness position.
    const POS_BITS: usize = 1 << K_SKIP;

    // A block smaller than one window cannot be skipped at this granularity.
    if padding.k_log < K_SKIP + N_INNER {
        return (0, vec![WINDOW as u8]);
    }
    let n_windows = 1usize << (padding.k_log - K_SKIP - N_INNER);
    let useful = padding.useful_bits_per_block;
    let counts = (0..n_windows)
        .map(|w| {
            let start = w * STRIDE;
            if start >= useful {
                0u8
            } else {
                (useful - start).div_ceil(POS_BITS).min(WINDOW) as u8
            }
        })
        .collect();
    (n_windows - 1, counts)
}

/// The round-1 prover message: the AB and C Λ-vectors, which the caller sends
/// as one sum.
#[allow(clippy::too_many_arguments)]
pub fn round1_message_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
    padding: &PaddingSpec,
) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(k_skip, K_SKIP, "round 1 is k_skip=6 only");
    assert!(
        m >= k_skip + N_INNER,
        "m must be ≥ k_skip + N_INNER ({})",
        k_skip + N_INNER
    );
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r_rest.len(), m - k_skip);
    assert_eq!(inv_table.k, k_skip);

    let (ab_tab, c_tab) = build_tables(&build_eq(&r_rest[..N_INNER]));
    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let (within_mask, pos_counts) = build_position_counts(padding);

    let state = parallel::fold_reduce(
        1usize << eq.n_hi,
        WorkerState::new,
        |state, x_hi| {
            process_one_x_hi(
                x_hi,
                1usize << eq.n_lo,
                eq.n_lo,
                within_mask,
                &pos_counts,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                &eq.lo,
                eq.hi[x_hi],
                &ab_tab,
                &c_tab,
                state,
            );
        },
        |mut a, b| {
            for lane in 0..ELL {
                a.res_ab[lane] += b.res_ab[lane];
                a.res_c_s[lane] += b.res_c_s[lane];
            }
            a
        },
    );

    let res_c_lifted = ntt_extend_vec(&state.res_c_s, inv_table);
    (state.res_ab.to_vec(), res_c_lifted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zerocheck::univariate_skip::{pack_bits, round1_naive};
    use pcs::ntt::AdditiveNttGf8;
    use primitives::test_rng::Rng;

    fn make_inv_table() -> InvNttTableByteSingleGf8 {
        let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
        InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l)
    }

    /// The message must equal the protocol formula exactly: no scaling factor
    /// survives now that the equality point is uniform.
    #[test]
    fn matches_naive() {
        for &m in &[10usize, 11, 13, 14, 15] {
            let mut rng = Rng::new(100 + m as u64);
            let (a, b, c) = (rng.bits(1 << m), rng.bits(1 << m), rng.bits(1 << m));
            let r = rng.ext_vec(m - K_SKIP);
            let table = make_inv_table();

            let (naive_ab, naive_c) = round1_naive(&a, &b, &c, m, K_SKIP, &r);
            let (ab, c_out) = round1_message_packed_padded(
                &pack_bits(&a),
                &pack_bits(&b),
                &pack_bits(&c),
                m,
                K_SKIP,
                &r,
                &table,
                &PaddingSpec::dense(m),
            );
            assert_eq!(naive_ab, ab, "AB mismatch at m={m}");
            assert_eq!(naive_c, c_out, "C mismatch at m={m}");
        }
    }

    /// Skipping the zero padding must be byte-identical to walking it: every
    /// position it drops would have contributed a literal zero.
    #[test]
    fn padded_matches_dense_with_zero_padding() {
        // (k_log, useful_bits, n_blocks_log), the supported hash padding shapes
        // plus one multi-block case.
        let cases = [
            (14usize, 16_000usize, 0usize),
            (15, 31_401, 0),
            (16, 42_560, 0),
            (16, 42_560, 3),
        ];

        for (k_log, useful_bits, n_blocks_log) in cases {
            let m = k_log + n_blocks_log;
            let mut rng = Rng::new(0xBEEF_DEAD_u64.wrapping_add((k_log * 31 + m) as u64));
            let block_size = 1usize << k_log;

            let mut bits = |n: usize| {
                let mut v = rng.bits(n);
                for blk in 0..(1usize << n_blocks_log) {
                    v[blk * block_size + useful_bits..(blk + 1) * block_size].fill(false);
                }
                pack_bits(&v)
            };
            let (a_p, b_p, c_p) = (bits(1 << m), bits(1 << m), bits(1 << m));
            let r = rng.ext_vec(m - K_SKIP);
            let table = make_inv_table();

            let run = |p: &PaddingSpec| round1_message_packed_padded(&a_p, &b_p, &c_p, m, K_SKIP, &r, &table, p);
            let dense = run(&PaddingSpec::dense(m));
            let padded = run(&PaddingSpec {
                k_log,
                useful_bits_per_block: useful_bits,
            });
            assert_eq!(dense, padded, "k_log={k_log}, useful={useful_bits}, m={m}");
        }
    }
}
