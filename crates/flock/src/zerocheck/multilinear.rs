// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Multilinear sumcheck: rounds 2..(m − k_skip + 1) of the zerocheck protocol.
//!
//! After the round-1 URM and the verifier's univariate-skip fold-point `z`, the
//! protocol enters a standard multilinear sumcheck over `n = m − k_skip`
//! variables, on the whole R1CS polynomial:
//!
//!   `Σ_x eq(r_rest, x) · (a_mlv(x) · b_mlv(x) + c_mlv(x))`
//!
//! with claim `P(z)` from round 1. The quadratic AB part and the linear C part
//! ride the same rounds, so all three claims land at one point; each round
//! sends `(P_r(1), P_r(∞))` via the Karatsuba ∞-trick, with C contributing to
//! `P_r(1)` only.
//!
//! This module holds both the **naive references** (separate Lagrange-weighted
//! fold, then a direct sum for the round-2 message) and the optimized fused
//! fold-plus-round-2 implementations, cross-checked against each other in
//! tests.
//!
//! **Index convention** (matches the C++ extract_c pipeline's `sumcheck_round_pair`
//! and the NEON `fold_in_place_pair`): the **low bit** of the multilinear index
//! is bound first. So `a_mlv[2k]` is the X=0 value and `a_mlv[2k+1]` is the X=1
//! value, paired by the round message and the fold.
//!
//! For `[r_0, …, r_{n-1}]` (one eq challenge per multilinear variable, built so
//! `build_eq` places `r_i` at bit i), **round r=2 binds the variable of `r_0`**
//! and takes eq over `r_1..` for the remaining variables. Subsequent rounds peel
//! off one more.
//!
//! **Round message format**: the kernels return `(G(1), G(∞))`, which is what
//! goes on the wire. The protocol polynomial is `Π(X) = eq(r_now, X) · G(X)` of
//! degree 3, for `r_now` the challenge of the variable bound this round; the
//! verifier reconstructs `G(0)` from the running claim via
//! `current_claim = (1+r_now)·G(0) + r_now·G(1)`.

use crate::zerocheck::PaddingSpec;
#[cfg(test)]
use crate::zerocheck::univariate_skip::pack_bits;
use crate::zerocheck::univariate_skip::{SplitEq, build_eq};
use primitives::field::{F192, F192Unreduced, PHI_8_TABLE_192 as PHI_8_TABLE};
use primitives::stream::Stream;
use zk_alloc::ArenaVec;

/// Four independent products. Tuples keep the scalar and NEON paths in registers, while AVX-512 uses the batched helper.
#[inline(always)]
fn mul_quad(a: (F192, F192, F192, F192), b: (F192, F192, F192, F192)) -> (F192, F192, F192, F192) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let r = primitives::field::mul4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    (a.0 * b.0, a.1 * b.1, a.2 * b.2, a.3 * b.3)
}

/// [`mul_quad`] without the reduction, for a caller XOR-accumulating products.
#[inline(always)]
fn mul_quad_unreduced(
    a: (F192, F192, F192, F192),
    b: (F192, F192, F192, F192),
) -> (F192Unreduced, F192Unreduced, F192Unreduced, F192Unreduced) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let r = primitives::field::mul_unreduced4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    (
        a.0.mul_unreduced(b.0),
        a.1.mul_unreduced(b.1),
        a.2.mul_unreduced(b.2),
        a.3.mul_unreduced(b.3),
    )
}

/// Returns `(pair_in_block_mask, useful_pairs_inclusive)` for the round-2
/// fused-fold kernel. A pair (post-URM chunks `2k`, `2k+1`) is fully inside
/// padding iff `(k & pair_in_block_mask) >= useful_pairs_inclusive`: those
/// pairs contribute zero to both the message and the folded output (which is
/// already zero-initialized), so the kernel can `continue` past them.
///
/// `useful_pairs_inclusive` is the index AFTER the last pair that has any
/// useful chunk. The boundary "mixed" pair (one useful + one padding chunk,
/// when `useful_bits` is odd in chunk units) is INSIDE the useful range and
/// processed normally: its padding side has value 0 so the message
/// contribution is naturally correct.
fn round2_pair_skip(padding: &PaddingSpec, k_skip: usize) -> (usize, usize) {
    if padding.k_log <= k_skip + 1 {
        return (0, usize::MAX);
    }
    let pairs_per_block = 1usize << (padding.k_log - k_skip - 1);
    let chunk_bits = 1usize << k_skip;
    let useful_pairs = padding.useful_bits_per_block.div_ceil(2 * chunk_bits);
    if useful_pairs >= pairs_per_block {
        return (0, usize::MAX);
    }
    (pairs_per_block - 1, useful_pairs)
}

// ---------------------------------------------------------------------------
// Lagrange weights for the univariate-skip fold at z.
// ---------------------------------------------------------------------------

use primitives::multilinear::lagrange_weights_naive;

/// Interpolate a degree-`< 2^k_skip` polynomial at z, given its `2^k_skip`
/// evaluations on the **extension domain** `Λ = {2^k_skip, …, 2^(k_skip+1) − 1}`
/// embedded via `φ_8` (offset by `2^k_skip` from the S-domain nodes).
///
/// `P^C` no longer travels on its own (it rides the sum the prover sends), so
/// this is only the cross-check handle: it turns the URM kernel's C Λ-vector
/// into `P^C(z) = ĉ(z, r_rest)`, which a direct fold of the witness must match.
pub fn interpolate_at_z_on_lambda(values: &[F192], k_skip: usize, z: F192) -> F192 {
    let ell = 1usize << k_skip;
    assert_eq!(values.len(), ell);
    assert!(2 * ell <= 256, "Λ ∪ S must fit in F_8 (need k_skip ≤ 7)");
    primitives::multilinear::lagrange_eval(&PHI_8_TABLE[ell..2 * ell], values, z)
}

/// Interpolate a degree-`< 2·2^k_skip` polynomial at z, given its `2^k_skip`
/// evaluations on Λ and the assumption that it equals **zero on S**.
///
/// This is the verifier's round-1 reconstruction trick: for an honest prover
/// the combined polynomial `P = P^{AB} + P^C` satisfies `P(λ) = 0` for every
/// `λ ∈ S` (the zerocheck identity at S). Together with the `2^k_skip`
/// evaluations on Λ that the prover sends, that's `2·2^k_skip` evaluations -
/// enough to interpolate the degree-`< 2·2^k_skip` polynomial uniquely.
///
pub fn interpolate_at_z_combined(values_on_lambda: &[F192], k_skip: usize, z: F192) -> F192 {
    let ell = 1usize << k_skip;
    assert_eq!(values_on_lambda.len(), ell);
    assert!(2 * ell <= 256, "Λ ∪ S must fit in F_8 (need k_skip ≤ 7)");
    // The first `ell` nodes are S, where the polynomial is zero by assumption;
    // the Λ evaluations follow.
    let mut values = vec![F192::ZERO; 2 * ell];
    values[ell..].copy_from_slice(values_on_lambda);
    primitives::multilinear::lagrange_eval(&PHI_8_TABLE[..2 * ell], &values, z)
}

// ---------------------------------------------------------------------------
// Fold a Boolean witness at z.
// ---------------------------------------------------------------------------

/// Evaluate the univariate-skip polynomial at the fold point `z`, given the
/// precomputed Lagrange `weights`. Returns the multilinear extension table
/// `a_mlv` of length `2^(m − k_skip)` over F_{2^192}.
///
///   `a_mlv[x_rest] = Σ_s a(s, x_rest) · L_s(z)`
///
/// `a(s, x_rest)` is the witness bit at index `x_rest * 2^k_skip + s` (low
/// bits = skip variable, high bits = rest variables).
#[cfg(test)]
fn fold_at_z_naive(witness: &[bool], m: usize, k_skip: usize, weights: &[F192]) -> ArenaVec<F192> {
    assert!(k_skip <= m);
    let ell = 1usize << k_skip;
    let n_rest = 1usize << (m - k_skip);
    assert_eq!(witness.len(), 1usize << m);
    assert_eq!(weights.len(), ell);

    // SAFETY: the loop below writes every one of the `n_rest` slots.
    let mut folded = unsafe { ArenaVec::<F192>::uninitialized(n_rest) };
    for x_rest in 0..n_rest {
        let base = x_rest * ell;
        let mut acc = F192::ZERO;
        for s in 0..ell {
            if witness[base + s] {
                acc += weights[s];
            }
        }
        folded[x_rest] = acc;
    }
    folded
}

// ---------------------------------------------------------------------------
// Naive round-2 prover message (AB-pair multilinear sumcheck).
// ---------------------------------------------------------------------------

/// Single-table sibling of [`round_pair_naive`], for the linear `c` term:
/// `G_c(1) = Σ_{x'} eq(r_eq, x') · c_mlv(1, x')`. Linear, so no `G(∞)`.
pub fn round_single_naive(c_mlv: &[F192], r_eq: &[F192]) -> F192 {
    let n = c_mlv.len();
    assert!(n.is_power_of_two() && n >= 2);
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);
    let eq_remaining = build_eq(r_eq);
    let mut g_one = F192::ZERO;
    for (x_prime, &eq_x) in eq_remaining.iter().enumerate() {
        g_one += eq_x * c_mlv[2 * x_prime + 1];
    }
    g_one
}

/// Round-2 (and any subsequent round) prover message for the AB-pair
/// multilinear sumcheck.
///
/// Inputs:
/// - `a_mlv`, `b_mlv`: F192 vectors of length `2^n` for some `n ≥ 1`.
/// - `r_eq`: the eq challenges of the `n − 1` variables NOT bound this round.
///
/// Output: `(G(1), G(∞))` for the round polynomial `G(X) = Σ_{x'} eq(r_eq, x')
/// · a_mlv(X, x') · b_mlv(X, x')`, where `a_mlv(0, x') = a_mlv[2x']` and
/// `a_mlv(1, x') = a_mlv[2x' + 1]` (low bit bound).
pub fn round_pair_naive(a_mlv: &[F192], b_mlv: &[F192], r_eq: &[F192]) -> (F192, F192) {
    let n = a_mlv.len();
    assert_eq!(b_mlv.len(), n);
    assert!(n.is_power_of_two() && n >= 2);
    let half = n / 2;
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);

    let eq_remaining = build_eq(r_eq);
    assert_eq!(eq_remaining.len(), half);

    let mut g_one = F192::ZERO;
    let mut g_inf = F192::ZERO;
    for x_prime in 0..half {
        let a0 = a_mlv[2 * x_prime];
        let a1 = a_mlv[2 * x_prime + 1];
        let b0 = b_mlv[2 * x_prime];
        let b1 = b_mlv[2 * x_prime + 1];
        let eq_x = eq_remaining[x_prime];
        g_one += eq_x * a1 * b1;
        // Char-2: (a_1 − a_0)(b_1 − b_0) = (a_0 + a_1)(b_0 + b_1).
        g_inf += eq_x * (a0 + a1) * (b0 + b1);
    }
    (g_one, g_inf)
}

// ---------------------------------------------------------------------------
// Naive fused (fold at z + round-2 message) for AB-pair.
// ---------------------------------------------------------------------------

/// Naive fold (at the univariate-skip challenge `z`) of `a` and `b`, plus the
/// round-2 prover message on the resulting multilinear polynomials.
///
/// `mlv_eq` is of length `m − k_skip − 1`: the eq challenges of the multilinear
/// variables NOT bound in round 2.
///
/// This is the *unfused* reference: it computes the fold and the round-2
/// message in two separate passes. The optimized version (next) does both
/// in one pass through the witness.
///
/// Returns `(a_mlv, b_mlv, G(1), G(∞))`.
#[cfg(test)]
fn uni_skip_fold_and_round_pair_naive(
    a: &[bool],
    b: &[bool],
    m: usize,
    k_skip: usize,
    z: F192,
    mlv_eq: &[F192],
) -> (ArenaVec<F192>, ArenaVec<F192>, F192, F192) {
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert!(m > k_skip, "need at least one multilinear variable past the skip");
    assert_eq!(mlv_eq.len(), m - k_skip - 1);

    let weights = lagrange_weights_naive(k_skip, z);
    let a_mlv = fold_at_z_naive(a, m, k_skip, &weights);
    let b_mlv = fold_at_z_naive(b, m, k_skip, &weights);
    let (msg_1, msg_inf) = round_pair_naive(&a_mlv, &b_mlv, mlv_eq);
    (a_mlv, b_mlv, msg_1, msg_inf)
}

// ---------------------------------------------------------------------------
// Optimized fused fold + round-2 message.
// ---------------------------------------------------------------------------

/// Precomputed fold table for the univariate-skip fold at a fixed `z`.
///
/// Storage: `n_chunks × 256` F192 entries. For each
/// byte-chunk `j ∈ 0..n_chunks` and byte value `v ∈ 0..256`:
///
///   `data[j * 256 + v] = Σ_{b : bit b of v set} weights[8j + b]`
///
/// where `weights = lagrange_weights_naive(k_skip, z)`. Built incrementally by
/// XOR-composition over the set bits of `v` (one XOR per non-power-of-2 entry).
///
/// Per-row fold then becomes one table lookup + XOR per byte (n_chunks lookups
/// total instead of `ell` Lagrange multiplications).
#[derive(Clone, Debug)]
pub struct UniSkipFoldTable {
    pub n_chunks: usize,
    pub data: Vec<F192>,
}

impl UniSkipFoldTable {
    pub fn new(k_skip: usize, z: F192) -> Self {
        let ell = 1usize << k_skip;
        assert_eq!(ell % 8, 0, "k_skip must be ≥ 3 (need ell divisible by 8)");
        let n_chunks = ell / 8;
        let weights = lagrange_weights_naive(k_skip, z);

        let mut data = vec![F192::ZERO; n_chunks * 256];
        for j in 0..n_chunks {
            let basis = &weights[8 * j..8 * j + 8];
            // v = 0: zero (already initialized).
            for b in 0..8 {
                data[j * 256 + (1 << b)] = basis[b];
            }
            // Non-powers-of-2: composed by XOR of (v ^ lo_bit) and lo_bit entries.
            for v in 3usize..256 {
                if (v & (v - 1)) == 0 {
                    continue; // skip powers of 2 (already written)
                }
                let lo_bit = 1usize << v.trailing_zeros();
                let parent = v ^ lo_bit;
                data[j * 256 + v] = data[j * 256 + parent] + data[j * 256 + lo_bit];
            }
        }
        Self { n_chunks, data }
    }

    /// Scalar one-row fold: `Σ_j table[j][bytes[j]]`.
    #[inline]
    pub fn fold_one_row(&self, bytes: &[u8]) -> F192 {
        assert_eq!(bytes.len(), self.n_chunks);
        let mut acc = F192::ZERO;
        for j in 0..self.n_chunks {
            acc += self.data[j * 256 + bytes[j] as usize];
        }
        acc
    }
}

/// NEON one-row fold, hand-unrolled for `n_chunks = 8` (the k_skip=6 protocol
/// size). Each table entry is 24 bytes: NEON folds c0/c1 together while c2 is
/// folded in a scalar register.
///
/// # Safety
/// Caller must guarantee `table_data` points to ≥ 8 × 256 valid F192 entries
/// (an `n_chunks ≥ 8` table) and `bytes_ptr` to ≥ 8 valid bytes.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn fold_one_row_neon_unchecked_8(table_data: *const F192, bytes_ptr: *const u8) -> F192 {
    use core::arch::aarch64::*;
    unsafe {
        let first = &*table_data.add((*bytes_ptr) as usize);
        let mut acc = vld1q_u64(&first.c0);
        let mut c2 = first.c2;
        for chunk in 1..8 {
            let entry = &*table_data.add(chunk * 256 + (*bytes_ptr.add(chunk)) as usize);
            acc = veorq_u64(acc, vld1q_u64(&entry.c0));
            c2 ^= entry.c2;
        }
        F192 {
            c0: vgetq_lane_u64::<0>(acc),
            c1: vgetq_lane_u64::<1>(acc),
            c2,
        }
    }
}

/// The NEON kernel's x86 twin: same 128-bit fold of `(c0, c1)` with `c2` in a
/// scalar register, same unroll. Without it the innermost operation of both
/// round-two kernels, run once per post-URM row, is a bounds-checked loop with a
/// trip count the compiler cannot see.
///
/// # Safety
/// Caller must guarantee `table_data` points to >= 8 x 256 valid F192 entries
/// (an `n_chunks >= 8` table) and `bytes_ptr` to >= 8 valid bytes.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
unsafe fn fold_one_row_x86_unchecked_8(table_data: *const F192, bytes_ptr: *const u8) -> F192 {
    use core::arch::x86_64::*;
    unsafe {
        let entry = |chunk: usize| &*table_data.add(chunk * 256 + (*bytes_ptr.add(chunk)) as usize);
        let first = entry(0);
        // Reads `c0` and `c1`; an entry is three u64, so the pair is in bounds.
        let mut acc = _mm_loadu_si128((&raw const first.c0).cast());
        let mut c2 = first.c2;
        for chunk in 1..8 {
            let e = entry(chunk);
            acc = _mm_xor_si128(acc, _mm_loadu_si128((&raw const e.c0).cast()));
            c2 ^= e.c2;
        }
        F192 {
            c0: _mm_cvtsi128_si64(acc) as u64,
            c1: _mm_cvtsi128_si64(_mm_unpackhi_epi64(acc, acc)) as u64,
            c2,
        }
    }
}

/// Fold post-URM row `row` of `packed`: the vector kernel where one exists, the
/// scalar table lookup elsewhere. Requires an 8-chunk `table` (the k_skip=6
/// protocol size) and `row` within `packed`.
#[inline(always)]
fn fold_row(table: &UniSkipFoldTable, packed: &[u8], row: usize) -> F192 {
    // SAFETY (both arms): the table has 8 chunks and `row` addresses 8 in-bounds
    // bytes, both asserted by the caller.
    #[cfg(target_arch = "aarch64")]
    unsafe {
        fold_one_row_neon_unchecked_8(table.data.as_ptr(), packed.as_ptr().add(row * 8))
    }
    #[cfg(target_arch = "x86_64")]
    unsafe {
        fold_one_row_x86_unchecked_8(table.data.as_ptr(), packed.as_ptr().add(row * 8))
    }
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let n_chunks = table.n_chunks;
        table.fold_one_row(&packed[row * n_chunks..(row + 1) * n_chunks])
    }
}

/// Optimized fused fold (at the URM challenge `z`, baked into `table`) plus
/// round-2 prover message. **Packed input** (LSB-first bit packing). **Parallel
/// by default** via the `parallel` pool: the outer x_hi loop is distributed
/// across workers, each writing to a disjoint chunk of `a_folded`/`b_folded`
/// and accumulating its own `(sum1_contrib, sum_inf_contrib)`. The final
/// reduce sums the per-worker contributions (commutative + associative F192
/// XOR/multiply).
///
/// Algorithm (per worker, one x_hi):
/// 1. For each `(x0, x1) = (2k, 2k+1)` pair (k within this x_hi's range),
///    fold the four rows `a[x0], b[x0], a[x1], b[x1]` via the table.
/// 2. Accumulate `eq_lo · a1·b1` and `eq_lo · (a0+a1)·(b0+b1)` with deferred
///    256-bit reduction, reduced once at the end of the worker's x_lo loop.
/// 3. Outer fold by `eq.hi[x_hi]` into the worker's `(sum1_contrib, sum_inf_contrib)`.
///
/// Pairs whose post-URM chunk indices both fall in the per-block zero padding
/// are skipped: the fold output is zero and so is the message contribution.
///
/// Returns `(a_folded, b_folded, G(1), G(∞))`: same convention as
/// `uni_skip_fold_and_round_pair_naive`.
///
/// To run single-threaded for debugging, set `LEANVM_NUM_THREADS=1`.
///
/// `k_skip = 6` is currently hardcoded (the protocol headline).
pub fn uni_skip_fold_and_round_pair_optimized_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    m: usize,
    k_skip: usize,
    table: &UniSkipFoldTable,
    mlv_eq: &[F192],
    padding: &PaddingSpec,
) -> (ArenaVec<F192>, ArenaVec<F192>, F192, F192) {
    assert_eq!(k_skip, 6, "optimized fold-and-round_pair variant is k_skip=6 only");
    assert_eq!(table.n_chunks, 8);
    let n_chunks = table.n_chunks;
    let n_out = 1usize << (m - k_skip);
    assert_eq!(a_packed.len(), n_out * n_chunks);
    assert_eq!(b_packed.len(), n_out * n_chunks);
    assert_eq!(mlv_eq.len(), m - k_skip - 1);

    // SAFETY (x2): the parallel loop below writes every slot (including padding
    // holes), avoiding a separate clear.
    let mut a_folded = unsafe { ArenaVec::<F192>::uninitialized(n_out) };
    let mut b_folded = unsafe { ArenaVec::<F192>::uninitialized(n_out) };

    let eq = SplitEq::new(mlv_eq);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    assert_eq!(lo_size * hi_size * 2, n_out);

    let chunk_size = 2 * lo_size;
    let eq_hi = &eq.hi;
    let eq_lo = &eq.lo;
    let (pair_in_block_mask, useful_pairs_inclusive) = round2_pair_skip(padding, k_skip);

    // Parallel: each worker writes one disjoint chunk of a_folded/b_folded
    // and returns its (sum1, sum_inf) contribution. Reduce by F192 XOR.
    let a_chunks = parallel::Chunks::new(&mut a_folded, chunk_size);
    let b_chunks = parallel::Chunks::new(&mut b_folded, chunk_size);
    let (sum1, sum_inf) = parallel::map_reduce(
        a_chunks.count(),
        || (F192::ZERO, F192::ZERO),
        |x_hi| {
            // SAFETY: `x_hi` takes chunk `x_hi` of each output exactly once, and
            // both buffers stay borrowed for the whole dispatch.
            let (a_chunk, b_chunk) = unsafe { (a_chunks.get(x_hi), b_chunks.get(x_hi)) };
            {
                let mut p1_acc = F192Unreduced::ZERO;
                let mut pinf_acc = F192Unreduced::ZERO;
                let pair_idx_base = x_hi * lo_size;
                let base = x_hi * chunk_size;

                // Four x_lo per iteration: the message's eight products go to
                // two quads and the eight outputs are one streaming publish. A
                // padding hole folds to zero and contributes nothing, so it costs
                // no branch of its own beyond skipping its rows.
                let stream = Stream::new();
                let live = |x_lo: usize| ((pair_idx_base + x_lo) & pair_in_block_mask) < useful_pairs_inclusive;
                let read = |x_lo: usize| -> (F192, F192, F192, F192) {
                    if live(x_lo) {
                        let x0g = base + 2 * x_lo;
                        (
                            fold_row(table, a_packed, x0g),
                            fold_row(table, a_packed, x0g + 1),
                            fold_row(table, b_packed, x0g),
                            fold_row(table, b_packed, x0g + 1),
                        )
                    } else {
                        (F192::ZERO, F192::ZERO, F192::ZERO, F192::ZERO)
                    }
                };
                let mut x_lo = 0;
                while x_lo + 4 <= lo_size {
                    let (a0_a, a1_a, b0_a, b1_a) = read(x_lo);
                    let (a0_b, a1_b, b0_b, b1_b) = read(x_lo + 1);
                    let (a0_c, a1_c, b0_c, b1_c) = read(x_lo + 2);
                    let (a0_d, a1_d, b0_d, b1_d) = read(x_lo + 3);

                    let (g1_a, g1_b, g1_c, g1_d) = mul_quad((a1_a, a1_b, a1_c, a1_d), (b1_a, b1_b, b1_c, b1_d));
                    let (gi_a, gi_b, gi_c, gi_d) = mul_quad(
                        (a0_a + a1_a, a0_b + a1_b, a0_c + a1_c, a0_d + a1_d),
                        (b0_a + b1_a, b0_b + b1_b, b0_c + b1_c, b0_d + b1_d),
                    );
                    let eq_q = (eq_lo[x_lo], eq_lo[x_lo + 1], eq_lo[x_lo + 2], eq_lo[x_lo + 3]);
                    let (t1_a, t1_b, t1_c, t1_d) = mul_quad_unreduced(eq_q, (g1_a, g1_b, g1_c, g1_d));
                    let (ti_a, ti_b, ti_c, ti_d) = mul_quad_unreduced(eq_q, (gi_a, gi_b, gi_c, gi_d));
                    p1_acc ^= t1_a;
                    p1_acc ^= t1_b;
                    p1_acc ^= t1_c;
                    p1_acc ^= t1_d;
                    pinf_acc ^= ti_a;
                    pinf_acc ^= ti_b;
                    pinf_acc ^= ti_c;
                    pinf_acc ^= ti_d;

                    let oi = 2 * x_lo;
                    stream.copy(
                        &mut a_chunk[oi..oi + 8],
                        &[a0_a, a1_a, a0_b, a1_b, a0_c, a1_c, a0_d, a1_d],
                    );
                    stream.copy(
                        &mut b_chunk[oi..oi + 8],
                        &[b0_a, b1_a, b0_b, b1_b, b0_c, b1_c, b0_d, b1_d],
                    );
                    x_lo += 4;
                }
                // `lo_size` is a power of two, so this runs only below the unroll
                // width, at the smallest rounds.
                while x_lo < lo_size {
                    let (a0, a1, b0, b1) = read(x_lo);
                    let eq_l = eq_lo[x_lo];
                    p1_acc ^= eq_l.mul_unreduced(a1 * b1);
                    pinf_acc ^= eq_l.mul_unreduced((a0 + a1) * (b0 + b1));
                    let oi = 2 * x_lo;
                    a_chunk[oi] = a0;
                    a_chunk[oi + 1] = a1;
                    b_chunk[oi] = b0;
                    b_chunk[oi + 1] = b1;
                    x_lo += 1;
                }

                let p1 = p1_acc.reduce();
                let pinf = pinf_acc.reduce();
                let eq_h = eq_hi[x_hi];
                (eq_h * p1, eq_h * pinf)
            }
        },
        |(s1, sinf), (c1, cinf)| (s1 + c1, sinf + cinf),
    );

    (a_folded, b_folded, sum1, sum_inf)
}

/// Single-table sibling of [`uni_skip_fold_and_round_pair_optimized_packed_padded`],
/// for the linear `c` term of the combined zerocheck polynomial. Same fold,
/// same padding skip, same parallel decomposition; the message is just
/// `G_c(1) = Σ_{x'} eq(mlv_eq, x') · c_folded(1, x')`, since a linear term has
/// no `G(∞)`.
pub fn uni_skip_fold_and_round_single_optimized_packed_padded(
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    table: &UniSkipFoldTable,
    mlv_eq: &[F192],
    padding: &PaddingSpec,
) -> (ArenaVec<F192>, F192) {
    assert_eq!(k_skip, 6, "optimized fold-and-round_single variant is k_skip=6 only");
    assert_eq!(table.n_chunks, 8);
    let n_out = 1usize << (m - k_skip);
    assert_eq!(c_packed.len(), n_out * table.n_chunks);
    assert_eq!(mlv_eq.len(), m - k_skip - 1);

    // SAFETY: the parallel loop below writes every slot (padding holes included).
    let mut c_folded = unsafe { ArenaVec::<F192>::uninitialized(n_out) };

    let eq = SplitEq::new(mlv_eq);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    assert_eq!(lo_size * hi_size * 2, n_out);

    let chunk_size = 2 * lo_size;
    let eq_hi = &eq.hi;
    let eq_lo = &eq.lo;
    let (pair_in_block_mask, useful_pairs_inclusive) = round2_pair_skip(padding, k_skip);

    let c_chunks = parallel::Chunks::new(&mut c_folded, chunk_size);
    let sum1 = parallel::map_reduce(
        c_chunks.count(),
        || F192::ZERO,
        |x_hi| {
            // SAFETY: `x_hi` takes chunk `x_hi` exactly once, and the buffer
            // stays borrowed for the whole dispatch.
            let c_chunk = unsafe { c_chunks.get(x_hi) };
            let mut p1_acc = F192Unreduced::ZERO;
            let pair_idx_base = x_hi * lo_size;
            let base = x_hi * chunk_size;

            // Four x_lo per iteration; see the pair kernel.
            let stream = Stream::new();
            let live = |x_lo: usize| ((pair_idx_base + x_lo) & pair_in_block_mask) < useful_pairs_inclusive;
            let read = |x_lo: usize| -> (F192, F192) {
                if live(x_lo) {
                    let x0g = base + 2 * x_lo;
                    (fold_row(table, c_packed, x0g), fold_row(table, c_packed, x0g + 1))
                } else {
                    (F192::ZERO, F192::ZERO)
                }
            };
            let mut x_lo = 0;
            while x_lo + 4 <= lo_size {
                let (c0_a, c1_a) = read(x_lo);
                let (c0_b, c1_b) = read(x_lo + 1);
                let (c0_c, c1_c) = read(x_lo + 2);
                let (c0_d, c1_d) = read(x_lo + 3);
                let eq_q = (eq_lo[x_lo], eq_lo[x_lo + 1], eq_lo[x_lo + 2], eq_lo[x_lo + 3]);
                let (t_a, t_b, t_c, t_d) = mul_quad_unreduced(eq_q, (c1_a, c1_b, c1_c, c1_d));
                p1_acc ^= t_a;
                p1_acc ^= t_b;
                p1_acc ^= t_c;
                p1_acc ^= t_d;
                let oi = 2 * x_lo;
                stream.copy(
                    &mut c_chunk[oi..oi + 8],
                    &[c0_a, c1_a, c0_b, c1_b, c0_c, c1_c, c0_d, c1_d],
                );
                x_lo += 4;
            }
            while x_lo < lo_size {
                let (c0, c1) = read(x_lo);
                p1_acc ^= eq_lo[x_lo].mul_unreduced(c1);
                let oi = 2 * x_lo;
                c_chunk[oi] = c0;
                c_chunk[oi + 1] = c1;
                x_lo += 1;
            }
            eq_hi[x_hi] * p1_acc.reduce()
        },
        |a, b| a + b,
    );

    (c_folded, sum1)
}

// ---------------------------------------------------------------------------
// Subsequent multilinear rounds (3..(m−k_skip+1)): fold + next message.
// ---------------------------------------------------------------------------

/// In-place fold of a single multilinear polynomial table at `challenge`.
/// Pairs `(a[2x], a[2x+1])` collapse to `a[x] = a[2x] + challenge · (a[2x+1] + a[2x])`.
/// After the call, `a.len()` is halved.
pub fn fold_in_place_single(a: &mut ArenaVec<F192>, challenge: F192) {
    let n = a.len();
    assert!(n.is_power_of_two() && n >= 2);
    let half = n / 2;
    for x in 0..half {
        let a0 = a[2 * x];
        let a1 = a[2 * x + 1];
        a[x] = a0 + challenge * (a1 + a0);
    }
    a.truncate(half);
}

/// In-place fold of a pair `(a, b)` of multilinear polynomial tables at
/// `challenge`. Binds the lowest bit of the index: pairs `(a[2x], a[2x+1])`
/// collapse to `a[x] = a[2x] + challenge · (a[2x+1] + a[2x])` (and same for b).
/// After the call, `a.len()` and `b.len()` are halved.
///
/// Used at the tail of the multilinear-round sequence where the polynomial is
/// small enough that parallel/fusion overhead outweighs benefit.
pub fn fold_in_place_pair(a: &mut ArenaVec<F192>, b: &mut ArenaVec<F192>, challenge: F192) {
    let n = a.len();
    assert_eq!(b.len(), n);
    assert!(n.is_power_of_two() && n >= 2);
    let half = n / 2;
    for x in 0..half {
        let a0 = a[2 * x];
        let a1 = a[2 * x + 1];
        let b0 = b[2 * x];
        let b1 = b[2 * x + 1];
        a[x] = a0 + challenge * (a1 + a0);
        b[x] = b0 + challenge * (b1 + b0);
    }
    a.truncate(half);
    b.truncate(half);
}

/// Single-table sibling of [`fold_and_compute_round_pair_into`], for the linear
/// `c` term: binds one variable at `r_fold` into `c_out` and returns the next
/// round's `G_c(1)`. Same chunking as the pair kernel, so the two dispatches
/// walk the same index layout.
pub fn fold_and_compute_round_single_into(c: &[F192], c_out: &mut [F192], r_fold: F192, r_eq: &[F192]) -> F192 {
    let n = c.len();
    assert!(n.is_power_of_two() && n >= 8);
    let half = n / 2;
    assert_eq!(c_out.len(), half);
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 2);

    let eq = SplitEq::new(r_eq);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    assert!(lo_size >= 2, "fold_and_compute requires lo_size ≥ 2");
    assert_eq!(lo_size * hi_size * 2, half);

    let chunk_in = 4 * lo_size;
    let chunk_out = 2 * lo_size;
    let eq_lo = &eq.lo;
    let eq_hi = &eq.hi;

    let c_chunks = parallel::Chunks::new(c_out, chunk_out);
    parallel::map_reduce(
        c_chunks.count(),
        || F192::ZERO,
        |x_hi| {
            // SAFETY: `x_hi` takes chunk `x_hi` exactly once, and the buffer
            // stays borrowed for the whole dispatch.
            let c_out = unsafe { c_chunks.get(x_hi) };
            let c_in = &c[x_hi * chunk_in..(x_hi + 1) * chunk_in];
            let mut p1_acc = F192Unreduced::ZERO;
            // Four x_lo per iteration, as in the pair kernel; see there for why
            // the outputs stream.
            let stream = Stream::new();
            let mut x_lo = 0;
            while x_lo + 4 <= lo_size {
                let ci = 4 * x_lo;
                let g = |j: usize, k: usize| c_in[ci + 4 * j + k];
                let rf = (r_fold, r_fold, r_fold, r_fold);
                let (d_a0, d_a1, d_b0, d_b1) = mul_quad(
                    (
                        g(0, 1) + g(0, 0),
                        g(0, 3) + g(0, 2),
                        g(1, 1) + g(1, 0),
                        g(1, 3) + g(1, 2),
                    ),
                    rf,
                );
                let (d_c0, d_c1, d_d0, d_d1) = mul_quad(
                    (
                        g(2, 1) + g(2, 0),
                        g(2, 3) + g(2, 2),
                        g(3, 1) + g(3, 0),
                        g(3, 3) + g(3, 2),
                    ),
                    rf,
                );
                let (c0_a, c1_a) = (g(0, 0) + d_a0, g(0, 2) + d_a1);
                let (c0_b, c1_b) = (g(1, 0) + d_b0, g(1, 2) + d_b1);
                let (c0_c, c1_c) = (g(2, 0) + d_c0, g(2, 2) + d_c1);
                let (c0_d, c1_d) = (g(3, 0) + d_d0, g(3, 2) + d_d1);

                let eq_q = (eq_lo[x_lo], eq_lo[x_lo + 1], eq_lo[x_lo + 2], eq_lo[x_lo + 3]);
                let (t_a, t_b, t_c, t_d) = mul_quad_unreduced(eq_q, (c1_a, c1_b, c1_c, c1_d));
                p1_acc ^= t_a;
                p1_acc ^= t_b;
                p1_acc ^= t_c;
                p1_acc ^= t_d;

                let oi = 2 * x_lo;
                stream.copy(
                    &mut c_out[oi..oi + 8],
                    &[c0_a, c1_a, c0_b, c1_b, c0_c, c1_c, c0_d, c1_d],
                );
                x_lo += 4;
            }
            // Scalar tail; see the pair kernel.
            while x_lo < lo_size {
                let ci = 4 * x_lo;
                let c0 = c_in[ci] + r_fold * (c_in[ci + 1] + c_in[ci]);
                let c1 = c_in[ci + 2] + r_fold * (c_in[ci + 3] + c_in[ci + 2]);
                let oi = 2 * x_lo;
                c_out[oi] = c0;
                c_out[oi + 1] = c1;
                p1_acc ^= eq_lo[x_lo].mul_unreduced(c1);
                x_lo += 1;
            }
            eq_hi[x_hi] * p1_acc.reduce()
        },
        |a, b| a + b,
    )
}

/// Fused: bind one variable at `r_fold` AND compute the *next* round's prover
/// message, writing the folded `a`/`b` into the caller-provided `a_out`/`b_out`
/// (each length `a.len() / 2`). Returns `(G(1), G(∞))`, with `r_eq` the eq
/// challenges of the variables the next round does NOT bind.
///
/// Parallelized via the `parallel` pool: each worker reads one disjoint
/// 4·lo_size chunk of the input and writes the corresponding 2·lo_size chunk of
/// the output.
///
/// Writing into caller buffers lets the multilinear-sumcheck tail ping-pong
/// between persistent scratch buffers (one per folded table, three since `c`
/// joined the sumcheck), so the decreasing-size buffers are allocated/freed
/// once rather than per round, avoiding serial unmaps in the sumcheck tail.
///
/// Requires `a.len() = b.len() ≥ 8` so the post-fold polynomial has at least
/// one bit of x_lo (lo_size ≥ 2). Smaller polynomials should use the
/// unfused `fold_in_place_pair + round_pair_naive` pair.
pub fn fold_and_compute_round_pair_into(
    a: &[F192],
    b: &[F192],
    a_out: &mut [F192],
    b_out: &mut [F192],
    r_fold: F192,
    r_eq: &[F192],
) -> (F192, F192) {
    let n = a.len();
    assert_eq!(b.len(), n);
    assert!(n.is_power_of_two() && n >= 8);
    let half = n / 2;
    assert_eq!(a_out.len(), half);
    assert_eq!(b_out.len(), half);
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 2);

    let eq = SplitEq::new(r_eq);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    assert!(lo_size >= 2, "fold_and_compute requires lo_size ≥ 2");
    // Total non-bound multilinear vars is log_n - 1; eq covers log_n - 2 of those.
    assert_eq!(lo_size * hi_size * 2, half);

    let chunk_in = 4 * lo_size; // read chunk per worker
    let chunk_out = 2 * lo_size; // write chunk per worker
    let eq_lo = &eq.lo;
    let eq_hi = &eq.hi;

    let a_chunks = parallel::Chunks::new(a_out, chunk_out);
    let b_chunks = parallel::Chunks::new(b_out, chunk_out);
    let (sum1, sum_inf) = parallel::map_reduce(
        a_chunks.count(),
        || (F192::ZERO, F192::ZERO),
        |x_hi| {
            // SAFETY: `x_hi` takes chunk `x_hi` of each output exactly once, and
            // both buffers stay borrowed for the whole dispatch.
            let (a_out, b_out) = unsafe { (a_chunks.get(x_hi), b_chunks.get(x_hi)) };
            let a_in = &a[x_hi * chunk_in..(x_hi + 1) * chunk_in];
            let b_in = &b[x_hi * chunk_in..(x_hi + 1) * chunk_in];

            let mut p1_acc = F192Unreduced::ZERO;
            let mut pinf_acc = F192Unreduced::ZERO;
            // The message is built from the folded values while they are still
            // in registers, so nothing reads `a_out`/`b_out` until the next
            // round, by which time a buffer this size is long evicted.
            let stream = Stream::new();

            // Unroll 4 x_lo's per iteration when lo_size % 4 == 0 (the common
            // case for the fused path; falls back to 2-wide for lo_size==2 at
            // the smallest fused round). This keeps independent products in flight.
            let mut x_lo = 0;
            if lo_size.is_multiple_of(4) {
                while x_lo + 4 <= lo_size {
                    let x_lo_a = x_lo;
                    let x_lo_b = x_lo + 1;
                    let x_lo_c = x_lo + 2;
                    let x_lo_d = x_lo + 3;
                    let ai_a = 4 * x_lo_a;
                    let ai_b = 4 * x_lo_b;
                    let ai_c = 4 * x_lo_c;
                    let ai_d = 4 * x_lo_d;

                    let aa0_a = a_in[ai_a];
                    let aa1_a = a_in[ai_a + 1];
                    let aa2_a = a_in[ai_a + 2];
                    let aa3_a = a_in[ai_a + 3];
                    let bb0_a = b_in[ai_a];
                    let bb1_a = b_in[ai_a + 1];
                    let bb2_a = b_in[ai_a + 2];
                    let bb3_a = b_in[ai_a + 3];
                    let aa0_b = a_in[ai_b];
                    let aa1_b = a_in[ai_b + 1];
                    let aa2_b = a_in[ai_b + 2];
                    let aa3_b = a_in[ai_b + 3];
                    let bb0_b = b_in[ai_b];
                    let bb1_b = b_in[ai_b + 1];
                    let bb2_b = b_in[ai_b + 2];
                    let bb3_b = b_in[ai_b + 3];
                    let aa0_c = a_in[ai_c];
                    let aa1_c = a_in[ai_c + 1];
                    let aa2_c = a_in[ai_c + 2];
                    let aa3_c = a_in[ai_c + 3];
                    let bb0_c = b_in[ai_c];
                    let bb1_c = b_in[ai_c + 1];
                    let bb2_c = b_in[ai_c + 2];
                    let bb3_c = b_in[ai_c + 3];
                    let aa0_d = a_in[ai_d];
                    let aa1_d = a_in[ai_d + 1];
                    let aa2_d = a_in[ai_d + 2];
                    let aa3_d = a_in[ai_d + 3];
                    let bb0_d = b_in[ai_d];
                    let bb1_d = b_in[ai_d + 1];
                    let bb2_d = b_in[ai_d + 2];
                    let bb3_d = b_in[ai_d + 3];

                    // 16 independent r_fold muls, four to a quad.
                    let rf = (r_fold, r_fold, r_fold, r_fold);
                    let (f0_a, f1_a, f2_a, f3_a) =
                        mul_quad((aa1_a + aa0_a, aa3_a + aa2_a, bb1_a + bb0_a, bb3_a + bb2_a), rf);
                    let (f0_b, f1_b, f2_b, f3_b) =
                        mul_quad((aa1_b + aa0_b, aa3_b + aa2_b, bb1_b + bb0_b, bb3_b + bb2_b), rf);
                    let (f0_c, f1_c, f2_c, f3_c) =
                        mul_quad((aa1_c + aa0_c, aa3_c + aa2_c, bb1_c + bb0_c, bb3_c + bb2_c), rf);
                    let (f0_d, f1_d, f2_d, f3_d) =
                        mul_quad((aa1_d + aa0_d, aa3_d + aa2_d, bb1_d + bb0_d, bb3_d + bb2_d), rf);
                    let (a0_a, a1_a, b0_a, b1_a) = (aa0_a + f0_a, aa2_a + f1_a, bb0_a + f2_a, bb2_a + f3_a);
                    let (a0_b, a1_b, b0_b, b1_b) = (aa0_b + f0_b, aa2_b + f1_b, bb0_b + f2_b, bb2_b + f3_b);
                    let (a0_c, a1_c, b0_c, b1_c) = (aa0_c + f0_c, aa2_c + f1_c, bb0_c + f2_c, bb2_c + f3_c);
                    let (a0_d, a1_d, b0_d, b1_d) = (aa0_d + f0_d, aa2_d + f1_d, bb0_d + f2_d, bb2_d + f3_d);

                    // Eight consecutive outputs are 192 bytes, three whole cache
                    // lines: the unrolled group is exactly a streaming publish.
                    let oi = 2 * x_lo_a;
                    stream.copy(
                        &mut a_out[oi..oi + 8],
                        &[a0_a, a1_a, a0_b, a1_b, a0_c, a1_c, a0_d, a1_d],
                    );
                    stream.copy(
                        &mut b_out[oi..oi + 8],
                        &[b0_a, b1_a, b0_b, b1_b, b0_c, b1_c, b0_d, b1_d],
                    );

                    // 8 independent msg muls.
                    let eq_l_a = eq_lo[x_lo_a];
                    let eq_l_b = eq_lo[x_lo_b];
                    let eq_l_c = eq_lo[x_lo_c];
                    let eq_l_d = eq_lo[x_lo_d];
                    let (g1_a, g1_b, g1_c, g1_d) = mul_quad((a1_a, a1_b, a1_c, a1_d), (b1_a, b1_b, b1_c, b1_d));
                    let (g_inf_a, g_inf_b, g_inf_c, g_inf_d) = mul_quad(
                        (a0_a + a1_a, a0_b + a1_b, a0_c + a1_c, a0_d + a1_d),
                        (b0_a + b1_a, b0_b + b1_b, b0_c + b1_c, b0_d + b1_d),
                    );
                    let eq_q = (eq_l_a, eq_l_b, eq_l_c, eq_l_d);
                    let (t1_a, t1_b, t1_c, t1_d) = mul_quad_unreduced(eq_q, (g1_a, g1_b, g1_c, g1_d));
                    let (ti_a, ti_b, ti_c, ti_d) = mul_quad_unreduced(eq_q, (g_inf_a, g_inf_b, g_inf_c, g_inf_d));
                    p1_acc ^= t1_a;
                    p1_acc ^= t1_b;
                    p1_acc ^= t1_c;
                    p1_acc ^= t1_d;
                    pinf_acc ^= ti_a;
                    pinf_acc ^= ti_b;
                    pinf_acc ^= ti_c;
                    pinf_acc ^= ti_d;

                    x_lo += 4;
                }
            }
            // Scalar tail. `lo_size` is a power of two, so this runs only at
            // `lo_size == 2` (the smallest fused round, at most twice per
            // proof), where the unrolled ILP would buy nothing.
            while x_lo < lo_size {
                let ai = 4 * x_lo;
                let a0 = a_in[ai] + r_fold * (a_in[ai + 1] + a_in[ai]);
                let a1 = a_in[ai + 2] + r_fold * (a_in[ai + 3] + a_in[ai + 2]);
                let b0 = b_in[ai] + r_fold * (b_in[ai + 1] + b_in[ai]);
                let b1 = b_in[ai + 2] + r_fold * (b_in[ai + 3] + b_in[ai + 2]);

                let oi = 2 * x_lo;
                a_out[oi] = a0;
                a_out[oi + 1] = a1;
                b_out[oi] = b0;
                b_out[oi + 1] = b1;

                let eq_l = eq_lo[x_lo];
                p1_acc ^= eq_l.mul_unreduced(a1 * b1);
                pinf_acc ^= eq_l.mul_unreduced((a0 + a1) * (b0 + b1));

                x_lo += 1;
            }

            let p1 = p1_acc.reduce();
            let pinf = pinf_acc.reduce();
            let eq_h = eq_hi[x_hi];
            (eq_h * p1, eq_h * pinf)
        },
        |(s1, sinf), (c1, cinf)| (s1 + c1, sinf + cinf),
    );

    (sum1, sum_inf)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Whichever `fold_row` kernel this target reaches, against the scalar table
    /// lookup. The vector arms are unchecked and hand-unrolled for eight chunks,
    /// so this is what stands between a mispaired chunk and a wrong proof.
    #[test]
    fn fold_row_matches_scalar() {
        let mut rng = Rng::new(70);
        let table = UniSkipFoldTable::new(6, rng.ext());
        for _ in 0..256 {
            let bytes: [u8; 8] = std::array::from_fn(|_| (rng.next_u64() & 0xff) as u8);
            assert_eq!(
                table.fold_one_row(&bytes),
                fold_row(&table, &bytes, 0),
                "bytes={bytes:02x?}"
            );
        }
    }

    /// `fold_in_place_pair` correctness: post-fold a[x] = a[2x] + X·(a[2x+1]+a[2x]).
    #[test]
    fn fold_in_place_pair_matches_formula() {
        let mut rng = Rng::new(300);
        for &log_n in &[1usize, 2, 3, 4, 6] {
            let n = 1usize << log_n;
            let a_orig: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let b_orig: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let challenge = rng.ext();

            let mut a = ArenaVec::from_slice(&a_orig);
            let mut b = ArenaVec::from_slice(&b_orig);
            fold_in_place_pair(&mut a, &mut b, challenge);

            assert_eq!(a.len(), n / 2);
            assert_eq!(b.len(), n / 2);
            for x in 0..(n / 2) {
                let a0 = a_orig[2 * x];
                let a1 = a_orig[2 * x + 1];
                let b0 = b_orig[2 * x];
                let b1 = b_orig[2 * x + 1];
                assert_eq!(a[x], a0 + challenge * (a1 + a0), "log_n={log_n}, x={x}");
                assert_eq!(b[x], b0 + challenge * (b1 + b0), "log_n={log_n}, x={x}");
            }
        }
    }

    /// **The round-1 kernel's C side**: `interpolate(round1_c, k_skip, z)`
    /// equals `ĉ(z, r_rest)` computed by direct folding (Lagrange at z, then
    /// bind each `r_rest` value). The protocol sends `round1_c` only inside its
    /// sum with the AB half, so this is what pins that half on its own.
    #[test]
    fn c_eval_from_round1_c_matches_direct_fold() {
        use crate::zerocheck::round1::round1_message_packed_padded;
        use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
        use primitives::field::F8;

        const K_SKIP: usize = 6;

        for &m in &[14usize, 15, 16] {
            let mut rng = Rng::new(500 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c = rng.bits(1 << m);

            let r: Vec<F192> = (0..m - K_SKIP).map(|_| rng.ext()).collect();
            let z = rng.ext();

            let a_packed = pack_bits(&a);
            let b_packed = pack_bits(&b);
            let c_packed = pack_bits(&c);

            let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
            let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
            let (_round1_ab, round1_c) = round1_message_packed_padded(
                &a_packed,
                &b_packed,
                &c_packed,
                m,
                K_SKIP,
                &r,
                &inv_table,
                &PaddingSpec::dense(m),
            );

            // Path A: interpolate round1_c at z.
            let c_eval_via_interpolation = interpolate_at_z_on_lambda(&round1_c, K_SKIP, z);

            // Path B: direct fold of c at z (Lagrange) then bind each
            // r_rest element with fold_in_place_single.
            let weights = lagrange_weights_naive(K_SKIP, z);
            let mut c_mlv = fold_at_z_naive(&c, m, K_SKIP, &weights);
            for &r_val in &r {
                fold_in_place_single(&mut c_mlv, r_val);
            }
            assert_eq!(c_mlv.len(), 1);
            let c_eval_via_fold = c_mlv[0];

            assert_eq!(
                c_eval_via_interpolation, c_eval_via_fold,
                "c-claim identity broken at m={m}"
            );
        }
    }

    /// **The big cross-check**: fused `fold_and_compute_round_pair_into`
    /// produces the same output as the unfused sequence
    /// `fold_in_place_pair` → `round_pair_naive`.
    #[test]
    fn fused_round_matches_unfused() {
        let mut rng = Rng::new(310);
        for &log_n in &[10usize, 11, 12] {
            let n = 1usize << log_n;
            let a: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let b: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let r_fold = rng.ext();
            let r_eq = rng.ext_vec(log_n - 2);

            // Fused path.
            let mut a_fused = vec![F192::ZERO; n / 2];
            let mut b_fused = vec![F192::ZERO; n / 2];
            let (m1_fused, minf_fused) =
                fold_and_compute_round_pair_into(&a, &b, &mut a_fused, &mut b_fused, r_fold, &r_eq);

            // Unfused path: clone, in-place fold, naive message.
            let mut a_unf = ArenaVec::from_slice(&a);
            let mut b_unf = ArenaVec::from_slice(&b);
            fold_in_place_pair(&mut a_unf, &mut b_unf, r_fold);
            let (m1_unf, minf_unf) = round_pair_naive(&a_unf, &b_unf, &r_eq);

            assert_eq!(a_fused.as_slice(), &a_unf[..], "a mismatch at log_n={log_n}");
            assert_eq!(b_fused.as_slice(), &b_unf[..], "b mismatch at log_n={log_n}");
            assert_eq!(m1_fused, m1_unf, "msg_1 mismatch at log_n={log_n}");
            assert_eq!(minf_fused, minf_unf, "msg_inf mismatch at log_n={log_n}");
        }
    }

    /// **Padding skip is byte-identical to the dense round-2 kernel.** Builds
    /// witnesses with bits `[useful_bits, 2^k_log)` of every block honestly
    /// zero, then asserts the `_padded` kernel produces the same
    /// `(a_mlv, b_mlv, msg_1, msg_inf)` as the dense path.
    ///
    /// Covers all three hash padding shapes: BLAKE2s (k_log=14, useful=15409),
    /// SHA-2 (k_log=15, useful=31401), Keccak (k_log=16, useful=42560).
    #[test]
    fn uni_skip_fold_round_pair_padded_matches_dense() {
        const K_SKIP: usize = 6;
        let cases: &[(usize, usize, usize)] = &[(17, 14, 15_409), (18, 15, 31_401), (19, 16, 42_560)];
        for &(m, k_log, useful_bits) in cases {
            let mut rng = Rng::new(0xFADE_F00D_u64.wrapping_add((k_log * 31 + m) as u64));
            let total_bits = 1usize << m;
            let block_size = 1usize << k_log;
            let n_blocks = 1usize << (m - k_log);

            // Random witness, then zero bits [useful_bits, block_size) of each
            // block in both a and b (matches honestly-padded hash R1CS).
            let mut a = rng.bits(total_bits);
            let mut b = rng.bits(total_bits);
            for blk in 0..n_blocks {
                for j in useful_bits..block_size {
                    a[blk * block_size + j] = false;
                    b[blk * block_size + j] = false;
                }
            }
            let a_packed = pack_bits(&a);
            let b_packed = pack_bits(&b);

            let z = rng.ext();
            let mlv_eq = rng.ext_vec(m - K_SKIP - 1);
            let table = UniSkipFoldTable::new(K_SKIP, z);
            let padding = PaddingSpec {
                k_log,
                useful_bits_per_block: useful_bits,
            };

            let dense = uni_skip_fold_and_round_pair_optimized_packed_padded(
                &a_packed,
                &b_packed,
                m,
                K_SKIP,
                &table,
                &mlv_eq,
                &PaddingSpec::dense(m),
            );
            let padded = uni_skip_fold_and_round_pair_optimized_packed_padded(
                &a_packed, &b_packed, m, K_SKIP, &table, &mlv_eq, &padding,
            );
            assert_eq!(dense.0, padded.0, "a_mlv: m={m}, k_log={k_log}, useful={useful_bits}");
            assert_eq!(dense.1, padded.1, "b_mlv: m={m}, k_log={k_log}, useful={useful_bits}");
            assert_eq!(dense.2, padded.2, "msg_1: m={m}, k_log={k_log}, useful={useful_bits}");
            assert_eq!(dense.3, padded.3, "msg_inf: m={m}, k_log={k_log}, useful={useful_bits}");
        }
    }

    /// The single-table kernels are the pair kernels' `c` half: fed the same
    /// table, they must fold to the same values, and their message must be the
    /// naive linear one. Covers both the URM fold and the fused round, whose
    /// index conventions are hand-written and shared with the pair siblings.
    #[test]
    fn single_kernels_match_the_pair_convention() {
        const K_SKIP: usize = 6;
        let mut rng = Rng::new(0x51_9C_1E);

        // URM fold: c_folded must equal the pair kernel's a_folded on the same
        // input, and G_c(1) must be the naive linear message on it.
        for &m in &[13usize, 14, 16] {
            let bits = rng.bits(1 << m);
            let packed = pack_bits(&bits);
            let z = rng.ext();
            let mlv_eq = rng.ext_vec(m - K_SKIP - 1);
            let table = UniSkipFoldTable::new(K_SKIP, z);
            let dense = PaddingSpec::dense(m);

            let (a_folded, _, _, _) = uni_skip_fold_and_round_pair_optimized_packed_padded(
                &packed, &packed, m, K_SKIP, &table, &mlv_eq, &dense,
            );
            let (c_folded, msg_c1) =
                uni_skip_fold_and_round_single_optimized_packed_padded(&packed, m, K_SKIP, &table, &mlv_eq, &dense);
            assert_eq!(&a_folded[..], &c_folded[..], "fold mismatch at m={m}");
            assert_eq!(msg_c1, round_single_naive(&c_folded, &mlv_eq), "msg at m={m}");
        }

        // Fused round: same, against fold_in_place_single + round_single_naive.
        // lo_size ≥ 2 needs log_n ≥ 10, which is the path's own gate.
        for &log_n in &[10usize, 11, 12] {
            let n = 1usize << log_n;
            let c: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let r_fold = rng.ext();
            let r_eq = rng.ext_vec(log_n - 2);

            let mut c_fused = vec![F192::ZERO; n / 2];
            let m1_fused = fold_and_compute_round_single_into(&c, &mut c_fused, r_fold, &r_eq);

            let mut c_unf = ArenaVec::from_slice(&c);
            fold_in_place_single(&mut c_unf, r_fold);
            let m1_unf = round_single_naive(&c_unf, &r_eq);

            assert_eq!(c_fused.as_slice(), &c_unf[..], "fold mismatch at log_n={log_n}");
            assert_eq!(m1_fused, m1_unf, "msg mismatch at log_n={log_n}");
        }
    }

    /// **The single kernel's padding skip is byte-identical to dense**, the
    /// sibling of `uni_skip_fold_round_pair_padded_matches_dense`. This is the
    /// first place the C witness's padding zeros are load-bearing: round 1's
    /// coarser skip does not reach them at BLAKE2s's shape.
    #[test]
    fn uni_skip_fold_round_single_padded_matches_dense() {
        const K_SKIP: usize = 6;
        let cases: &[(usize, usize, usize)] = &[(17, 14, 15_409), (17, 14, 16_000), (18, 15, 31_401)];
        for &(m, k_log, useful_bits) in cases {
            let mut rng = Rng::new(0xC0DE_F00D_u64.wrapping_add((k_log * 31 + m) as u64));
            let block_size = 1usize << k_log;
            let n_blocks = 1usize << (m - k_log);

            let mut c = rng.bits(1usize << m);
            for blk in 0..n_blocks {
                for j in useful_bits..block_size {
                    c[blk * block_size + j] = false;
                }
            }
            let c_packed = pack_bits(&c);

            let z = rng.ext();
            let mlv_eq = rng.ext_vec(m - K_SKIP - 1);
            let table = UniSkipFoldTable::new(K_SKIP, z);
            let padding = PaddingSpec {
                k_log,
                useful_bits_per_block: useful_bits,
            };

            let dense = uni_skip_fold_and_round_single_optimized_packed_padded(
                &c_packed,
                m,
                K_SKIP,
                &table,
                &mlv_eq,
                &PaddingSpec::dense(m),
            );
            let padded =
                uni_skip_fold_and_round_single_optimized_packed_padded(&c_packed, m, K_SKIP, &table, &mlv_eq, &padding);
            assert_eq!(dense.0, padded.0, "c_mlv: m={m}, k_log={k_log}, useful={useful_bits}");
            assert_eq!(dense.1, padded.1, "msg_1: m={m}, k_log={k_log}, useful={useful_bits}");
        }
    }

    /// `fold_one_row` via the table equals direct-Lagrange fold.
    #[test]
    fn fold_table_one_row_matches_direct_lagrange() {
        let m = 8;
        let k_skip = 3;
        let mut rng = Rng::new(60);
        let z = rng.ext();
        let a = rng.bits(1 << m);
        let weights = lagrange_weights_naive(k_skip, z);
        let table = UniSkipFoldTable::new(k_skip, z);
        let a_packed = pack_bits(&a);

        let n_chunks = table.n_chunks;

        for x_rest in 0..(1usize << (m - k_skip)) {
            let direct = {
                let mut acc = F192::ZERO;
                for s in 0..(1usize << k_skip) {
                    if a[x_rest * (1usize << k_skip) + s] {
                        acc += weights[s];
                    }
                }
                acc
            };
            let via_table = table.fold_one_row(&a_packed[x_rest * n_chunks..(x_rest + 1) * n_chunks]);
            assert_eq!(via_table, direct, "x_rest={x_rest}");
        }
    }

    /// **The full cross-check**: optimized fused output matches naive
    /// byte-for-byte at the headline `k_skip = 6` (and other small m). Same eq
    /// weights, same z, same r: so a_mlv, b_mlv, and the two message values
    /// must all agree exactly.
    #[test]
    fn optimized_matches_naive() {
        for &m in &[7usize, 8, 9, 10] {
            let k_skip = 6;
            if m <= k_skip {
                continue;
            }
            let mut rng = Rng::new(100 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let z = rng.ext();
            let mlv_eq = rng.ext_vec(m - k_skip - 1);

            let (a_n, b_n, m1_n, minf_n) = uni_skip_fold_and_round_pair_naive(&a, &b, m, k_skip, z, &mlv_eq);
            let table = UniSkipFoldTable::new(k_skip, z);
            let (a_o, b_o, m1_o, minf_o) = uni_skip_fold_and_round_pair_optimized_packed_padded(
                &pack_bits(&a),
                &pack_bits(&b),
                m,
                k_skip,
                &table,
                &mlv_eq,
                &PaddingSpec::dense(m),
            );

            assert_eq!(a_n, a_o, "a_mlv mismatch at m={m}");
            assert_eq!(b_n, b_o, "b_mlv mismatch at m={m}");
            assert_eq!(m1_n, m1_o, "msg_1 mismatch at m={m}");
            assert_eq!(minf_n, minf_o, "msg_inf mismatch at m={m}");
        }
    }

    /// Strong cross-check: compute G(0), G(1), G(∞) by direct sum (using the
    /// LSB-first index convention `a_mlv(0, x') = a[2x']`, `a_mlv(1, x') = a[2x'+1]`),
    /// then verify that G interpolated through those three values agrees with
    /// the direct multilinear evaluation at a fresh random X: confirming G
    /// genuinely has degree ≤ 2.
    ///
    /// Also verifies `round_pair_naive` returns `(r[0] · G(1), G(∞))`.
    #[test]
    fn round_pair_message_has_degree_two() {
        let m = 6;
        let k_skip = 3;
        let mut rng = Rng::new(55);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let z = rng.ext();
        let r_eq = rng.ext_vec(m - k_skip - 1);

        let weights = lagrange_weights_naive(k_skip, z);
        let a_mlv = fold_at_z_naive(&a, m, k_skip, &weights);
        let b_mlv = fold_at_z_naive(&b, m, k_skip, &weights);

        let n = a_mlv.len();
        let half = n / 2;
        let eq_remaining = build_eq(&r_eq);

        // G(0), G(1), G(∞) by direct definition.
        let mut g0 = F192::ZERO;
        let mut g1 = F192::ZERO;
        let mut g_inf = F192::ZERO;
        for x_prime in 0..half {
            let a0 = a_mlv[2 * x_prime];
            let a1 = a_mlv[2 * x_prime + 1];
            let b0 = b_mlv[2 * x_prime];
            let b1 = b_mlv[2 * x_prime + 1];
            let eq_x = eq_remaining[x_prime];
            g0 += eq_x * a0 * b0;
            g1 += eq_x * a1 * b1;
            g_inf += eq_x * (a0 + a1) * (b0 + b1);
        }

        let (msg_1, msg_inf) = round_pair_naive(&a_mlv, &b_mlv, &r_eq);
        assert_eq!(msg_1, g1);
        assert_eq!(msg_inf, g_inf);

        // Degree-2 check: G(X) reconstructed through (G(0), G(1), G(∞)) must
        // agree with the direct multilinear evaluation at a fresh point X.
        // Char-2 interpolation: G(X) = G(0) + X·(G(0)+G(1)) + X·(X+1)·G(∞).
        let x = rng.ext();
        let g_via_poly = g0 + x * (g0 + g1) + x * (x + F192::ONE) * g_inf;
        let mut g_via_sum = F192::ZERO;
        for x_prime in 0..half {
            let a0 = a_mlv[2 * x_prime];
            let a1 = a_mlv[2 * x_prime + 1];
            let b0 = b_mlv[2 * x_prime];
            let b1 = b_mlv[2 * x_prime + 1];
            let a_x = a0 + x * (a0 + a1);
            let b_x = b0 + x * (b0 + b1);
            g_via_sum += eq_remaining[x_prime] * a_x * b_x;
        }
        assert_eq!(g_via_poly, g_via_sum);
    }
}
