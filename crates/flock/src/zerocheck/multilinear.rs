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
//! The rounds run in two regimes, cross-checked in tests against the naive fold-then-sum references:
//!
//! - **Bit rounds.** While a folded F192 table would outweigh the packed bits, each pass re-reads the bits.
//!   A pass folds them on the fly and sends two rounds, the second as a quadratic in the first's challenge.
//! - **Table rounds.** The last bit pass stores the folded tables, and each later round folds and sums them.
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
use crate::zerocheck::bit_fold::{BLOCK, BitFold};
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

// ---------------------------------------------------------------------------
// Lagrange weights for the univariate-skip fold at z.
// ---------------------------------------------------------------------------

#[cfg(test)]
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
// Bit-resident rounds: fold and message straight from the packed witness.
// ---------------------------------------------------------------------------

/// Returns `(pair_in_block_mask, live_pairs)` for a round whose positions each cover `2^position_log` witness bits.
///
/// Pair `k` (positions `2k`, `2k+1`) lies wholly in a block's zero padding iff `(k & pair_in_block_mask) >= live_pairs`.
///
/// - Such a pair folds to zero, so it adds nothing to the message.
/// - A pair straddling the boundary counts as live: its padding half is honestly zero.
/// - With no whole padding pair, the mask is zero and every pair is live.
fn padding_pairs(padding: &PaddingSpec, position_log: usize) -> (usize, usize) {
    if padding.k_log <= position_log + 1 {
        return (0, usize::MAX);
    }
    let pairs_per_block = 1usize << (padding.k_log - position_log - 1);
    let live_pairs = padding.useful_bits_per_block.div_ceil(2 << position_log);
    if live_pairs >= pairs_per_block {
        return (0, usize::MAX);
    }
    (pairs_per_block - 1, live_pairs)
}

/// Eq variables in the per-task half of the split eq table.
///
/// - 2^10 entries are 24 KiB, so the table stays in L1 beside the fold's matrices.
/// - The remaining variables index the tasks, one reduced product each.
const EQ_LO_VARS: usize = 10;

/// The split eq table over `r`: `eq(r, k) = hi[k >> n_lo] * lo[k & (2^n_lo - 1)]`.
///
/// Each task sums its `2^n_lo` terms unreduced, then pays one reduction and one product.
fn split_eq(r: &[F192]) -> (Vec<F192>, Vec<F192>) {
    let n_lo = r.len().min(EQ_LO_VARS);
    (build_eq(&r[..n_lo]), build_eq(&r[n_lo..]))
}

/// The packed `a`, `b`, `c` witnesses, 64 skip bits per row.
#[derive(Clone, Copy, Debug)]
pub struct PackedWitness<'a> {
    /// The `A z` bits.
    pub a: &'a [u8],
    /// The `B z` bits.
    pub b: &'a [u8],
    /// The `C z` bits.
    pub c: &'a [u8],
}

impl<'a> PackedWitness<'a> {
    /// The three witnesses cut into rows of `CHUNKS` bytes, one per position at this level.
    fn rows<const CHUNKS: usize>(self) -> [&'a [[u8; CHUNKS]]; 3] {
        let rows = [self.a, self.b, self.c].map(|packed| {
            let (rows, rest) = packed.as_chunks::<CHUNKS>();
            assert!(rest.is_empty(), "packed witness is whole rows");
            rows
        });
        let n_pos = rows[0].len();
        assert!(rows.iter().all(|r| r.len() == n_pos), "a, b, c have one length");
        assert!(n_pos.is_power_of_two(), "a power-of-two number of positions");
        rows
    }
}

/// The folded `a`, `b`, `c` values of up to 64 consecutive positions.
struct FoldedBlock {
    a: [F192; BLOCK],
    b: [F192; BLOCK],
    c: [F192; BLOCK],
}

impl FoldedBlock {
    /// Fold positions `first..first + len` of each witness.
    #[inline(always)]
    fn new<const CHUNKS: usize>(fold: &BitFold, rows: [&[[u8; CHUNKS]]; 3], first: usize, len: usize) -> Self {
        let mut block = Self {
            a: [F192::ZERO; BLOCK],
            b: [F192::ZERO; BLOCK],
            c: [F192::ZERO; BLOCK],
        };
        let [a, b, c] = rows;
        fold.fold_block(&a[first..first + len], &mut block.a);
        fold.fold_block(&b[first..first + len], &mut block.b);
        fold.fold_block(&c[first..first + len], &mut block.c);
        block
    }
}

/// Two consecutive multilinear rounds from one pass over the packed bits.
///
/// Round `t + 1` binds its variable after the verifier samples `rho`, the challenge of round `t`.
///
/// Its polynomial is quadratic in that `rho`, so one pass stores its three coefficients per evaluation point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundPair {
    /// Round `t`'s `(G(1), G(inf))`.
    pub first: (F192, F192),
    /// Round `t + 1` at `Y = 1` and `Y = inf`, each as `[S_0, S_1, S_2]`.
    ///
    /// ```text
    ///     G(Y) = (1 + rho) S_0 + rho S_1 + rho (1 + rho) S_2
    /// ```
    second: [[F192; 3]; 2],
}

impl RoundPair {
    /// Round `t + 1`'s `(G(1), G(inf))`, once round `t`'s challenge `rho` is known.
    pub fn second(&self, rho: F192) -> (F192, F192) {
        let [one, inf] = self
            .second
            .map(|[s0, s1, s2]| s0 + rho * (s0 + s1) + rho * (F192::ONE + rho) * s2);
        (one, inf)
    }
}

/// Rounds `t` and `t + 1` straight from the packed bits, the folded tables never stored.
///
/// With `rho_1..rho_t` bound, `fold` weights each position's `2^t` rows (see its level constructor).
///
/// Each round's polynomial, with `r_eq` the eq challenges of the variables round `t` does not bind:
///
/// ```text
///     G(X) = sum_x' eq(r_eq, x') * (a(X, x') * b(X, x') + c(X, x'))
/// ```
///
/// The linear `c` term reaches `G(1)` only.
pub fn bit_round_pair(bits: PackedWitness<'_>, fold: &BitFold, r_eq: &[F192], padding: &PaddingSpec) -> RoundPair {
    match fold.n_chunks() {
        8 => bit_round_pair_kernel::<8>(bits, fold, r_eq, padding),
        16 => bit_round_pair_kernel::<16>(bits, fold, r_eq, padding),
        32 => bit_round_pair_kernel::<32>(bits, fold, r_eq, padding),
        64 => bit_round_pair_kernel::<64>(bits, fold, r_eq, padding),
        128 => bit_round_pair_kernel::<128>(bits, fold, r_eq, padding),
        n => panic!("no bit-round kernel for {n}-byte rows"),
    }
}

/// One round straight from the packed bits, storing the folded `(a, b, c)` tables for the rounds that follow.
///
/// Returns the round's `(G(1), G(inf))`, then the three tables.
pub fn bit_round_materialize(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> ((F192, F192), [ArenaVec<F192>; 3]) {
    match fold.n_chunks() {
        8 => bit_round_store_kernel::<8>(bits, fold, r_eq, padding),
        16 => bit_round_store_kernel::<16>(bits, fold, r_eq, padding),
        32 => bit_round_store_kernel::<32>(bits, fold, r_eq, padding),
        64 => bit_round_store_kernel::<64>(bits, fold, r_eq, padding),
        128 => bit_round_store_kernel::<128>(bits, fold, r_eq, padding),
        n => panic!("no bit-round kernel for {n}-byte rows"),
    }
}

/// The two-round pass, for rows of `CHUNKS` bytes.
///
/// Positions group in quads `4k + u + 2v`: `u` is round `t`'s variable and `v` round `t + 1`'s.
///
/// ```text
///     position   4k     4k+1   4k+2   4k+3
///     (u, v)     (0,0)  (1,0)  (0,1)  (1,1)
/// ```
///
/// Round `t + 1` folds `u` at `rho` first, so each of its values is `f(rho, Y) = f(0, Y) + rho * (f(0, Y) + f(1, Y))`.
///
/// Expanding the product in `rho` gives the three sums of the second round:
///
/// ```text
///     S_0 = sum eq * a(0, Y) b(0, Y)      S_1 = sum eq * a(1, Y) b(1, Y)
///     S_2 = sum eq * (a(0, Y) + a(1, Y)) (b(0, Y) + b(1, Y))
/// ```
///
/// Round `t` needs its sums split by `v`, and two of them coincide with round `t + 1`'s.
///
/// So eight products per quad cover both rounds, the same count as two passes.
fn bit_round_pair_kernel<const CHUNKS: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> RoundPair {
    let rows = bits.rows::<CHUNKS>();
    let n_quads = rows[0].len() / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);

    // `r_eq[0]` weights round `t`'s split by `v`; the rest weight the quads.
    let (r_v, r_quad) = (r_eq[0], &r_eq[1..]);
    let (eq_lo, eq_hi) = split_eq(r_quad);
    let lo_size = eq_lo.len();

    // A quad covers 2^6 skip bits times its 4 * 2^t bound rows.
    let quad_log = (32 * CHUNKS).trailing_zeros() as usize;
    let (quad_in_block_mask, live_quads) = padding_pairs(padding, quad_log - 1);
    let live = |quad: usize| (quad & quad_in_block_mask) < live_quads;

    let sums = parallel::map_reduce(
        eq_hi.len(),
        || [F192::ZERO; 8],
        |hi| {
            let mut acc = [F192Unreduced::ZERO; 8];
            // Sixteen quads per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 4) {
                let n = (lo_size - lo_first).min(BLOCK / 4);
                let quad_first = hi * lo_size + lo_first;
                // A block wholly in padding folds to zero.
                if !(quad_first..quad_first + n).any(live) {
                    continue;
                }
                let f = FoldedBlock::new(fold, rows, 4 * quad_first, 4 * n);
                for i in 0..n {
                    let [a0, a1, a2, a3]: [F192; 4] = f.a[4 * i..4 * i + 4].try_into().expect("a quad");
                    let [b0, b1, b2, b3]: [F192; 4] = f.b[4 * i..4 * i + 4].try_into().expect("a quad");
                    let [_, c1, c2, c3]: [F192; 4] = f.c[4 * i..4 * i + 4].try_into().expect("a quad");

                    // Leading coefficients along `u` (positions 0,1 and 2,3) and along `v` (0,2 and 1,3).
                    let (du0, du1, dv0, dv1) = (a0 + a1, a2 + a3, a0 + a2, a1 + a3);
                    let (eu0, eu1, ev0, ev1) = (b0 + b1, b2 + b3, b0 + b2, b1 + b3);
                    let (p1, p2, p3, q0) = mul_quad((a1, a2, a3, du0), (b1, b2, b3, eu0));
                    let (q1, r0, r1, r2) = mul_quad((du1, dv0, dv1, du0 + du1), (eu1, ev0, ev1, eu0 + eu1));

                    // Every term of the quad shares one eq weight.
                    let eq = eq_lo[lo_first + i];
                    let e = (eq, eq, eq, eq);
                    let (s0, s1, s2, s3) = mul_quad_unreduced(e, (p1 + c1, p3 + c3, q0, q1));
                    let (s4, s5, s6, s7) = mul_quad_unreduced(e, (p2 + c2, r0, r1, r2));
                    for (acc, s) in acc.iter_mut().zip([s0, s1, s2, s3, s4, s5, s6, s7]) {
                        *acc ^= s;
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    // Slots 0, 1 hold round t's G(1) at v = 0, 1, and slots 2, 3 its G(inf).
    // Round t + 1 reads slots 4, 1, 3 at Y = 1 and 5, 6, 7 at Y = inf.
    let split_v = |v0: F192, v1: F192| v0 + r_v * (v0 + v1);
    RoundPair {
        first: (split_v(sums[0], sums[1]), split_v(sums[2], sums[3])),
        second: [[sums[4], sums[1], sums[3]], [sums[5], sums[6], sums[7]]],
    }
}

/// The storing single-round pass, for rows of `CHUNKS` bytes.
///
/// Positions pair up as `(2k, 2k + 1)`, the low index bit being the variable this round binds.
fn bit_round_store_kernel<const CHUNKS: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> ((F192, F192), [ArenaVec<F192>; 3]) {
    let rows = bits.rows::<CHUNKS>();
    let n_pos = rows[0].len();
    assert!(n_pos >= 2, "a round needs two positions");
    assert_eq!(r_eq.len(), n_pos.trailing_zeros() as usize - 1);

    let (eq_lo, eq_hi) = split_eq(r_eq);
    let lo_size = eq_lo.len();

    // A position covers 2^6 skip bits times its 2^t bound rows.
    let position_log = (8 * CHUNKS).trailing_zeros() as usize;
    let (pair_in_block_mask, live_pairs) = padding_pairs(padding, position_log);
    let live = |pair: usize| (pair & pair_in_block_mask) < live_pairs;

    // SAFETY (x3): every slot is written below, padding included.
    let mut out: [ArenaVec<F192>; 3] = std::array::from_fn(|_| unsafe { ArenaVec::uninitialized(n_pos) });
    let [out_a, out_b, out_c] = &mut out;
    let chunks = [out_a, out_b, out_c].map(|o| parallel::Chunks::new(o, 2 * lo_size));

    let message = parallel::map_reduce(
        eq_hi.len(),
        || (F192::ZERO, F192::ZERO),
        |hi| {
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let [oa, ob, oc] = chunks.map(|ch| unsafe { ch.get(hi) });
            let stream = Stream::new();
            let mut g1_acc = F192Unreduced::ZERO;
            let mut ginf_acc = F192Unreduced::ZERO;
            // Thirty-two pairs per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 2) {
                let n = (lo_size - lo_first).min(BLOCK / 2);
                let pair_first = hi * lo_size + lo_first;
                let (o_first, o_len) = (2 * lo_first, 2 * n);
                // A block wholly in padding folds to zero.
                if !(pair_first..pair_first + n).any(live) {
                    for o in [&mut *oa, &mut *ob, &mut *oc] {
                        o[o_first..o_first + o_len].fill(F192::ZERO);
                    }
                    continue;
                }
                let f = FoldedBlock::new(fold, rows, 2 * pair_first, o_len);

                // Four pairs per step: every product is one lane of a quad.
                let mut i = 0;
                while i + 4 <= n {
                    let at = |t: &[F192; BLOCK], k: usize| (t[2 * (i + k)], t[2 * (i + k) + 1]);
                    let [(a0_a, a1_a), (a0_b, a1_b), (a0_c, a1_c), (a0_d, a1_d)] = [0, 1, 2, 3].map(|k| at(&f.a, k));
                    let [(b0_a, b1_a), (b0_b, b1_b), (b0_c, b1_c), (b0_d, b1_d)] = [0, 1, 2, 3].map(|k| at(&f.b, k));
                    let [(_, c1_a), (_, c1_b), (_, c1_c), (_, c1_d)] = [0, 1, 2, 3].map(|k| at(&f.c, k));

                    // G(1) takes a_1 b_1 + c_1.
                    // G(inf) takes (a_0 + a_1)(b_0 + b_1), the leading coefficient in characteristic 2.
                    let (p_a, p_b, p_c, p_d) = mul_quad((a1_a, a1_b, a1_c, a1_d), (b1_a, b1_b, b1_c, b1_d));
                    let (q_a, q_b, q_c, q_d) = mul_quad(
                        (a0_a + a1_a, a0_b + a1_b, a0_c + a1_c, a0_d + a1_d),
                        (b0_a + b1_a, b0_b + b1_b, b0_c + b1_c, b0_d + b1_d),
                    );
                    let lo = lo_first + i;
                    let eq_q = (eq_lo[lo], eq_lo[lo + 1], eq_lo[lo + 2], eq_lo[lo + 3]);
                    let (t1_a, t1_b, t1_c, t1_d) =
                        mul_quad_unreduced(eq_q, (p_a + c1_a, p_b + c1_b, p_c + c1_c, p_d + c1_d));
                    let (ti_a, ti_b, ti_c, ti_d) = mul_quad_unreduced(eq_q, (q_a, q_b, q_c, q_d));
                    g1_acc ^= t1_a ^ t1_b ^ t1_c ^ t1_d;
                    ginf_acc ^= ti_a ^ ti_b ^ ti_c ^ ti_d;
                    i += 4;
                }
                // Fewer than four pairs per task only at the smallest instances.
                while i < n {
                    let (a0, a1, b0, b1, c1) = (f.a[2 * i], f.a[2 * i + 1], f.b[2 * i], f.b[2 * i + 1], f.c[2 * i + 1]);
                    let eq = eq_lo[lo_first + i];
                    g1_acc ^= eq.mul_unreduced(a1 * b1 + c1);
                    ginf_acc ^= eq.mul_unreduced((a0 + a1) * (b0 + b1));
                    i += 1;
                }

                // Publish the block without a read: nothing touches these tables before the next round.
                let dst = o_first..o_first + o_len;
                if o_len.is_multiple_of(8) {
                    for (o, t) in [(&mut *oa, &f.a), (&mut *ob, &f.b), (&mut *oc, &f.c)] {
                        for (d, s) in o[dst.clone()]
                            .as_chunks_mut::<8>()
                            .0
                            .iter_mut()
                            .zip(t.as_chunks::<8>().0)
                        {
                            stream.copy(d, s);
                        }
                    }
                } else {
                    oa[dst.clone()].copy_from_slice(&f.a[..o_len]);
                    ob[dst.clone()].copy_from_slice(&f.b[..o_len]);
                    oc[dst].copy_from_slice(&f.c[..o_len]);
                }
            }
            (eq_hi[hi] * g1_acc.reduce(), eq_hi[hi] * ginf_acc.reduce())
        },
        |(s1, si), (t1, ti)| (s1 + t1, si + ti),
    );
    (message, out)
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

    /// **The URM kernel's C side**: `C_s · interpolate(round1_c, k_skip, z)`
    /// equals `ĉ(z, r_rest)` computed by direct folding (Lagrange at z, then
    /// bind each `r_rest` value). The protocol sends `round1_c` only inside its
    /// sum with the AB half, so this is what pins that half on its own.
    #[test]
    fn c_eval_from_round1_c_matches_direct_fold() {
        use crate::zerocheck::univariate_skip_optimized::{
            c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges,
        };
        use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
        use primitives::field::F8;

        const K_SKIP: usize = 6;
        const N_INNER: usize = 7;

        for &m in &[14usize, 15, 16] {
            let mut rng = Rng::new(500 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c = rng.bits(1 << m);

            // Build the equality tail with the seven protocol-fixed constants,
            // matching how `prove` constructs it.
            let mut r = vec![F192::ZERO; m - K_SKIP];
            for (i, v) in small_challenges().iter().enumerate() {
                r[i] = *v;
            }
            for (i, v) in medium_challenges().iter().enumerate() {
                r[3 + i] = *v;
            }
            for slot in r[N_INNER..].iter_mut() {
                *slot = rng.ext();
            }
            let z = rng.ext();

            let a_packed = pack_bits(&a);
            let b_packed = pack_bits(&b);
            let c_packed = pack_bits(&c);

            let ntt_s = AdditiveNttGf8::new(K_SKIP, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(K_SKIP, F8(1u8 << K_SKIP));
            let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
            let (_round1_ab, round1_c) = round1_shift_reduce_extract_c_packed_padded(
                &a_packed,
                &b_packed,
                &c_packed,
                m,
                K_SKIP,
                &r,
                &inv_table,
                &PaddingSpec::dense(m),
            );

            // Path A: interpolate round1_c at z, scale by C_s.
            let c_eval_via_interpolation = c_s() * interpolate_at_z_on_lambda(&round1_c, K_SKIP, z);

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

    /// The fused single-table round against `fold_in_place_single` then `round_single_naive`.
    #[test]
    fn fused_single_round_matches_unfused() {
        let mut rng = Rng::new(0x51_9C_1E);
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

    /// A random `a, b, c` witness over `2^m` slots, bits and packed.
    fn random_witness(rng: &mut Rng, m: usize) -> ([Vec<bool>; 3], [Vec<u8>; 3]) {
        let bits = [rng.bits(1 << m), rng.bits(1 << m), rng.bits(1 << m)];
        let packed = [0, 1, 2].map(|i| pack_bits(&bits[i]));
        (bits, packed)
    }

    fn packed(p: &[Vec<u8>; 3]) -> PackedWitness<'_> {
        PackedWitness {
            a: &p[0],
            b: &p[1],
            c: &p[2],
        }
    }

    /// The naive message of one round on stored tables: `(G(1), G(inf))` with `c` added to `G(1)`.
    fn naive_message(t: &[ArenaVec<F192>; 3], r_eq: &[F192]) -> (F192, F192) {
        let (g1, g_inf) = round_pair_naive(&t[0], &t[1], r_eq);
        (g1 + round_single_naive(&t[2], r_eq), g_inf)
    }

    /// Every bit-round kernel at every level against the naive route: fold at z, bind each rho, then sum.
    #[test]
    fn bit_rounds_match_naive() {
        const K_SKIP: usize = 6;
        for m in [13usize, 14, 15] {
            let mut rng = Rng::new(0xB17_0000 + m as u64);
            let (bits, packed_bits) = random_witness(&mut rng, m);
            let n_mlv = m - K_SKIP;
            let z = rng.ext();
            let r_rest = rng.ext_vec(n_mlv);
            let rho = rng.ext_vec(n_mlv);
            let lagrange = lagrange_weights_naive(K_SKIP, z);
            let dense = PaddingSpec::dense(m);

            // Level 0 of the naive route: the univariate-skip fold at z.
            let mut tables = [0, 1, 2].map(|i| fold_at_z_naive(&bits[i], m, K_SKIP, &lagrange));
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let expected = naive_message(&tables, r_eq);

                // The storing kernel: this level's message and tables.
                let (message, stored) = bit_round_materialize(packed(&packed_bits), &fold, r_eq, &dense);
                assert_eq!(message, expected, "store message, m={m}, t={t}");
                for (got, want) in stored.iter().zip(&tables) {
                    assert_eq!(&got[..], &want[..], "stored table, m={m}, t={t}");
                }

                // Bind rho_{t+1} on the naive side; the pair kernel's second round must land on it.
                let [ta, tb, tc] = &mut tables;
                fold_in_place_pair(ta, tb, rho[t]);
                fold_in_place_single(tc, rho[t]);
                let pair = bit_round_pair(packed(&packed_bits), &fold, r_eq, &dense);
                assert_eq!(pair.first, expected, "pair first round, m={m}, t={t}");
                assert_eq!(
                    pair.second(rho[t]),
                    naive_message(&tables, &r_rest[t + 2..]),
                    "pair second round, m={m}, t={t}"
                );
            }
        }
    }

    /// Skipping whole padding pairs and quads changes nothing on an honestly padded witness.
    ///
    /// Shapes: BLAKE2s (k_log = 14, 16,000 bits), an odd boundary, and a two-block-per-row stride.
    #[test]
    fn bit_rounds_skip_padding_exactly() {
        const K_SKIP: usize = 6;
        for (m, k_log, useful) in [(17usize, 14usize, 16_000usize), (17, 14, 15_409), (18, 15, 31_401)] {
            let mut rng = Rng::new(0xFADE_F00D + (k_log * 31 + useful) as u64);
            let ([mut a, mut b, mut c], _) = random_witness(&mut rng, m);
            // Zero bits [useful, 2^k_log) of every block, as the hash witness does.
            for x in [&mut a, &mut b, &mut c] {
                for block in x.chunks_mut(1 << k_log) {
                    block[useful..].fill(false);
                }
            }
            let packed_bits = [pack_bits(&a), pack_bits(&b), pack_bits(&c)];
            let padding = PaddingSpec {
                k_log,
                useful_bits_per_block: useful,
            };
            let lagrange = lagrange_weights_naive(K_SKIP, rng.ext());
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(4);
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let run = |p: &PaddingSpec| {
                    (
                        bit_round_pair(packed(&packed_bits), &fold, r_eq, p),
                        bit_round_materialize(packed(&packed_bits), &fold, r_eq, p),
                    )
                };
                let ((pair_d, (msg_d, tab_d)), (pair_p, (msg_p, tab_p))) = (run(&PaddingSpec::dense(m)), run(&padding));
                assert_eq!(pair_d, pair_p, "pair, m={m}, useful={useful}, t={t}");
                assert_eq!(msg_d, msg_p, "store message, m={m}, useful={useful}, t={t}");
                for (d, p) in tab_d.iter().zip(&tab_p) {
                    assert_eq!(&d[..], &p[..], "stored table, m={m}, useful={useful}, t={t}");
                }
            }
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
