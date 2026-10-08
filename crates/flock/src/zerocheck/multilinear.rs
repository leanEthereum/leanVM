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
//!   A pass folds them on the fly and sends two or three rounds, each later one quadratic in each earlier challenge.
//! - **Table rounds.** The last bit pass stores the folded tables.
//!   Each later pass folds the challenges pending on them and sends two rounds, as a two-round bit pass does.
//!
//! **Index convention** (matches `fold_in_place_pair`): the **low bit** of the multilinear index
//! is bound first. So `a_mlv[2k]` is the X=0 value and `a_mlv[2k+1]` is the X=1
//! value, paired by the round message and the fold.
//!
//! For `[r_0, …, r_{n-1}]` (one eq challenge per multilinear variable, built so
//! `eq_table` places `r_i` at bit i), **round r=2 binds the variable of `r_0`**
//! and takes eq over `r_1..` for the remaining variables. Subsequent rounds peel
//! off one more.
//!
//! **Round message format**: the kernels return `(G(1), G(∞))`, which is what
//! goes on the wire. The protocol polynomial is `Π(X) = eq(r_now, X) · G(X)` of
//! degree 3, for `r_now` the challenge of the variable bound this round; the
//! verifier reconstructs `G(0)` from the running claim via
//! `current_claim = (1+r_now)·G(0) + r_now·G(1)`.

use crate::zerocheck::PaddingSpec;
use crate::zerocheck::round1::EQ_HIGH_VARS;
use parallel::Chunks;
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::{SplitEq, eq_table};
use primitives::stream::Stream;
use std::mem::MaybeUninit;

/// Four independent products. Tuples keep the scalar and NEON paths in registers, while VPCLMULQDQ uses the batched helper.
#[inline(always)]
fn mul_quad(a: (F192, F192, F192, F192), b: (F192, F192, F192, F192)) -> (F192, F192, F192, F192) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (a.0 * b.0, a.1 * b.1, a.2 * b.2, a.3 * b.3)
}

/// [`mul_quad`] without the reduction, for a caller XOR-accumulating products.
#[inline(always)]
fn mul_quad_unreduced(
    a: (F192, F192, F192, F192),
    b: (F192, F192, F192, F192),
) -> (F192Unreduced, F192Unreduced, F192Unreduced, F192Unreduced) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul_unreduced4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (
        a.0.mul_unreduced(b.0),
        a.1.mul_unreduced(b.1),
        a.2.mul_unreduced(b.2),
        a.3.mul_unreduced(b.3),
    )
}

/// Single-table sibling of [`round_pair_naive`], for the linear `c` term:
/// `G_c(1) = Σ_{x'} eq(r_eq, x') · c_mlv(1, x')`. Linear, so no `G(∞)`.
pub(crate) fn round_single_naive(c_mlv: &[F192], r_eq: &[F192]) -> F192 {
    let n = c_mlv.len();
    assert!(n.is_power_of_two() && n >= 2);
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);
    let eq_remaining = eq_table(r_eq);
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
pub(crate) fn round_pair_naive(a_mlv: &[F192], b_mlv: &[F192], r_eq: &[F192]) -> (F192, F192) {
    let n = a_mlv.len();
    assert_eq!(b_mlv.len(), n);
    assert!(n.is_power_of_two() && n >= 2);
    let half = n / 2;
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);

    let eq_remaining = eq_table(r_eq);
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

/// Returns `(pair_in_block_mask, live_pairs)` for a round whose positions each cover `2^position_log` witness bits.
///
/// Pair `k` (positions `2k`, `2k+1`) lies wholly in a block's zero padding iff `(k & pair_in_block_mask) >= live_pairs`.
///
/// - Such a pair folds to zero, so it adds nothing to the message.
/// - A pair straddling the boundary counts as live: its padding half is honestly zero.
/// - With no whole padding pair, the mask is zero and every pair is live.
const fn padding_pairs(padding: &PaddingSpec, position_log: usize) -> (usize, usize) {
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
/// - Each task sums its terms unreduced, then pays one reduction and one product.
const EQ_LO_VARS: usize = 10;

/// The packed `a` and `b` witnesses, 64 skip bits per row.
///
/// The kernels never read `c`: an honest witness has `c = a AND b`, derived from the rows already loaded.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedWitness<'a> {
    /// The `A z` bits.
    pub a: &'a [u8],
    /// The `B z` bits.
    pub b: &'a [u8],
}

impl<'a> PackedWitness<'a> {
    /// The two witnesses cut into rows of `CHUNKS` bytes, one per position at this level.
    fn rows<const CHUNKS: usize>(self) -> [&'a [[u8; CHUNKS]]; 2] {
        let rows = [self.a, self.b].map(|packed| {
            let (rows, rest) = packed.as_chunks::<CHUNKS>();
            assert!(rest.is_empty(), "packed witness is whole rows");
            rows
        });
        let n_pos = rows[0].len();
        assert_eq!(rows[1].len(), n_pos, "a and b have one length");
        assert!(n_pos.is_power_of_two(), "a power-of-two number of positions");
        rows
    }
}

/// The `c = a AND b` rows of up to 64 positions, into the first `a.len()` rows of `c`.
#[inline(always)]
fn and_rows<const CHUNKS: usize>(a: &[[u8; CHUNKS]], b: &[[u8; CHUNKS]], c: &mut [[u8; CHUNKS]; BLOCK]) {
    for ((c, a), b) in c
        .as_flattened_mut()
        .iter_mut()
        .zip(a.as_flattened())
        .zip(b.as_flattened())
    {
        *c = a & b;
    }
}

/// The folded `a`, `b`, `c` values of up to 64 consecutive positions.
///
/// A task folds every block into one of these, so no block pays for zeroing or moving its tables.
struct FoldedBlock {
    a: [F192; BLOCK],
    b: [F192; BLOCK],
    c: [F192; BLOCK],
}

impl FoldedBlock {
    const ZERO: Self = Self {
        a: [F192::ZERO; BLOCK],
        b: [F192::ZERO; BLOCK],
        c: [F192::ZERO; BLOCK],
    };

    /// Fold positions `first..first + len` of each witness into the first `len` values.
    #[inline(always)]
    fn fold<const CHUNKS: usize>(&mut self, fold: &BitFold, rows: [&[[u8; CHUNKS]]; 2], first: usize, len: usize) {
        let [a, b] = rows.map(|r| &r[first..first + len]);
        let mut c = [[0u8; CHUNKS]; BLOCK];
        and_rows(a, b, &mut c);
        fold.fold_block(a, &mut self.a);
        fold.fold_block(b, &mut self.b);
        fold.fold_block(&c[..len], &mut self.c);
    }
}

/// Points of `{0, 1, inf}^3`, digit `d` in base 3 the value of a pass's variable `d`, `inf` written 2.
const POINTS: usize = 27;

/// The base-3 index of the Boolean point whose bit `d` is variable `d`.
const fn ternary(x: usize) -> usize {
    (x & 1) + 3 * (x >> 1 & 1) + 9 * (x >> 2 & 1)
}

/// Two or three consecutive multilinear rounds from one pass.
///
/// Round `t + i` waits on the challenges `rho_0..rho_i` of the pass's earlier rounds.
/// Its values are multilinear in them, so its products are quadratic in each.
/// So the pass keeps its sums at every point of `{0, 1, inf}` per variable, `inf` the leading coefficient.
///
/// ```text
///     G(Y) = sum_p  prod_d B_{p_d}(rho_d) * S(p, Y)        B_0 = 1 + rho,  B_1 = rho,  B_inf = rho (1 + rho)
/// ```
///
/// `S(p, Y)` sums the pass's later variables over their Boolean points, weighted by their eq challenges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RoundBatch {
    /// The rounds of the pass.
    rounds: usize,
    /// The sums at each point, by base-3 index, before the eq weights of the pass's variables.
    sums: [F192; POINTS],
    /// The eq challenges of the pass's variables after its first.
    r: [F192; 2],
}

impl RoundBatch {
    /// Two rounds from the eight sums of the quad terms, `r_v` the eq challenge of the second variable.
    fn pair(sums: [F192; 8], r_v: F192) -> Self {
        // The slots hold the points (1, 0), (1, 1), (inf, 0), (inf, 1), (0, 1), (0, inf), (1, inf), (inf, inf).
        let mut points = [F192::ZERO; POINTS];
        for (sum, point) in sums.into_iter().zip([1, 4, 2, 5, 3, 6, 7, 8]) {
            points[point] = sum;
        }
        Self {
            rounds: 2,
            sums: points,
            r: [r_v, F192::ZERO],
        }
    }

    /// The rounds the pass sends.
    pub(crate) const fn rounds(&self) -> usize {
        self.rounds
    }

    /// Round `t + i`'s `(G(1), G(inf))`, once the challenges `rhos` of the `i` rounds before it are known.
    pub(crate) fn round(&self, rhos: &[F192]) -> (F192, F192) {
        let i = rhos.len();
        assert!(i < self.rounds, "a round of the pass");
        // The weights of the earlier variables' points, the latest variable the highest digit.
        let mut prefix = vec![F192::ONE];
        for &rho in rhos {
            let basis = [F192::ONE + rho, rho, rho * (F192::ONE + rho)];
            prefix = basis.iter().flat_map(|&w| prefix.iter().map(move |&p| p * w)).collect();
        }
        // The eq weights of the later variables.
        let suffix = eq_table(&self.r[i..self.rounds - 1]);
        let place = 3usize.pow(i as u32);
        let at = |y: usize| {
            (suffix.iter().enumerate()).fold(F192::ZERO, |g, (s, &e)| {
                let sums = &self.sums[3 * place * ternary(s) + place * y..];
                g + e * (prefix.iter().zip(sums)).fold(F192::ZERO, |acc, (&w, &sum)| acc + w * sum)
            })
        };
        (at(1), at(2))
    }
}

/// One quad's terms of two consecutive rounds, before its eq weight.
///
/// The quad is positions `4k + u + 2v`, `u` the first round's variable and `v` the second's.
///
/// Returns the eight products the two rounds sum, in the slots a two-round batch reads.
#[inline(always)]
fn quad_pair_terms(
    [a0, a1, a2, a3]: [F192; 4],
    [b0, b1, b2, b3]: [F192; 4],
    [_, c1, c2, c3]: [F192; 4],
) -> [(F192, F192, F192, F192); 2] {
    // Leading coefficients along `u` (positions 0,1 and 2,3) and along `v` (0,2 and 1,3).
    let (du0, du1, dv0, dv1) = (a0 + a1, a2 + a3, a0 + a2, a1 + a3);
    let (eu0, eu1, ev0, ev1) = (b0 + b1, b2 + b3, b0 + b2, b1 + b3);
    let (p1, p2, p3, q0) = mul_quad((a1, a2, a3, du0), (b1, b2, b3, eu0));
    let (q1, r0, r1, r2) = mul_quad((du1, dv0, dv1, du0 + du1), (eu1, ev0, ev1, eu0 + eu1));
    [(p1 + c1, p3 + c3, q0, q1), (p2 + c2, r0, r1, r2)]
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
pub(crate) fn bit_round_pair(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> RoundBatch {
    let sums = match fold.n_chunks() {
        8 => bit_round_pair_kernel::<8>(bits, fold, r_eq, padding),
        16 => bit_round_pair_kernel::<16>(bits, fold, r_eq, padding),
        32 => bit_round_pair_kernel::<32>(bits, fold, r_eq, padding),
        64 => bit_round_pair_kernel::<64>(bits, fold, r_eq, padding),
        128 => bit_round_pair_kernel::<128>(bits, fold, r_eq, padding),
        n => panic!("no bit-round kernel for {n}-byte rows"),
    };
    RoundBatch::pair(sums, r_eq[0])
}

/// Rounds `t`, `t + 1` and `t + 2` straight from the packed bits, the folded tables never stored.
pub(crate) fn bit_round_triple(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> RoundBatch {
    let sums = match fold.n_chunks() {
        8 => bit_round_triple_kernel::<8>(bits, fold, r_eq, padding),
        16 => bit_round_triple_kernel::<16>(bits, fold, r_eq, padding),
        32 => bit_round_triple_kernel::<32>(bits, fold, r_eq, padding),
        64 => bit_round_triple_kernel::<64>(bits, fold, r_eq, padding),
        128 => bit_round_triple_kernel::<128>(bits, fold, r_eq, padding),
        n => panic!("no bit-round kernel for {n}-byte rows"),
    };
    RoundBatch {
        rounds: 3,
        sums,
        r: [r_eq[0], r_eq[1]],
    }
}

/// One round straight from the packed bits, storing the folded `(a, b, c)` tables for the rounds that follow.
///
/// Returns the round's `(G(1), G(inf))`, then the three tables.
pub(crate) fn bit_round_materialize(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> ((F192, F192), [Vec<F192>; 3]) {
    let n_pos = bits.a.len() / fold.n_chunks();
    let mut out: [Box<[MaybeUninit<F192>]>; 3] = std::array::from_fn(|_| Box::new_uninit_slice(n_pos));
    let outs = out.each_mut().map(|o| &mut o[..]);
    let message = match fold.n_chunks() {
        8 => bit_round_store_kernel::<8>(bits, fold, r_eq, padding, outs),
        16 => bit_round_store_kernel::<16>(bits, fold, r_eq, padding, outs),
        32 => bit_round_store_kernel::<32>(bits, fold, r_eq, padding, outs),
        64 => bit_round_store_kernel::<64>(bits, fold, r_eq, padding, outs),
        128 => bit_round_store_kernel::<128>(bits, fold, r_eq, padding, outs),
        256 => bit_round_store_kernel::<256>(bits, fold, r_eq, padding, outs),
        n => panic!("no bit-round kernel for {n}-byte rows"),
    };
    // SAFETY: the kernel writes every slot, padding and tail included.
    (message, out.map(|o| unsafe { o.assume_init() }.into_vec()))
}

/// The two-round pass, for rows of `CHUNKS` bytes: the eight sums of a two-round batch.
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
) -> [F192; 8] {
    let rows = bits.rows::<CHUNKS>();
    let n_quads = rows[0].len() / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);

    // `r_eq[0]` weights round `t`'s split by `v`; the rest weight the quads.
    let r_quad = &r_eq[1..];
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_low_vars(r_quad, EQ_LO_VARS);
    let lo_size = eq_lo.len();

    // A quad covers 2^6 skip bits times its 4 * 2^t bound rows.
    let quad_log = (32 * CHUNKS).trailing_zeros() as usize;
    let (quad_in_block_mask, live_quads) = padding_pairs(padding, quad_log - 1);
    // The quads before the tail, in whole folded blocks of sixteen.
    let m = quad_log + n_quads.trailing_zeros() as usize;
    let tail = padding.tail(m, quad_log, quad_log + 4, r_eq);
    let head_quads = tail.map_or(n_quads, |t| t.head >> quad_log);
    let live = |quad: usize| quad < head_quads && (quad & quad_in_block_mask) < live_quads;

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    let eq_planes = (lo_size >= BLOCK / 4).then(|| planar::planes(&eq_lo));

    let mut sums = parallel::map_reduce(
        head_quads.div_ceil(lo_size),
        || [F192::ZERO; 8],
        |hi| {
            #[cfg(all(
                target_arch = "x86_64",
                target_feature = "gfni",
                target_feature = "avx512bw",
                target_feature = "avx512vbmi",
                target_feature = "avx512f",
                target_feature = "vpclmulqdq"
            ))]
            if let Some(eq_planes) = &eq_planes {
                // SAFETY: the target features are enabled at compile time.
                let acc = unsafe { planar::quad_sums(fold, rows, hi * lo_size, eq_planes, live) };
                return acc.map(|s| eq_hi[hi] * s.reduce());
            }
            let mut acc = [F192Unreduced::ZERO; 8];
            let mut f = FoldedBlock::ZERO;
            // Sixteen quads per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 4) {
                let n = (lo_size - lo_first).min(BLOCK / 4);
                let quad_first = hi * lo_size + lo_first;
                // A block wholly in padding folds to zero, and the tail is summed apart.
                if !(quad_first..quad_first + n).any(live) {
                    continue;
                }
                f.fold(fold, rows, 4 * quad_first, 4 * n);
                for i in 0..n {
                    let quad = |t: &[F192; BLOCK]| -> [F192; 4] { t[4 * i..4 * i + 4].try_into().expect("a quad") };
                    let [lo, hi] = quad_pair_terms(quad(&f.a), quad(&f.b), quad(&f.c));

                    // Every term of the quad shares one eq weight.
                    let eq = eq_lo[lo_first + i];
                    let e = (eq, eq, eq, eq);
                    let (s0, s1, s2, s3) = mul_quad_unreduced(e, lo);
                    let (s4, s5, s6, s7) = mul_quad_unreduced(e, hi);
                    for (acc, s) in acc.iter_mut().zip([s0, s1, s2, s3, s4, s5, s6, s7]) {
                        *acc ^= s;
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        let group = PackedWitness {
            a: tail.group(bits.a),
            b: tail.group(bits.b),
        };
        let group_sums = bit_round_pair_kernel::<CHUNKS>(group, fold, &r_eq[..tail.r_inner], &padding.without_tail());
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
    }
    sums
}

/// The sums extending values on `{0, 1}^3` to `{0, 1, inf}^3`, as `(t, t - place, t - 2 place)`.
///
/// Variable `d` extends after the lower ones, at the points whose higher variables are still Boolean.
const EXTEND: [(usize, usize, usize); 19] = {
    let mut sums = [(0, 0, 0); 19];
    let (mut n, mut place) = (0, 1);
    while place < POINTS {
        let mut t = 0;
        while t < POINTS {
            let above = t / (3 * place);
            if t / place % 3 == 2 && above % 3 != 2 && above / 3 % 3 != 2 {
                sums[n] = (t, t - place, t - 2 * place);
                n += 1;
            }
            t += 1;
        }
        place *= 3;
    }
    assert!(n == sums.len());
    sums
};

/// The `a b` terms of an octet: every point but `(0, 0, 0)`, which no round reads.
const AB_TERMS: usize = POINTS - 1;

/// The `eq c` terms of an octet: its Boolean points but 0, the only ones a linear term reaches.
const C_TERMS: usize = 7;

/// The point each term of an octet lands on, four terms per batched product, the padding on `(0, 0, 0)`.
const TERMS: [usize; 36] = {
    let mut terms = [0; 36];
    let mut k = 0;
    while k < AB_TERMS + C_TERMS {
        terms[k] = if k < AB_TERMS { k + 1 } else { ternary(k - AB_TERMS + 1) };
        k += 1;
    }
    terms
};

/// Values on `{0, 1}^3`, bit `d` of the index variable `d`, at every point of `{0, 1, inf}^3`.
#[inline(always)]
fn extend<T: Copy>(f: [T; 8], add: impl Fn(T, T) -> T) -> [T; POINTS] {
    let mut ext = [f[0]; POINTS];
    for (x, v) in f.into_iter().enumerate() {
        ext[ternary(x)] = v;
    }
    for (t, one, zero) in EXTEND {
        ext[t] = add(ext[one], ext[zero]);
    }
    ext
}

/// One octet's terms of three consecutive rounds, at its eq weight `eq`, added to `acc` by point.
///
/// The octet is positions `8k + x`, bit `d` of `x` the variable of round `t + d`.
///
/// Each value extends from the octet's Boolean points to all 27, so each point's term is one product.
/// The weight multiplies `a` before the extension, which is linear, so every product carries it.
/// The linear `c` has no `inf` coefficient: it reaches the Boolean points only.
#[inline(always)]
fn octet_terms(eq: F192, a: [F192; 8], b: [F192; 8], c: [F192; 8], acc: &mut [F192Unreduced; POINTS]) {
    let e = (eq, eq, eq, eq);
    let lo = mul_quad(e, (a[0], a[1], a[2], a[3]));
    let hi = mul_quad(e, (a[4], a[5], a[6], a[7]));
    let ea = extend([lo.0, lo.1, lo.2, lo.3, hi.0, hi.1, hi.2, hi.3], |x, y| x + y);
    let eb = extend(b, |x, y| x + y);
    let term = |k: usize| match k {
        k if k < AB_TERMS => (ea[k + 1], eb[k + 1]),
        k if k < AB_TERMS + C_TERMS => (eq, c[k - AB_TERMS + 1]),
        _ => (F192::ZERO, F192::ZERO),
    };
    let (lhs, rhs): ([F192; 36], [F192; 36]) = (std::array::from_fn(|k| term(k).0), std::array::from_fn(|k| term(k).1));
    for ((l, r), d) in lhs
        .as_chunks::<4>()
        .0
        .iter()
        .zip(rhs.as_chunks::<4>().0)
        .zip(TERMS.as_chunks::<4>().0)
    {
        let p = mul_quad_unreduced((l[0], l[1], l[2], l[3]), (r[0], r[1], r[2], r[3]));
        for (&d, p) in d.iter().zip([p.0, p.1, p.2, p.3]) {
            acc[d] ^= p;
        }
    }
}

/// The three-round pass, for rows of `CHUNKS` bytes: its sums by point.
///
/// Positions group in octets, bit `d` of a position's index in its octet the variable of round `t + d`.
/// A third round costs products only: the fold and the bits read are a pair's.
fn bit_round_triple_kernel<const CHUNKS: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
) -> [F192; POINTS] {
    let rows = bits.rows::<CHUNKS>();
    let n_octets = rows[0].len() / 8;
    assert!(n_octets >= 1, "three rounds need eight positions");
    assert_eq!(r_eq.len(), n_octets.trailing_zeros() as usize + 2);

    // `r_eq[..2]` weigh the octet's later variables; the rest weigh the octets.
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_low_vars(&r_eq[2..], EQ_LO_VARS);
    let lo_size = eq_lo.len();

    // An octet covers 2^6 skip bits times its 8 * 2^t bound rows.
    let octet_log = (64 * CHUNKS).trailing_zeros() as usize;
    let (octet_in_block_mask, live_octets) = padding_pairs(padding, octet_log - 1);
    // The octets before the tail, in whole folded blocks of eight.
    let m = octet_log + n_octets.trailing_zeros() as usize;
    let tail = padding.tail(m, octet_log, octet_log + 3, r_eq);
    let head_octets = tail.map_or(n_octets, |t| t.head >> octet_log);
    let live = |octet: usize| octet < head_octets && (octet & octet_in_block_mask) < live_octets;

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    let eq_planes = (lo_size >= BLOCK / 8).then(|| planar::planes(&eq_lo));

    let mut sums = parallel::map_reduce(
        head_octets.div_ceil(lo_size),
        || [F192::ZERO; POINTS],
        |hi| {
            #[cfg(all(
                target_arch = "x86_64",
                target_feature = "gfni",
                target_feature = "avx512bw",
                target_feature = "avx512vbmi",
                target_feature = "avx512f",
                target_feature = "vpclmulqdq"
            ))]
            if let Some(eq_planes) = &eq_planes {
                // SAFETY: the target features are enabled at compile time.
                let acc = unsafe { planar::octet_sums(fold, rows, hi * lo_size, eq_planes, live) };
                return acc.map(|s| eq_hi[hi] * s.reduce());
            }
            let mut acc = [F192Unreduced::ZERO; POINTS];
            let mut f = FoldedBlock::ZERO;
            // Eight octets per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 8) {
                let n = (lo_size - lo_first).min(BLOCK / 8);
                let octet_first = hi * lo_size + lo_first;
                // A block wholly in padding folds to zero, and the tail is summed apart.
                if !(octet_first..octet_first + n).any(live) {
                    continue;
                }
                f.fold(fold, rows, 8 * octet_first, 8 * n);
                for i in 0..n {
                    let octet = |t: &[F192; BLOCK]| -> [F192; 8] { t[8 * i..8 * i + 8].try_into().expect("an octet") };
                    octet_terms(eq_lo[lo_first + i], octet(&f.a), octet(&f.b), octet(&f.c), &mut acc);
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        let group = PackedWitness {
            a: tail.group(bits.a),
            b: tail.group(bits.b),
        };
        let group_sums = bit_round_triple_kernel::<CHUNKS>(group, fold, &r_eq[..tail.r_inner], &padding.without_tail());
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
    }
    sums
}

/// The storing single-round pass, for rows of `CHUNKS` bytes, writing the folded tables to `outs`.
///
/// Positions pair up as `(2k, 2k + 1)`, the low index bit being the variable this round binds.
///
/// The identical tail's tables are copies of its last group's.
fn bit_round_store_kernel<const CHUNKS: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &PaddingSpec,
    mut outs: [&mut [MaybeUninit<F192>]; 3],
) -> (F192, F192) {
    let rows = bits.rows::<CHUNKS>();
    let n_pos = rows[0].len();
    assert!(n_pos >= 2, "a round needs two positions");
    assert_eq!(r_eq.len(), n_pos.trailing_zeros() as usize - 1);

    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_low_vars(r_eq, EQ_LO_VARS);
    let lo_size = eq_lo.len();

    // A position covers 2^6 skip bits times its 2^t bound rows.
    let position_log = (8 * CHUNKS).trailing_zeros() as usize;
    let (pair_in_block_mask, live_pairs) = padding_pairs(padding, position_log);
    let live = |pair: usize| (pair & pair_in_block_mask) < live_pairs;
    // The pairs before the tail, in whole folded blocks of thirty-two.
    let m = position_log + n_pos.trailing_zeros() as usize;
    let tail = padding.tail(m, position_log + 1, position_log + 6, r_eq);
    let head_pairs = tail.map_or(n_pos / 2, |t| t.head >> (position_log + 1));

    assert!(outs.iter().all(|o| o.len() == n_pos), "one output per position");
    let chunks = outs.each_mut().map(|o| Chunks::new(o, 2 * lo_size));

    let mut message = parallel::map_reduce(
        head_pairs.div_ceil(lo_size),
        || (F192::ZERO, F192::ZERO),
        |hi| {
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let [oa, ob, oc] = chunks.map(|ch| unsafe { ch.get(hi) });
            let stream = Stream::new();
            let mut f = FoldedBlock::ZERO;
            let mut g1_acc = F192Unreduced::ZERO;
            let mut ginf_acc = F192Unreduced::ZERO;
            // Thirty-two pairs per folded block.
            for lo_first in (0..lo_size).step_by(BLOCK / 2) {
                let n = (lo_size - lo_first).min(BLOCK / 2);
                let pair_first = hi * lo_size + lo_first;
                // The tail is copied after the dispatch.
                if pair_first >= head_pairs {
                    break;
                }
                let (o_first, o_len) = (2 * lo_first, 2 * n);
                // A block wholly in padding folds to zero.
                if !(pair_first..pair_first + n).any(live) {
                    for o in [&mut *oa, &mut *ob, &mut *oc] {
                        o[o_first..o_first + o_len].fill(MaybeUninit::new(F192::ZERO));
                    }
                    continue;
                }
                f.fold(fold, rows, 2 * pair_first, o_len);

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
                            stream.write(d, s);
                        }
                    }
                } else {
                    oa[dst.clone()].write_copy_of_slice(&f.a[..o_len]);
                    ob[dst.clone()].write_copy_of_slice(&f.b[..o_len]);
                    oc[dst].write_copy_of_slice(&f.c[..o_len]);
                }
            }
            (eq_hi[hi] * g1_acc.reduce(), eq_hi[hi] * ginf_acc.reduce())
        },
        |(s1, si), (t1, ti)| (s1 + t1, si + ti),
    );
    if let Some(tail) = tail {
        // The last group is stored in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - position_log);
        let group = PackedWitness {
            a: tail.group(bits.a),
            b: tail.group(bits.b),
        };
        let (g1, g_inf) = bit_round_store_kernel::<CHUNKS>(
            group,
            fold,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            outs.each_mut().map(|o| &mut o[n_pos - group_len..]),
        );
        message.0 += tail.weight * g1;
        message.1 += tail.weight * g_inf;
        copy_group(outs, 2 * head_pairs, group_len);
    }
    message
}

/// Rounds `t` and `t + 1` from the stored tables, folding the challenges still pending on them first.
///
/// - `ins` are the `(a, b, c)` tables, `rhos.len()` variables short of level `t`: one or two.
/// - `rhos` are those variables' challenges, lowest first; each output folds `2^rhos.len()` inputs.
/// - `outs` receive the level-`t` tables, `ins.len() >> rhos.len()` values each, every slot written.
/// - `r_eq` are the eq challenges of the variables round `t` does not bind.
/// - `padding` is the witness's, and each output covers `2^out_log` of its bits.
///
/// ```text
///     two pending:  read level t - 2 (n)  ->  write level t (n / 4)  +  rounds t, t + 1
///     one round at a time:  n + n / 2 + n / 2 + n / 4 for the same two rounds
/// ```
///
/// The rounds are built from each quad of folded values while they are in registers, as in the bit pass.
pub(crate) fn fold_and_round_pair_into(
    ins: [&[F192]; 3],
    outs: [&mut [MaybeUninit<F192>]; 3],
    rhos: &[F192],
    r_eq: &[F192],
    padding: &PaddingSpec,
    out_log: usize,
) -> RoundBatch {
    let sums = match *rhos {
        [rho] => fold_and_round_pair_kernel::<1>(ins, outs, [rho, F192::ZERO], r_eq, padding, out_log),
        [rho_0, rho_1] => fold_and_round_pair_kernel::<2>(ins, outs, [rho_0, rho_1], r_eq, padding, out_log),
        _ => panic!("one or two pending challenges"),
    };
    RoundBatch::pair(sums, r_eq[0])
}

/// The paired pass for `K` pending challenges, `rhos[..K]`: the eight sums of a two-round batch.
///
/// The identical tail's outputs are copies of its last group's.
fn fold_and_round_pair_kernel<const K: usize>(
    ins: [&[F192]; 3],
    mut outs: [&mut [MaybeUninit<F192>]; 3],
    rhos: [F192; 2],
    r_eq: &[F192],
    padding: &PaddingSpec,
    out_log: usize,
) -> [F192; 8] {
    let n_out = ins[0].len() >> K;
    assert!(ins.iter().all(|t| t.len() == n_out << K), "a, b, c have one length");
    assert!(
        outs.iter().all(|t| t.len() == n_out),
        "each output is the folded length"
    );
    let n_quads = n_out / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);

    // `r_eq[0]` weighs round `t`'s split by `v`; the rest weigh the quads.
    //
    // Up to 2^7 high eq indices, one task each: enough tasks for every worker at every table size.
    let r_quad = &r_eq[1..];
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_high_vars(r_quad, EQ_HIGH_VARS);
    let lo_size = eq_lo.len();

    // The quads before the tail, in the pairs the outputs are published in.
    let quad_log = out_log + 2;
    let m = quad_log + n_quads.trailing_zeros() as usize;
    let tail = padding.tail(m, quad_log, quad_log + 1, r_eq);
    let head_quads = tail.map_or(n_quads, |t| t.head >> quad_log);

    // One task per high eq index: `lo_size` quads, `4 * lo_size` outputs of each table.
    let (chunk_in, chunk_out) = ((4 * lo_size) << K, 4 * lo_size);
    let chunks = outs.each_mut().map(|o| Chunks::new(o, chunk_out));
    let rho = |j: usize| (rhos[j], rhos[j], rhos[j], rhos[j]);

    // Four outputs of one table, each folded from its `2^K` inputs.
    //
    //     one pending:   z = x_0 + rho_0 (x_0 + x_1)
    //     two pending:   y_lo = x_0 + rho_0 (x_0 + x_1),  y_hi = x_2 + rho_0 (x_2 + x_3)
    //                    z = y_lo + rho_1 (y_lo + y_hi)
    let fold_quad = |g: &[F192]| -> [F192; 4] {
        // The four outputs' inputs, `2^K` each.
        let g = &g[..4 << K];
        let x = |j: usize, i: usize| g[(j << K) + i];
        let d = mul_quad(
            (
                x(0, 0) + x(0, 1),
                x(1, 0) + x(1, 1),
                x(2, 0) + x(2, 1),
                x(3, 0) + x(3, 1),
            ),
            rho(0),
        );
        let lo = [x(0, 0) + d.0, x(1, 0) + d.1, x(2, 0) + d.2, x(3, 0) + d.3];
        if K == 1 {
            return lo;
        }
        let e = mul_quad(
            (
                x(0, 2) + x(0, 3),
                x(1, 2) + x(1, 3),
                x(2, 2) + x(2, 3),
                x(3, 2) + x(3, 3),
            ),
            rho(0),
        );
        let hi = [x(0, 2) + e.0, x(1, 2) + e.1, x(2, 2) + e.2, x(3, 2) + e.3];
        let f = mul_quad((lo[0] + hi[0], lo[1] + hi[1], lo[2] + hi[2], lo[3] + hi[3]), rho(1));
        [lo[0] + f.0, lo[1] + f.1, lo[2] + f.2, lo[3] + f.3]
    };

    let mut sums = parallel::map_reduce(
        head_quads.div_ceil(lo_size),
        || [F192::ZERO; 8],
        |hi| {
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let mut outs = chunks.map(|ch| unsafe { ch.get(hi) });
            let ins = ins.map(|t| &t[hi * chunk_in..(hi + 1) * chunk_in]);
            let stream = Stream::new();
            let mut acc = [F192Unreduced::ZERO; 8];
            // Two quads of a table are eight outputs, three whole cache lines, published at once.
            let mut staged = [[F192::ZERO; 8]; 3];
            let n_q = lo_size.min(head_quads - hi * lo_size);
            for q in 0..n_q {
                let [a, b, c] = ins.map(|t| fold_quad(&t[(4 * q) << K..(4 * (q + 1)) << K]));
                let [lo, hi] = quad_pair_terms(a, b, c);

                // Every term of the quad shares one eq weight.
                let eq = eq_lo[q];
                let e = (eq, eq, eq, eq);
                let (s0, s1, s2, s3) = mul_quad_unreduced(e, lo);
                let (s4, s5, s6, s7) = mul_quad_unreduced(e, hi);
                for (acc, s) in acc.iter_mut().zip([s0, s1, s2, s3, s4, s5, s6, s7]) {
                    *acc ^= s;
                }

                // Publish the folded values without a read: nothing touches them before the next pass.
                let half = 4 * (q % 2);
                for (stage, folded) in staged.iter_mut().zip([a, b, c]) {
                    stage[half..half + 4].copy_from_slice(&folded);
                }
                if q % 2 == 1 {
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        stream.write(&mut out[4 * (q - 1)..4 * (q + 1)], stage);
                    }
                } else if q + 1 == n_q {
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        out[4 * q..4 * q + 4].write_copy_of_slice(&stage[..4]);
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        // The last group is folded in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - out_log);
        let group_ins = ins.map(|t| &t[t.len() - (group_len << K)..]);
        let group_sums = fold_and_round_pair_kernel::<K>(
            group_ins,
            outs.each_mut().map(|o| &mut o[n_out - group_len..]),
            rhos,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            out_log,
        );
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
        copy_group(outs, head_quads * 4, group_len);
    }
    sums
}

/// Copy each table's last `group_len` values over its values from `head` on.
fn copy_group(tables: [&mut [MaybeUninit<F192>]; 3], head: usize, group_len: usize) {
    // Whole groups per copy task, about 2^12 values.
    let task = group_len.max(1 << 12);
    for t in tables {
        let tail = &mut t[head..];
        let (body, group) = tail.split_at_mut(tail.len() - group_len);
        let group = &*group;
        parallel::chunks_mut(body, task, |_, dst| {
            for d in dst.chunks_exact_mut(group_len) {
                d.copy_from_slice(group);
            }
        });
    }
}

/// In-place fold of a single multilinear polynomial table at `challenge`.
/// Pairs `(a[2x], a[2x+1])` collapse to `a[x] = a[2x] + challenge · (a[2x+1] + a[2x])`.
/// After the call, `a.len()` is halved.
pub(crate) fn fold_in_place_single(a: &mut Vec<F192>, challenge: F192) {
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
pub(crate) fn fold_in_place_pair(a: &mut Vec<F192>, b: &mut Vec<F192>, challenge: F192) {
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

/// The two-round pass on coefficient planes: eight quads per register, so no product packs or unpacks a value.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "avx512f",
    target_feature = "vpclmulqdq"
))]
mod planar {
    use core::arch::x86_64::__m512i;
    use core::mem::transmute;

    use super::{POINTS, ternary};
    use primitives::bit_fold::{BLOCK, BitFold};
    use primitives::field::gf2_64x3::x86_64::{F192x8, F192x8Sum};
    use primitives::field::{F192, F192Unreduced};

    /// Eight consecutive values per entry, in planes.
    pub(super) fn planes(values: &[F192]) -> Vec<F192x8> {
        let (groups, rest) = values.as_chunks::<8>();
        assert!(rest.is_empty(), "whole groups of eight");
        groups
            .iter()
            .map(|g| {
                // SAFETY: eight qwords are one register.
                let plane = |k: fn(&F192) -> u64| unsafe { transmute::<[u64; 8], __m512i>(g.each_ref().map(k)) };
                F192x8([plane(|e| e.c0), plane(|e| e.c1), plane(|e| e.c2)])
            })
            .collect()
    }

    /// The eight sums of [`super::quad_pair_terms`] over the quads `quad_first..`, one per `eq` entry's eight.
    ///
    /// The eq weight multiplies the four `a` values first, so each sum's terms are products of `eq * a` combinations:
    ///
    /// ```text
    ///     eq * (a_1 b_1 + c_1) = (eq a_1) b_1 + eq c_1          eq * du_0 eu_0 = (eq a_0 + eq a_1)(b_0 + b_1)
    /// ```
    ///
    /// Fifteen products per quad, four of them reduced, against sixteen with eight reduced.
    #[inline]
    #[target_feature(
        enable = "avx512f",
        enable = "avx512bw",
        enable = "avx512vbmi",
        enable = "gfni",
        enable = "vpclmulqdq"
    )]
    pub(super) fn quad_sums<const CHUNKS: usize>(
        fold: &BitFold,
        rows: [&[[u8; CHUNKS]]; 2],
        quad_first: usize,
        eq: &[F192x8],
        live: impl Fn(usize) -> bool,
    ) -> [F192Unreduced; 8] {
        let mut acc = [F192x8Sum::zero(); 8];
        // Sixteen quads per folded block, two registers of eight.
        for (b, eq) in eq.as_chunks::<2>().0.iter().enumerate() {
            let q0 = quad_first + (BLOCK / 4) * b;
            // A block wholly in padding folds to zero.
            if !(q0..q0 + BLOCK / 4).any(&live) {
                continue;
            }
            let [ra, rb]: [&[[u8; CHUNKS]; BLOCK]; 2] =
                rows.map(|t| t[4 * q0..4 * q0 + BLOCK].try_into().expect("a block"));
            let mut rc = [[0u8; CHUNKS]; BLOCK];
            super::and_rows(ra, rb, &mut rc);
            let [pa, pb, pc] = [ra, rb, &rc].map(|t| fold.fold_quads::<CHUNKS>(t));
            for (g, &e) in eq.iter().enumerate() {
                let at =
                    |p: &[[__m512i; 8]; 3], uv: usize| F192x8([p[0][uv + 4 * g], p[1][uv + 4 * g], p[2][uv + 4 * g]]);
                let [a0, a1, a2, a3] = [0, 1, 2, 3].map(|uv| e.mul(at(&pa, uv)));
                let [b0, b1, b2, b3] = [0, 1, 2, 3].map(|uv| at(&pb, uv));
                let [c1, c2, c3] = [1, 2, 3].map(|uv| at(&pc, uv));
                let (du0, du1, dv0, dv1) = (a0.add(a1), a2.add(a3), a0.add(a2), a1.add(a3));
                let (eu0, eu1, ev0, ev1) = (b0.add(b1), b2.add(b3), b0.add(b2), b1.add(b3));
                acc[0].mul_add(a1, b1);
                acc[0].mul_add(e, c1);
                acc[1].mul_add(a3, b3);
                acc[1].mul_add(e, c3);
                acc[2].mul_add(du0, eu0);
                acc[3].mul_add(du1, eu1);
                acc[4].mul_add(a2, b2);
                acc[4].mul_add(e, c2);
                acc[5].mul_add(dv0, ev0);
                acc[6].mul_add(dv1, ev1);
                acc[7].mul_add(du0.add(du1), eu0.add(eu1));
            }
        }
        acc.map(|s| s.total())
    }

    /// The octet sums over the octets `octet_first..`, eight per `eq` entry.
    #[inline]
    #[target_feature(
        enable = "avx512f",
        enable = "avx512bw",
        enable = "avx512vbmi",
        enable = "gfni",
        enable = "vpclmulqdq"
    )]
    pub(super) fn octet_sums<const CHUNKS: usize>(
        fold: &BitFold,
        rows: [&[[u8; CHUNKS]]; 2],
        octet_first: usize,
        eq: &[F192x8],
        live: impl Fn(usize) -> bool,
    ) -> [F192Unreduced; POINTS] {
        let mut acc = [F192x8Sum::zero(); POINTS];
        // Eight octets per folded block, one register of eight.
        for (b, &e) in eq.iter().enumerate() {
            let o0 = octet_first + (BLOCK / 8) * b;
            // A block wholly in padding folds to zero.
            if !(o0..o0 + BLOCK / 8).any(&live) {
                continue;
            }
            let [ra, rb]: [&[[u8; CHUNKS]; BLOCK]; 2] =
                rows.map(|t| t[8 * o0..8 * o0 + BLOCK].try_into().expect("a block"));
            let mut rc = [[0u8; CHUNKS]; BLOCK];
            super::and_rows(ra, rb, &mut rc);
            let [pa, pb, pc] = [ra, rb, &rc].map(|t| fold.fold_octets::<CHUNKS>(t));
            let at = |p: &[[__m512i; 8]; 3], x: usize| F192x8([p[0][x], p[1][x], p[2][x]]);
            let add = |x: F192x8, y: F192x8| x.add(y);
            let ea = super::extend(std::array::from_fn(|x| e.mul(at(&pa, x))), add);
            let eb = super::extend(std::array::from_fn(|x| at(&pb, x)), add);
            for t in 1..POINTS {
                acc[t].mul_add(ea[t], eb[t]);
            }
            for x in 1..8 {
                acc[ternary(x)].mul_add(e, at(&pc, x));
            }
        }
        acc.map(|s| s.total())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zerocheck::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
    use crate::zerocheck::round1::tests::pack_bits;
    use crate::zerocheck::round1::{
        c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges,
    };
    use primitives::field::F8;
    use primitives::field::PHI_8_TABLE_192;
    use primitives::multilinear::{barycentric_sum, skip_lagrange_weights, window_denominator};
    use primitives::test_util::Rng;

    /// Evaluate the univariate-skip polynomial at the fold point `z`, given the
    /// precomputed Lagrange `weights`. Returns the multilinear extension table
    /// `a_mlv` of length `2^(m − k_skip)` over F_{2^192}.
    ///
    ///   `a_mlv[x_rest] = Σ_s a(s, x_rest) · L_s(z)`
    ///
    /// `a(s, x_rest)` is the witness bit at index `x_rest * 2^k_skip + s` (low
    /// bits = skip variable, high bits = rest variables).
    fn fold_at_z_naive(witness: &[bool], m: usize, k_skip: usize, weights: &[F192]) -> Vec<F192> {
        assert!(k_skip <= m);
        let ell = 1usize << k_skip;
        let n_rest = 1usize << (m - k_skip);
        assert_eq!(witness.len(), 1usize << m);
        assert_eq!(weights.len(), ell);

        (0..n_rest)
            .map(|x_rest| {
                let bits = &witness[x_rest * ell..][..ell];
                (bits.iter().zip(weights))
                    .filter(|&(&bit, _)| bit)
                    .fold(F192::ZERO, |acc, (_, &w)| acc + w)
            })
            .collect()
    }

    /// Interpolate a degree-`< 2^k_skip` polynomial at z, given its `2^k_skip`
    /// evaluations on the **extension domain** `Λ = {2^k_skip, …, 2^(k_skip+1) − 1}`
    /// embedded via `φ_8` (offset by `2^k_skip` from the S-domain nodes).
    ///
    /// `P^C` no longer travels on its own (it rides the sum the prover sends), so
    /// this is only the cross-check handle: it turns the URM kernel's C Λ-vector
    /// into `P^C(z) = ĉ(z, r_rest)`, which a direct fold of the witness must match.
    fn interpolate_at_z_on_lambda(values: &[F192], k_skip: usize, z: F192) -> F192 {
        let ell = 1usize << k_skip;
        assert_eq!(values.len(), ell);
        assert!(2 * ell <= 256, "Λ ∪ S must fit in F_8 (need k_skip ≤ 7)");
        barycentric_sum(&PHI_8_TABLE_192[ell..2 * ell], values, z, window_denominator(ell))
    }

    #[test]
    fn fold_and_round_pair_matches_one_round_at_a_time() {
        // Invariant: folding the pending challenges and building two rounds in one pass
        // gives the tables and messages of folding and summing one round at a time.
        let mut rng = Rng::new(0x7AB1E);
        // Fixture state: one or two pending challenges, from one quad up to 2^10 of them.
        for k in [1usize, 2] {
            for log_out in [2usize, 3, 6, 12] {
                let n_in = 1usize << (log_out + k);
                let tables: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(n_in));
                let rhos = rng.ext_vec(k);
                let r_eq = rng.ext_vec(log_out - 1);
                let rho_t = rng.ext();

                // Reference: fold one challenge at a time, then sum each round from the tables.
                let [mut a, mut b, mut c] = tables.clone().map(|t| t.to_vec());
                for &rho in &rhos {
                    fold_in_place_pair(&mut a, &mut b, rho);
                    fold_in_place_single(&mut c, rho);
                }
                let (level_a, level_b, level_c) = (a.to_vec(), b.to_vec(), c.to_vec());
                let round = |a: &[F192], b: &[F192], c: &[F192], r_eq: &[F192]| {
                    let (g1, g_inf) = round_pair_naive(a, b, r_eq);
                    (g1 + round_single_naive(c, r_eq), g_inf)
                };
                let first = round(&a, &b, &c, &r_eq);
                fold_in_place_pair(&mut a, &mut b, rho_t);
                fold_in_place_single(&mut c, rho_t);
                let second = round(&a, &b, &c, &r_eq[1..]);

                // The pass under test.
                let mut outs: [Box<[MaybeUninit<F192>]>; 3] =
                    std::array::from_fn(|_| Box::new_uninit_slice(1 << log_out));
                let ins = [&tables[0][..], &tables[1][..], &tables[2][..]];
                let pair = fold_and_round_pair_into(
                    ins,
                    outs.each_mut().map(|o| &mut o[..]),
                    &rhos,
                    &r_eq,
                    &PaddingSpec::dense(log_out),
                    0,
                );
                // SAFETY: the pass writes every slot of its outputs.
                let outs = outs.map(|o| unsafe { o.assume_init() }.into_vec());
                assert_eq!(outs, [level_a, level_b, level_c], "tables, k={k}, log_out={log_out}");
                assert_eq!(pair.round(&[]), first, "round t, k={k}, log_out={log_out}");
                assert_eq!(pair.round(&[rho_t]), second, "round t + 1, k={k}, log_out={log_out}");
            }
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

            let mut a = a_orig.to_vec();
            let mut b = b_orig.to_vec();
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
                &r,
                &inv_table,
                &PaddingSpec::dense(m),
            );

            // Path A: interpolate round1_c at z, scale by C_s.
            let c_eval_via_interpolation = c_s() * interpolate_at_z_on_lambda(&round1_c, K_SKIP, z);

            // Path B: direct fold of c at z (Lagrange) then bind each
            // r_rest element with fold_in_place_single.
            let weights = skip_lagrange_weights(K_SKIP, z);
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

    /// A random honest `a, b, c = a AND b` witness over `2^m` slots, bits and packed.
    fn random_witness(rng: &mut Rng, m: usize) -> ([Vec<bool>; 3], [Vec<u8>; 3]) {
        let (a, b) = (rng.bits(1 << m), rng.bits(1 << m));
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        let bits = [a, b, c];
        let packed = [0, 1, 2].map(|i| pack_bits(&bits[i]));
        (bits, packed)
    }

    fn packed(p: &[Vec<u8>; 3]) -> PackedWitness<'_> {
        PackedWitness { a: &p[0], b: &p[1] }
    }

    /// The naive message of one round on stored tables: `(G(1), G(inf))` with `c` added to `G(1)`.
    fn naive_message(t: &[Vec<F192>; 3], r_eq: &[F192]) -> (F192, F192) {
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
            let lagrange = skip_lagrange_weights(K_SKIP, z);
            let dense = PaddingSpec::dense(m);

            // Level 0 of the naive route: the univariate-skip fold at z.
            let level0 = [0, 1, 2].map(|i| fold_at_z_naive(&bits[i], m, K_SKIP, &lagrange));
            // The naive messages of rounds `t..` with `rho[t..]` bound, from level `t`.
            let naive_rounds = |mut tables: [Vec<F192>; 3], t: usize, n: usize| -> Vec<(F192, F192)> {
                (t..t + n)
                    .map(|j| {
                        let message = naive_message(&tables, &r_rest[j + 1..]);
                        let [ta, tb, tc] = &mut tables;
                        fold_in_place_pair(ta, tb, rho[j]);
                        fold_in_place_single(tc, rho[j]);
                        message
                    })
                    .collect()
            };
            let mut tables = level0;
            for t in 0..=5 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let expected = naive_rounds(tables.clone(), t, (n_mlv - t).min(3));

                // The storing kernel: this level's message and tables.
                let (message, stored) = bit_round_materialize(packed(&packed_bits), &fold, r_eq, &dense);
                assert_eq!(message, expected[0], "store message, m={m}, t={t}");
                for (got, want) in stored.iter().zip(&tables) {
                    assert_eq!(&got[..], &want[..], "stored table, m={m}, t={t}");
                }

                // The batch kernels' later rounds land on the naive side's, once their challenges are bound.
                if t <= 4 {
                    let pair = bit_round_pair(packed(&packed_bits), &fold, r_eq, &dense);
                    let got: Vec<_> = (0..2).map(|i| pair.round(&rho[t..t + i])).collect();
                    assert_eq!(got, expected[..2], "pair, m={m}, t={t}");
                }
                if t <= 4 && t + 3 <= n_mlv {
                    let triple = bit_round_triple(packed(&packed_bits), &fold, r_eq, &dense);
                    let got: Vec<_> = (0..3).map(|i| triple.round(&rho[t..t + i])).collect();
                    assert_eq!(got, expected, "triple, m={m}, t={t}");
                }

                let [ta, tb, tc] = &mut tables;
                fold_in_place_pair(ta, tb, rho[t]);
                fold_in_place_single(tc, rho[t]);
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
                live_blocks: usize::MAX,
            };
            let lagrange = skip_lagrange_weights(K_SKIP, rng.ext());
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(5);
            for t in 0..=5 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                let run = |p: &PaddingSpec| {
                    let batches = (t <= 4).then(|| {
                        (
                            bit_round_pair(packed(&packed_bits), &fold, r_eq, p),
                            bit_round_triple(packed(&packed_bits), &fold, r_eq, p),
                        )
                    });
                    (batches, bit_round_materialize(packed(&packed_bits), &fold, r_eq, p))
                };
                let ((batch_d, (msg_d, tab_d)), (batch_p, (msg_p, tab_p))) =
                    (run(&PaddingSpec::dense(m)), run(&padding));
                assert_eq!(batch_d, batch_p, "pair and triple, m={m}, useful={useful}, t={t}");
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

        let weights = skip_lagrange_weights(k_skip, z);
        let a_mlv = fold_at_z_naive(&a, m, k_skip, &weights);
        let b_mlv = fold_at_z_naive(&b, m, k_skip, &weights);

        let n = a_mlv.len();
        let half = n / 2;
        let eq_remaining = eq_table(&r_eq);

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
