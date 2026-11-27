// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! WHIR with affine folds (Annex B, protocol `fig:protocol`): the commitment to a stack of `K` words, and the opening
//! of one weighted claim on it.
//!
//! Level 0 commits `K` words; every challenge, round message, weight and folded lane is `E`, and a deeper level
//! commits its `E` lanes as two `K` words each. The encoding domains and their twiddles lie in `K`.
//!
//! The opening runs Annex B's levels. Level `i`
//!
//! 1. folds its lanes `ell_i` times (`FoldRounds`): level 0 on the weight's terms (`whir_lanes`), the
//!    deeper levels in the clear (`Dense`);
//! 2. below the last level, commits the folded lane's low part as the next level's message and sends its high part,
//!    sends the message's value at an OOD point, draws the queries and `lambda`, opens its own oracle at the queries,
//!    and adds the OOD and query claims' weights to the weight, the queries' by `induce_basis`;
//! 3. at the last level, sends the folded lane, opens its oracle at the queries, and closes with the tail sumcheck.

use crate::sumcheck::product_sumcheck;
use fiat_shamir::merkle::{Hash, MerklePath};
use primitives::field::{Acc8, F64, F128, F128x8, dot, powers};
use primitives::hash::OUT_LEN;
use primitives::multilinear::{eq_table, fold};
use primitives::transcript::ProverState;

use crate::merkle::{LeafHasher, MerkleTree};
use crate::ntt::AdditiveNttF64;
use crate::whir_induce::induce_basis;
use crate::whir_lanes::{Folded, LaneRounds, Lanes};
use crate::xmul::x_at;
use verifier::{
    FOLD_GRINDING_BITS, INITIAL_FOLDING_FACTOR, MIN_LOG_INV_RATE, OOD_GRINDING_BITS, QUERY_GRINDING_BITS, WhirConfig,
};

/// Elements a task of a parallel pass takes.
const CHUNK: usize = 1 << 12;

/// [`dot`] with the pool.
fn dot_par(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    let chunk = |t: usize| t * CHUNK..((t + 1) * CHUNK).min(a.len());
    parallel::map_reduce(
        a.len().div_ceil(CHUNK),
        || F128::ZERO,
        |t| dot(&a[chunk(t)], &b[chunk(t)]),
        |a, v| a + v,
    )
}

/// A committed oracle: its codeword, kept whole, a row per domain point, and the Merkle tree over the rows.
pub(crate) struct ProverData {
    codeword: Vec<F64>,
    row_words: usize,
    /// The leaf's width. At level 0, `2^ell_0` `K` words, the last lane first, of which the row holds the committed
    /// lanes and the rest are zero. A deeper level's row is its leaf: `E` lanes, lane 0 first, two words each.
    leaf_words: usize,
    tree: MerkleTree,
}

impl ProverData {
    fn row(&self, q: usize) -> &[F64] {
        &self.codeword[q * self.row_words..][..self.row_words]
    }

    fn block_len(&self) -> usize {
        self.codeword.len() / self.row_words
    }

    pub(crate) fn root(&self) -> Hash {
        self.tree.root()
    }

    /// The Merkle paths of the rows at `queries`.
    fn open(&self, queries: &[usize]) -> Vec<MerklePath> {
        self.tree.open(queries, self.leaf_words, |q| self.row(q))
    }
}

/// Commit to the `K` message of a `2^log_n`-word stack: its leading lane blocks of
/// `2^(log_n - INITIAL_FOLDING_FACTOR)` words, zero past them, one codeword per lane, and a Merkle leaf per domain point
/// across the `2^INITIAL_FOLDING_FACTOR` lanes.
///
/// Only the lanes that carry data are encoded. The others' codewords are zero, and lane `t` of a row is message block
/// `n_lanes - 1 - t`, so the absent lanes' zeros lead the leaf, where their whole blocks of zeros are one sponge state
/// every leaf shares (Annex B, `sec:pcs-opt`).
pub(crate) fn commit(message: &[F64], log_n: usize, log_inv_rate: usize) -> ProverData {
    assert!(log_inv_rate >= MIN_LOG_INV_RATE && log_n > INITIAL_FOLDING_FACTOR);
    let log_rows = log_n - INITIAL_FOLDING_FACTOR;
    let n_lanes = message.len() >> log_rows;
    assert!(
        message.len() == n_lanes << log_rows && (1..=1 << INITIAL_FOLDING_FACTOR).contains(&n_lanes),
        "the message is whole lane blocks of the stack"
    );
    commit_words(
        message,
        n_lanes,
        1 << INITIAL_FOLDING_FACTOR,
        log_rows + log_inv_rate,
        log_inv_rate,
        true,
    )
}

/// Commit to a deeper level's `E` message, `2^log_msg_cols` rows of `2^log_lanes` lanes.
fn commit_ext(message: &[F128], log_msg_cols: usize, log_lanes: usize, log_inv_rate: usize) -> ProverData {
    assert_eq!(message.len(), 1 << (log_msg_cols + log_lanes));
    let words = primitives::cast_slice(message);
    commit_words(
        words,
        2 << log_lanes,
        2 << log_lanes,
        log_msg_cols + log_inv_rate,
        log_inv_rate,
        false,
    )
}

/// The oracle of `message`'s codeword on `2^log_domain` rows of `row_words`, leaves of `leaf_words`: the message lane
/// by lane ([`AdditiveNttF64::encode_lane_major`]) or row by row ([`AdditiveNttF64::encode_rows`]).
fn commit_words(
    message: &[F64],
    row_words: usize,
    leaf_words: usize,
    log_domain: usize,
    log_inv_rate: usize,
    lane_major: bool,
) -> ProverData {
    let hasher = LeafHasher::new(row_words, leaf_words);
    let mut leaves = parallel::filled(1 << log_domain, [0u8; OUT_LEN]);
    let (ntt, hash) = (
        AdditiveNttF64::standard(log_domain),
        &|rows: &[F64], out: &mut [Hash]| hasher.hash(rows, out),
    );
    let codeword = if lane_major {
        ntt.encode_lane_major(message, row_words, log_inv_rate, &mut leaves, hash)
    } else {
        ntt.encode_rows(message, row_words, log_inv_rate, &mut leaves, hash)
    };
    ProverData {
        codeword,
        row_words,
        leaf_words,
        tree: MerkleTree::from_leaves(leaves),
    }
}

/// The challenges of one fold round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FoldChallenges {
    pub(crate) alpha: F128,
    pub(crate) beta: F128,
}

/// What a fold round sends, with `W_i` the weight on the lanes whose folded bit is `i`:
/// `[v_G, v_F, t_0, t_1] = [<W_0, G>, <W_0 + W_1, F>, <W_0, X F>, <W_1, X F>]`.
pub(crate) type FoldTable = [F128; 4];

/// A level's fold rounds: each pairs the lanes `F` (folded bit 0) and `G` (folded bit 1) and sends their
/// [`FoldTable`]; after `(alpha, beta)` the lanes become `P = G + (alpha + beta X) F`, one coefficient longer, and the
/// weight `W(alpha, .)`. The weight covers a lane's low `2^mu` coefficients only, and so do the inner products: the
/// low coefficients of `X F` depend only on those of `F`.
pub(crate) trait FoldRounds {
    fn table(&mut self) -> FoldTable;
    fn fold(&mut self, ch: &FoldChallenges);
}

/// A level's `k` fold rounds: each round's table, then `(alpha, beta)` after a grind.
fn fold_rounds(ps: &mut ProverState, lanes: &mut dyn FoldRounds, k: usize) {
    for _ in 0..k {
        ps.add_scalars(&lanes.table());
        ps.grind(FOLD_GRINDING_BITS);
        let ch = FoldChallenges {
            alpha: ps.sample(),
            beta: ps.sample(),
        };
        lanes.fold(&ch);
    }
}

/// A deeper level's lanes and the weight over each lane's `low` low coefficients, in the clear and lane by lane: lane
/// `l` of the weight at `l * low_stride`, zero past `low`. A round's pairs are lanes `(2m, 2m + 1)`.
pub(crate) struct Dense {
    f: Folded,
    w: Vec<F128>,
    low: usize,
    low_stride: usize,
}

impl Dense {
    /// The `n_lanes` lanes of `p` under the weight `w` over their low coefficients, coefficient `c` of lane `l` at
    /// `c * n_lanes + l` in both.
    pub(crate) fn new(p: &[F128], w: &[F128], n_lanes: usize) -> Self {
        let w = Folded::transpose(w, n_lanes);
        Self {
            f: Folded::transpose(p, n_lanes),
            low: w.len,
            low_stride: w.stride,
            w: w.coefs,
        }
    }

    /// The one lane left, low coefficients then high, and the weight over its low ones.
    pub(crate) fn finish(self) -> (Vec<F128>, Vec<F128>) {
        let mut w = self.w;
        w.truncate(self.low);
        (self.f.into_lane(), w)
    }
}

impl FoldRounds for Dense {
    fn table(&mut self) -> FoldTable {
        let (f, low) = (&self.f, self.low);
        let n_chunks = low.div_ceil(CHUNK);
        parallel::map_reduce(
            f.count() / 2 * n_chunks,
            || [F128::ZERO; 4],
            |t| {
                let (m, k) = (t / n_chunks, t % n_chunks);
                let (lf, lg) = (f.lane(2 * m), f.lane(2 * m + 1));
                let w = |l: usize| &self.w[l * self.low_stride..][..self.low_stride];
                let (lw0, lw1) = (w(2 * m), w(2 * m + 1));
                let mut acc = [Acc8::ZERO; 4];
                for c in (k * CHUNK..((k + 1) * CHUNK).min(low)).step_by(8) {
                    let (f, g) = (F128x8::load(&lf[c..][..8]), F128x8::load(&lg[c..][..8]));
                    let (w0, w1) = (F128x8::load(&lw0[c..][..8]), F128x8::load(&lw1[c..][..8]));
                    let xf = F128x8::from_array(&core::array::from_fn(|j| x_at(lf, c + j)));
                    for (acc, (w, v)) in acc.iter_mut().zip([(w0, g), (w0 + w1, f), (w0, xf), (w1, xf)]) {
                        *acc += w.mul_unreduced(v);
                    }
                }
                acc.map(Acc8::sum)
            },
            |a, b| std::array::from_fn(|i| a[i] + b[i]),
        )
    }

    fn fold(&mut self, ch: &FoldChallenges) {
        self.f = Lanes::Folded(std::mem::take(&mut self.f)).fold(ch);
        self.w = fold(&self.w, self.low_stride, ch.alpha);
    }
}

/// `count` query positions in `0..block_len` in transcript order, duplicates kept: each challenge `c_0 + c_1 y`, as
/// the integer `c_0 + 2^64 c_1`, gives `floor(128 / log_2(block_len))` of them, its runs of `log_2(block_len)` bits
/// from the low end, as `verifier`'s `whir.rs` reads them.
fn sample_queries(ps: &mut ProverState, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let word = u128::from(ps.sample());
        for j in 0..(128 / d).min(count - out.len()) {
            out.push((word >> (j * d)) as usize & (block_len - 1));
        }
    }
    out
}

/// Prove the weighted claim `<W, f>` on the stack `f` committed in `committed`, `level0` holding its lanes and the
/// weight `W` as terms. The caller has bound the commitment and every claim the weight batches.
pub(crate) fn open(ps: &mut ProverState, config: &WhirConfig, mut level0: LaneRounds, committed: ProverData) {
    let levels = config.folds.len();
    fold_rounds(ps, &mut level0, config.folds[0]);
    // `p`: the folded lane `P`, its `2^mu` low coefficients then the high ones; `w`: the weight over the low ones.
    let (mut p, mut w) = level0.finish();
    let mut oracle = committed;
    for level in 0..levels {
        if level > 0 {
            let mut dense = Dense::new(&p, &w, 1 << config.folds[level]);
            fold_rounds(ps, &mut dense, config.folds[level]);
            (p, w) = dense.finish();
        }
        let mu = w.len().ilog2() as usize;
        let block_len = oracle.block_len();

        if level == levels - 1 {
            ps.add_scalars(&p);
            ps.grind(QUERY_GRINDING_BITS);
            let queries = sample_queries(ps, block_len, config.queries[level]);
            ps.hint_merkle(oracle.open(&queries));
            p.truncate(1 << mu);
            product_sumcheck(ps, p, w, 1, F128::ONE);
            return;
        }

        // (commit) The low part is the next level's message, and the high part is sent.
        let high = p.split_off(1 << mu);
        let k = config.folds[level + 1];
        let next = commit_ext(&p, mu - k, k, config.log_inv_rates[level + 1]);
        ps.add_root(&next.tree.root());
        ps.add_scalars(&high);

        // (ood) The message's value at a point the next level's list is bound by.
        ps.grind(OOD_GRINDING_BITS);
        let eq = eq_table(&ps.sample_vec(mu));
        ps.add_scalar(dot_par(&p, &eq));

        // (query) The queries and lambda, one message; then the oracle's rows there.
        ps.grind(QUERY_GRINDING_BITS);
        let queries = sample_queries(ps, block_len, config.queries[level]);
        let lambda = ps.sample();
        ps.hint_merkle(oracle.open(&queries));
        oracle = next;

        // (next level) `W += lambda eq(z, .) + sum_q lambda^(q+2) W_(x_q)`.
        let scalars = &powers(lambda, queries.len() + 2)[2..];
        let induced = induce_basis(mu, &queries, scalars);
        parallel::chunks_mut(&mut w, CHUNK, |i, w| {
            let at = i * CHUNK;
            for (j, w) in w.iter_mut().enumerate() {
                *w += lambda * eq[at + j] + induced[at + j];
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stack_open::{RingSwitchOpen, StackClaim, commit, open};
    use crate::whir_induce::novel_basis_at;
    use crate::whir_induce::tests::novel_sum_at;
    use primitives::multilinear::interp;
    use primitives::test_rng::Rng;
    use verifier::Subspace;

    /// Committing only the lanes that carry data is indistinguishable from committing the whole `2^log_n` witness
    /// with an explicit zero tail: same proof, root included.
    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        for (log_n, lanes) in [(16usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let lane_vars = log_n - INITIAL_FOLDING_FACTOR;
            let lane_block = 1usize << lane_vars;
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                witness[used..].fill(F64::ZERO);
                // The first and the last committed lane, and the whole stack, whose weight reaches past them.
                let claims: Vec<_> = [(0, lane_vars), (used - lane_block, lane_vars), (0, log_n)]
                    .into_iter()
                    .map(|(offset, vars)| StackClaim {
                        offset,
                        low_point: rng.ext_vec(vars),
                    })
                    .collect();
                let ring = RingSwitchOpen {
                    offset: 0,
                    points: Vec::new(),
                };
                let prove = |msg: &[F64]| {
                    let mut ps = ProverState::from_label(b"whir-test");
                    let committed = commit(&mut ps, msg, log_n, MIN_LOG_INV_RATE);
                    open(&mut ps, committed, msg.to_vec(), &claims, &ring);
                    ps.into_proof()
                };
                assert_eq!(prove(&witness[..used]), prove(&witness), "n_lanes = {n_lanes}");
            }
        }
    }

    fn challenges(rng: &mut Rng) -> FoldChallenges {
        FoldChallenges {
            alpha: rng.ext(),
            beta: rng.ext(),
        }
    }

    /// A dense round's table is the four inner products over the low columns, written out lane by lane, and its fold
    /// is `G + alpha F + beta X F` over every column and the weight's interpolation at `alpha`.
    #[test]
    fn dense_round_matches_the_direct_inner_products() {
        let mut rng = Rng::new(0xF01D);
        for (log_stride, mu, high) in [
            (1usize, 0usize, 0usize),
            (1, 3, 2),
            (2, 5, 0),
            (3, 4, 3),
            (4, 9, 1),
            (4, 12, 5),
        ] {
            let (s, low) = (1usize << log_stride, 1usize << mu);
            let n_cols = low + high;
            let (f_in, w_in) = (rng.ext_vec(n_cols * s), rng.ext_vec(low * s));
            let mut dense = Dense::new(&f_in, &w_in, s);
            let ch = challenges(&mut rng);
            let lane = |v: &[F128], l: usize, cols: usize| (0..cols).map(|c| v[c * s + l]).collect::<Vec<_>>();
            let mut want = [F128::ZERO; 4];
            let (mut folded, mut w_want) = (Vec::new(), Vec::new());
            for m in 0..s / 2 {
                let (f, g) = (lane(&f_in, 2 * m, n_cols), lane(&f_in, 2 * m + 1, n_cols));
                let (w0, w1) = (lane(&w_in, 2 * m, low), lane(&w_in, 2 * m + 1, low));
                w_want.push(
                    w0.iter()
                        .zip(&w1)
                        .map(|(&lo, &hi)| interp(lo, hi, ch.alpha))
                        .collect::<Vec<_>>(),
                );
                let xf: Vec<F128> = (0..=n_cols).map(|c| crate::xmul::x_at(&f, c)).collect();
                let ip = |w: &[F128], v: &[F128]| w.iter().zip(v).map(|(&a, &b)| a * b).sum::<F128>();
                for (s, v) in want
                    .iter_mut()
                    .zip([ip(&w0, &g), ip(&w0, &f) + ip(&w1, &f), ip(&w0, &xf), ip(&w1, &xf)])
                {
                    *s += v;
                }
                let at = |v: &[F128], c: usize| v.get(c).copied().unwrap_or(F128::ZERO);
                folded.push(
                    (0..=n_cols)
                        .map(|c| at(&g, c) + ch.alpha * at(&f, c) + ch.beta * xf[c])
                        .collect::<Vec<_>>(),
                );
            }
            assert_eq!(dense.table(), want, "table, stride {s}, mu {mu}, high {high}");
            dense.fold(&ch);
            assert_eq!(dense.f.count(), s / 2);
            for (m, (f_want, w_want)) in folded.iter().zip(&w_want).enumerate() {
                assert_eq!(
                    dense.f.lane(m)[..=n_cols],
                    f_want[..],
                    "lane {m}, stride {s}, mu {mu}, high {high}"
                );
                let w = &dense.w[m * dense.low_stride..][..low];
                assert_eq!(w, &w_want[..], "weight {m}, stride {s}, mu {mu}, high {high}");
            }
        }
    }

    /// After a level's folds, the folded lane at a domain point is the codeword's row there folded by the level's
    /// challenges.
    #[test]
    fn folded_lane_matches_the_folded_codeword_rows() {
        let mut rng = Rng::new(0xC0DE);
        for (k, mu, log_inv_rate) in [(1usize, 4usize, 1usize), (2, 6, 2), (4, 8, 1), (4, 10, 3)] {
            let f = rng.ext_vec(1 << (mu + k));
            let oracle = commit_ext(&f, mu, k, log_inv_rate);
            let mut dense = Dense::new(&f, &rng.ext_vec(1 << (mu + k)), 1 << k);
            let rounds: Vec<_> = (0..k).map(|_| challenges(&mut rng)).collect();
            for ch in &rounds {
                dense.fold(ch);
            }
            let (p, _) = dense.finish();
            assert_eq!(p.len(), (1 << mu) + k);
            for q in (0..20).map(|_| rng.next_u64() as usize % oracle.block_len()) {
                let x = F64(q as u64);
                // The row's lanes, lane 0 first, two words each, folded pairwise round by round.
                let lanes = oracle.row(q).as_chunks::<2>().0.iter();
                let mut vals: Vec<F128> = lanes.map(|&[lo, hi]| F128::new(lo.0, hi.0)).collect();
                for ch in &rounds {
                    let pairs = vals.as_chunks::<2>().0.iter();
                    vals = pairs.map(|&[f, g]| g + (ch.alpha + ch.beta.mul_base(x)) * f).collect();
                }
                let want = novel_sum_at(&p, &novel_basis_at(&Subspace::new(mu + 1), q));
                assert_eq!(vals, [want], "k {k}, mu {mu}, position {q}");
            }
        }
    }
}
