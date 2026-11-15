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

use fiat_shamir::merkle::MerklePath;
use primitives::field::{Acc8, F64, F128, F128x8, powers};
use primitives::hash::OUT_LEN;
use primitives::multilinear::eq_table;
use primitives::transcript::ProverState;

use crate::merkle::{Hash, LeafHasher, MerkleTree};
use crate::ntt::AdditiveNttF64;
use crate::whir_induce::induce_basis;
use crate::whir_lanes::LaneRounds;
use verifier::{FOLD_GRINDING_BITS, OOD_GRINDING_BITS, QUERY_GRINDING_BITS, WhirConfig};

/// The smallest `log_inv_rate` a proof can use, its code rate being `2^-log_inv_rate`.
pub const MIN_LOG_INV_RATE: usize = 1;
/// The largest `log_inv_rate` a proof can use, its code rate being `2^-log_inv_rate`.
pub const MAX_LOG_INV_RATE: usize = 4;
/// Level 0's fold count, which is also the number of lanes a level-0 leaf holds, `2^INITIAL_FOLDING_FACTOR`.
pub const INITIAL_FOLDING_FACTOR: usize = 6;

/// The per-level sizes a [`WhirConfig`] (`verifier::derive_config`) implies for a `log_n`-variable opening.
#[derive(Clone, Debug)]
pub struct LevelShapes {
    /// Log message columns after each level's folds.
    pub log_msg_cols: Vec<usize>,
    /// Each level's block length: its message columns times its inverse rate.
    pub block_len: Vec<usize>,
    /// The variables left after every fold, which the tail sumcheck takes.
    pub yr_log_n: usize,
}

/// See [`LevelShapes`].
pub fn level_shapes(config: &WhirConfig, log_n: usize) -> LevelShapes {
    let log_msg_cols: Vec<usize> = config
        .folds
        .iter()
        .scan(log_n, |vars, &k| {
            *vars -= k;
            Some(*vars)
        })
        .collect();
    let block_len = log_msg_cols
        .iter()
        .zip(&config.log_inv_rates)
        .map(|(&c, &r)| 1 << (c + r))
        .collect();
    LevelShapes {
        yr_log_n: *log_msg_cols.last().expect("at least one level"),
        log_msg_cols,
        block_len,
    }
}

/// Elements a task of a parallel pass takes.
const CHUNK: usize = 1 << 12;

/// The pairs `(v[2q], v[2q + 1])` for the eight `q` from `q`, as their first and their second elements, zero past `v`.
fn pairs8(v: &[F128], q: usize) -> (F128x8, F128x8) {
    let at = |i: usize| v.get(i).copied().unwrap_or(F128::ZERO);
    let first = core::array::from_fn(|j| at(2 * (q + j)));
    let second = core::array::from_fn(|j| at(2 * (q + j) + 1));
    (F128x8::from_array(&first), F128x8::from_array(&second))
}

/// `n` values written by the pool eight at a time, `eight(k)` giving values `8k..8k + 8`.
pub(crate) fn collect8(n: usize, eight: impl Fn(usize) -> F128x8 + Sync) -> Vec<F128> {
    let mut v = parallel::map_collect(n.div_ceil(8), |k| eight(k).to_array()).into_flattened();
    v.truncate(n);
    v
}

/// `interp(x[2q], x[2q + 1], r)` for every pair.
fn fold_pairs(x: &[F128], r: F128) -> Vec<F128> {
    let r = F128x8::splat(r);
    collect8(x.len() / 2, |k| {
        let (lo, hi) = pairs8(x, 8 * k);
        lo + r * (lo + hi)
    })
}

/// `sum_i a[i] b[i]` over `E`.
fn inner_product(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    parallel::map_reduce(
        a.len().div_ceil(CHUNK),
        || F128::ZERO,
        |t| {
            let at = t * CHUNK..((t + 1) * CHUNK).min(a.len());
            a[at.clone()].iter().zip(&b[at]).map(|(&x, &y)| x * y).sum()
        },
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
    assert!(log_inv_rate >= 1 && log_n > INITIAL_FOLDING_FACTOR);
    let log_rows = log_n - INITIAL_FOLDING_FACTOR;
    let n_lanes = message.len() >> log_rows;
    assert!(
        message.len() == n_lanes << log_rows && (1..=1 << INITIAL_FOLDING_FACTOR).contains(&n_lanes),
        "the message is whole lane blocks of the stack"
    );
    let log_domain = log_rows + log_inv_rate;
    let hasher = LeafHasher::new(n_lanes, 1 << INITIAL_FOLDING_FACTOR);
    let mut leaves = parallel::filled(1 << log_domain, [0u8; OUT_LEN]);
    let codeword = tracing::info_span!("NTT", kind = "base encode", log_domain, lanes = n_lanes).in_scope(|| {
        AdditiveNttF64::standard(log_domain).encode_lane_major(
            message,
            n_lanes,
            log_inv_rate,
            &mut leaves,
            |rows, out| hasher.hash(rows, out),
        )
    });
    let tree = tracing::info_span!("Merkle").in_scope(|| MerkleTree::from_leaves(leaves));
    ProverData {
        codeword,
        row_words: n_lanes,
        leaf_words: 1 << INITIAL_FOLDING_FACTOR,
        tree,
    }
}

/// Commit to a deeper level's `E` message, `2^log_msg_cols` rows of `2^log_lanes` lanes.
fn commit_ext(message: &[F128], log_msg_cols: usize, log_lanes: usize, log_inv_rate: usize) -> ProverData {
    assert_eq!(message.len(), 1 << (log_msg_cols + log_lanes));
    let (log_domain, row_words) = (log_msg_cols + log_inv_rate, 2 << log_lanes);
    let hasher = LeafHasher::new(row_words, row_words);
    let mut leaves = parallel::filled(1 << log_domain, [0u8; OUT_LEN]);
    let codeword =
        tracing::info_span!("NTT", kind = "extension encode", log_domain, lanes = 1 << log_lanes).in_scope(|| {
            let words = primitives::cast_slice(message);
            AdditiveNttF64::standard(log_domain).encode_rows(
                words,
                row_words,
                log_inv_rate,
                &mut leaves,
                |rows, out| hasher.hash(rows, out),
            )
        });
    let tree = tracing::info_span!("Merkle").in_scope(|| MerkleTree::from_leaves(leaves));
    ProverData {
        codeword,
        row_words,
        leaf_words: row_words,
        tree,
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

/// Level `level`'s `k` fold rounds: each round's table, then `(alpha, beta)` after a grind.
fn fold_rounds(ps: &mut ProverState, lanes: &mut impl FoldRounds, level: usize, k: usize) {
    for round in 0..k {
        let _span = tracing::info_span!("Fold round", level, round).entered();
        ps.add_scalars(&lanes.table());
        ps.grind(FOLD_GRINDING_BITS);
        let ch = FoldChallenges {
            alpha: ps.sample(),
            beta: ps.sample(),
        };
        lanes.fold(&ch);
    }
}

/// A deeper level's lanes and weight in the clear: coefficient `c` of lane `l` at `c * stride + l`, the lanes' low
/// coefficients then the high ones the level's folds have added, and the weight over the low ones. A round's pair `q`
/// is then `(F, G) = (f[2q], f[2q + 1])` under the weights `(w[2q], w[2q + 1])`.
pub(crate) struct Dense {
    pub(crate) f: Vec<F128>,
    pub(crate) w: Vec<F128>,
    pub(crate) stride: usize,
}

impl Dense {
    /// `X F` at pairs `q..q + 8`: coefficient `c` of `X` times lane `2m`, where pair `q` is `(c, m)`.
    fn xf8(&self, q: usize) -> F128x8 {
        let (f, s) = (&self.f, self.stride);
        F128x8::from_array(&core::array::from_fn(|j| {
            let (c, m) = ((q + j) / (s / 2), (q + j) % (s / 2));
            crate::xmul::x_coef(|i| f.get(i * s + 2 * m).copied().unwrap_or(F128::ZERO), c)
        }))
    }
}

impl FoldRounds for Dense {
    fn table(&mut self) -> FoldTable {
        assert!(self.stride >= 2 && self.stride.is_power_of_two());
        let low_pairs = self.w.len() / 2;
        parallel::map_reduce(
            low_pairs.div_ceil(CHUNK),
            || [F128::ZERO; 4],
            |t| {
                let mut acc = [Acc8::ZERO; 4];
                for q in (t * CHUNK..((t + 1) * CHUNK).min(low_pairs)).step_by(8) {
                    let ((f, g), (w0, w1), xf) = (pairs8(&self.f, q), pairs8(&self.w, q), self.xf8(q));
                    acc[0] += w0.mul_unreduced(g);
                    acc[1] += (w0 + w1).mul_unreduced(f);
                    acc[2] += w0.mul_unreduced(xf);
                    acc[3] += w1.mul_unreduced(xf);
                }
                acc.map(Acc8::sum)
            },
            |a, b| std::array::from_fn(|i| a[i] + b[i]),
        )
    }

    fn fold(&mut self, ch: &FoldChallenges) {
        let (alpha, beta) = (F128x8::splat(ch.alpha), F128x8::splat(ch.beta));
        // One column longer: `X F` reaches one coefficient past `F`.
        let pairs = (self.f.len() / self.stride + 1) * self.stride / 2;
        let f = collect8(pairs, |k| {
            let (f, g) = pairs8(&self.f, 8 * k);
            (alpha.mul_unreduced(f) + beta.mul_unreduced(self.xf8(8 * k))).reduce() + g
        });
        (self.f, self.w, self.stride) = (f, fold_pairs(&self.w, ch.alpha), self.stride / 2);
    }
}

/// `count` query positions in `0..block_len` in transcript order, duplicates kept: each challenge `c_0 + c_1 y`, as
/// the integer `c_0 + 2^64 c_1`, gives `floor(128 / log_2(block_len))` of them, its runs of `log_2(block_len)` bits
/// from the low end (Annex B, "Sampling the queries").
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

/// The tail sumcheck on `<f, w>`, low variable first. Each round sends `(u_0, u_2)` of its quadratic
/// `q(X) = u_0 + u_1 X + u_2 X^2`, the running claim `q(0) + q(1)` fixing `u_1`, then grinds.
fn tail_sumcheck(ps: &mut ProverState, mut f: Vec<F128>, mut w: Vec<F128>) {
    while f.len() > 1 {
        let (mut u_0, mut u_2) = (F128::ZERO, F128::ZERO);
        for (&[f0, f1], &[w0, w1]) in f.as_chunks::<2>().0.iter().zip(w.as_chunks::<2>().0) {
            u_0 += f0 * w0;
            u_2 += (f0 + f1) * (w0 + w1);
        }
        ps.add_round_poly(&[u_0, F128::ZERO, u_2], false);
        let r = ps.sample();
        (f, w) = (fold_pairs(&f, r), fold_pairs(&w, r));
    }
}

/// Prove the weighted claim `<W, f>` on the stack `f` committed in `committed`, `level0` holding its lanes and the
/// weight `W` as terms. The caller has bound the commitment and every claim the weight batches.
pub(crate) fn open(ps: &mut ProverState, config: &WhirConfig, mut level0: LaneRounds, committed: ProverData) {
    let levels = config.folds.len();
    fold_rounds(ps, &mut level0, 0, config.folds[0]);
    // `p`: the folded lane `P`, its `2^mu` low coefficients then the high ones; `w`: the weight over the low ones.
    let (mut p, mut w) = level0.finish();
    let mut oracle = committed;
    for level in 0..levels {
        if level > 0 {
            let mut dense = Dense {
                f: p,
                w,
                stride: 1 << config.folds[level],
            };
            fold_rounds(ps, &mut dense, level, config.folds[level]);
            (p, w) = (dense.f, dense.w);
        }
        let mu = w.len().ilog2() as usize;
        let block_len = oracle.block_len();

        if level == levels - 1 {
            let _span = tracing::info_span!("Final level").entered();
            ps.add_scalars(&p);
            ps.grind(QUERY_GRINDING_BITS);
            let queries = sample_queries(ps, block_len, config.queries[level]);
            ps.hint_merkle(oracle.open(&queries));
            p.truncate(1 << mu);
            return tracing::info_span!("Tail").in_scope(|| tail_sumcheck(ps, p, w));
        }

        // (commit) The low part is the next level's message, and the high part is sent.
        let high = p.split_off(1 << mu);
        let k = config.folds[level + 1];
        let next = tracing::info_span!("Commit", level = level + 1)
            .in_scope(|| commit_ext(&p, mu - k, k, config.log_inv_rates[level + 1]));
        ps.add_root(&next.tree.root());
        ps.add_scalars(&high);

        // (ood) The message's value at a point the next level's list is bound by.
        ps.grind(OOD_GRINDING_BITS);
        let eq = eq_table(&ps.sample_vec(mu));
        ps.add_scalar(inner_product(&p, &eq));

        // (query) The queries and lambda, one message; then the oracle's rows there.
        ps.grind(QUERY_GRINDING_BITS);
        let queries = sample_queries(ps, block_len, config.queries[level]);
        let lambda = ps.sample();
        ps.hint_merkle(oracle.open(&queries));
        oracle = next;

        // (next level) `W += lambda eq(z, .) + sum_q lambda^(q+2) W_(x_q)`.
        let scalars = &powers(lambda, queries.len() + 2)[2..];
        let induced = tracing::info_span!("Induce", level).in_scope(|| induce_basis(mu, &queries, scalars));
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
            let mut dense = Dense {
                f: rng.ext_vec(n_cols * s),
                w: rng.ext_vec(low * s),
                stride: s,
            };
            let ch = challenges(&mut rng);
            let lane = |v: &[F128], l: usize, cols: usize| (0..cols).map(|c| v[c * s + l]).collect::<Vec<_>>();
            let mut want = [F128::ZERO; 4];
            let mut folded = Vec::new();
            for m in 0..s / 2 {
                let (f, g) = (lane(&dense.f, 2 * m, n_cols), lane(&dense.f, 2 * m + 1, n_cols));
                let (w0, w1) = (lane(&dense.w, 2 * m, low), lane(&dense.w, 2 * m + 1, low));
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
            let w_want: Vec<F128> = dense
                .w
                .as_chunks::<2>()
                .0
                .iter()
                .map(|&[a, b]| interp(a, b, ch.alpha))
                .collect();
            assert_eq!(dense.table(), want, "table, stride {s}, mu {mu}, high {high}");
            dense.fold(&ch);
            let f_want: Vec<F128> = (0..(n_cols + 1) * s / 2)
                .map(|i| folded[i % (s / 2)][i / (s / 2)])
                .collect();
            assert_eq!(dense.f, f_want, "lanes, stride {s}, mu {mu}, high {high}");
            assert_eq!(dense.w, w_want, "weight, stride {s}, mu {mu}, high {high}");
            assert_eq!(dense.stride, s / 2);
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
            let mut dense = Dense {
                f,
                w: rng.ext_vec(1 << (mu + k)),
                stride: 1 << k,
            };
            let rounds: Vec<_> = (0..k).map(|_| challenges(&mut rng)).collect();
            for ch in &rounds {
                dense.fold(ch);
            }
            let p = dense.f;
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
                let want = novel_sum_at(&p, &novel_basis_at(x, mu + 1));
                assert_eq!(vals, [want], "k {k}, mu {mu}, position {q}");
            }
        }
    }
}
