// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! WHIR with `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
//! `E = K[y]/(y^2+x*y+1)`.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, fold-round message, weight,
//! and post-fold witness is [`F128`]-valued. A level folds its lanes with the affine
//! combiner of \[CWYZ26\] rather than multilinearly.
//!
//! Representations:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas: `F128` (16 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F128::mul_base`] instead of a full E multiplication.

use crate::merkle::{Hash, MerkleTree};
use crate::ntt::{AdditiveNttF64, words};
use fiat_shamir::merkle::MerklePath;
use fiat_shamir::transcript::ProverState;
use primitives::field::{F64, F128, powers};
use primitives::multilinear::{eq_table, interp};

use super::whir_config::{FOLD_GRINDING_BITS, OOD_GRINDING_BITS};
pub use super::whir_config::{
    INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, LevelShapes, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE, ProverConfig,
    QUERY_GRINDING_BITS, SECURITY_BITS, config_for_rate, validate_log_inv_rate,
};

pub use crate::whir_induce::*;

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Elements a task of a parallel pass takes.
const CHUNK: usize = 1 << 12;

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F128]) -> F128 {
    assert_eq!(witness.len(), b.len());
    parallel::map_reduce(
        witness.len().div_ceil(CHUNK),
        || F128::ZERO,
        |t| {
            let at = t * CHUNK..((t + 1) * CHUNK).min(b.len());
            witness[at.clone()]
                .iter()
                .zip(&b[at])
                .map(|(&w, &e)| e.mul_base(w))
                .sum()
        },
        |a, v| a + v,
    )
}

/// `Σ_i a[i] · b[i]` over E.
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

// ===================================================================
// Commit: F64 message -> interleaved RS codeword -> Merkle root
// ===================================================================

/// Public commitment for an `F64` message: the L0 Merkle root.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub root: Hash,
}

/// A codeword kept whole: rows of `row_words` words.
struct Codeword {
    words: Vec<F64>,
    row_words: usize,
}

impl Codeword {
    /// The row at position `q`.
    fn row(&self, q: usize) -> &[F64] {
        &self.words[q * self.row_words..][..self.row_words]
    }
}

/// Prover-side state retained after commit for the opening phase: the codeword, a row per position holding the
/// committed lanes, and its Merkle tree.
pub struct ProverData {
    codeword: Codeword,
    merkle_tree: MerkleTree,
}

/// Commit to the `F64` message of a `2^log_n`-word witness: the message is its
/// leading `n_lanes` lane blocks of `2^(log_n - log_batch_size)` words each, one
/// RS codeword per lane, Merkle-committed one leaf per codeword position, the
/// leaf being that position across all `2^log_batch_size` lanes
/// (`2^log_batch_size * 8` bytes).
///
/// `n_lanes` is read off the message length, and `n_lanes < 2^log_batch_size` is
/// the padding-free case: the stacked witness's zero tail is whole lanes, so those
/// lanes are never encoded. Their codeword is zero (the encoding is linear), so the
/// leaf image is the one a full-width commitment would have hashed, with those
/// zeros LEADING it: lane `t` of the codeword is message block `n_lanes-1-t`, which
/// puts them at the front of the image where their whole chunks are one sponge
/// state every leaf shares. At most the image's tail, the committed lanes,
/// rides the proof, the opening saying its width and the image's.
pub fn commit(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> (Commitment, ProverData) {
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    assert!(log_n > log_batch_size, "witness must be wider than the interleaving");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= 1usize << log_batch_size,
        "at most 2^log_batch_size lanes carry data"
    );
    let k_code = log_rows + log_inv_rate;
    let ntt = AdditiveNttF64::standard(k_code);
    let words = tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes)
        .in_scope(|| ntt.encode_lane_major(message, n_lanes, log_inv_rate));
    let merkle_tree =
        tracing::info_span!("Merkle").in_scope(|| MerkleTree::build(&words, n_lanes, 1 << log_batch_size));
    let root = merkle_tree.root();
    let codeword = Codeword {
        words,
        row_words: n_lanes,
    };
    (Commitment { root }, ProverData { codeword, merkle_tree })
}

/// Codeword + Merkle tree for one deeper WHIR commitment level: a row is one position across the
/// `num_interleaved` lanes, one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitness {
    codeword: Codeword,
    tree: MerkleTree,
    pub block_len: usize,
    pub num_interleaved: usize,
}

impl LigeroWitness {
    /// The rows at `queries`, in order and back to back, and their paths.
    fn open(&self, queries: &[usize]) -> (Vec<F128>, Vec<MerklePath>) {
        let row = |q| self.codeword.row(q);
        let mut rows = Vec::with_capacity(queries.len() * self.num_interleaved);
        rows.extend(
            queries
                .iter()
                .flat_map(|&q| row(q).as_chunks::<2>().0.iter().map(|w| F128::new(w[0].0, w[1].0))),
        );
        let paths = self.tree.open(queries, 2 * self.num_interleaved, row);
        (rows, paths)
    }

    #[inline]
    pub fn root(&self) -> Hash {
        self.tree.root()
    }
}

/// Commit an extension-field polynomial at one recursive WHIR level.
///
/// - Each lane of the row-major message is RS-encoded with base-field twiddles.
/// - The codeword is then Merkle-committed, one leaf per row.
pub(crate) fn ligero_commit_ext(
    poly: &[F128],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
) -> LigeroWitness {
    let ntt = AdditiveNttF64::standard(log_msg_cols + log_inv_rate);
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);

    // One leaf per row, its F128s as K words.
    let row_words = 2 * num_interleaved;
    let words = tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| ntt.encode_rows(words(poly), row_words, log_inv_rate));
    let tree = tracing::info_span!("Merkle").in_scope(|| MerkleTree::build(&words, row_words, row_words));

    LigeroWitness {
        codeword: Codeword { words, row_words },
        tree,
        block_len,
        num_interleaved,
    }
}

// ===================================================================
// The final level's sumcheck over E
// ===================================================================
//
// Each round sends (u_0, u_2) of the quadratic
// q(X) = u_0 + u_1 X + u_2 X^2 with q(0) + q(1) = T_r, verifier derives
// u_1 = T_r + u_2 (char 2), round eval q(r) = u_0 + r T_r + (r + r^2) u_2.
// Then the round's grind, as for every round polynomial of degree two.

/// (u_0, u_2) per round in E.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    pub(crate) u_0: F128,
    pub(crate) u_2: F128,
}

/// Transmit the constant and quadratic coefficients (the claim fixes the linear one), then the round's grind.
fn send_msg(ps: &mut ProverState, m: SumcheckMessage) {
    ps.add_round_poly(&[m.u_0, F128::ZERO, m.u_2], false);
}

/// Round-quadratic in coefficient form `c + b X + a X^2`.
#[derive(Clone, Copy, Debug)]
struct RoundQuad {
    c: F128, // u_0
    b: F128, // u_1 (X coeff), derived from T_r and u_2
    a: F128, // u_2 (X^2 coeff)
}

impl RoundQuad {
    /// The quadratic a round message stands for, given the claim it answers:
    /// `h(0) + h(1) = claim` fixes the linear coefficient.
    #[inline]
    fn from_msg(msg: SumcheckMessage, t_r: F128) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    fn eval(&self, r: F128) -> F128 {
        (self.a * r + self.b) * r + self.c
    }
}

/// The round message of `f` against `b` over the adjacent pairs `(f[2j], f[2j + 1])`.
fn round_msg(f: &[F128], b: &[F128]) -> SumcheckMessage {
    let (mut u_0, mut u_2) = (F128::ZERO, F128::ZERO);
    for (&[f0, f1], &[b0, b1]) in f.as_chunks::<2>().0.iter().zip(b.as_chunks::<2>().0) {
        u_0 += f0 * b0;
        u_2 += (f0 + f1) * (b0 + b1);
    }
    SumcheckMessage { u_0, u_2 }
}

/// `interp(x[2j], x[2j + 1], r)` for every pair.
fn fold_pairs(x: &[F128], r: F128) -> Vec<F128> {
    x.as_chunks::<2>().0.iter().map(|&[a, b]| interp(a, b, r)).collect()
}

// ===================================================================
// Affine fold rounds [CWYZ26]
// ===================================================================
//
// A round pairs the lanes `F` (folded bit 0) and `G` (folded bit 1) of a level. It sends, with `W_i` the weight on
// the lanes with folded bit `i`,
//
//     [u0, w, c0, c1] = [<W_0, G>, <W_0 + W_1, F>, <W_0, X F>, <W_1, X F>],
//
// and after `(alpha, beta)` the lanes become `P = G + alpha F + beta X F`, one coefficient longer, and the
// weight `W_0 + alpha (W_0 + W_1)`. The weight covers a lane's low `2^mu` coefficients only, and so do the inner
// products; the high coefficients the folds add matter only where the lane is evaluated.

/// The challenges of one fold round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FoldChallenges {
    pub(crate) alpha: F128,
    pub(crate) beta: F128,
}

/// What a fold round sends: `[u0, w, c0, c1]`.
pub(crate) type FoldTable = [F128; 4];

impl FoldChallenges {
    /// The claim after the round, from the claim before it and the round's table:
    /// `u0 + alpha (u0 + claim) + alpha^2 w + beta c0 + alpha beta (c0 + c1)`.
    pub(crate) fn next_claim(&self, claim: F128, table: &FoldTable) -> F128 {
        let [u0, w, c0, c1] = *table;
        let (alpha, beta) = (self.alpha, self.beta);
        u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))
    }

    /// `G + (alpha + beta x) F`: the folded lane at the domain point `x`, from the two it folds.
    #[inline]
    pub(crate) fn fold_at(&self, f: F128, g: F128, x: F64) -> F128 {
        g + (self.alpha + self.beta.mul_base(x)) * f
    }
}

/// One fold round's transcript: the table, then `(alpha, beta)` after a grind.
fn fold_round(ps: &mut ProverState, table: &FoldTable) -> FoldChallenges {
    ps.add_scalars(table);
    ps.grind(FOLD_GRINDING_BITS);
    let (alpha, beta) = (ps.sample(), ps.sample());
    FoldChallenges { alpha, beta }
}

/// An opened row's lanes, in fold order, folded by the level's rounds at the row's domain point `x`.
pub(crate) fn fold_row(row: impl IntoIterator<Item = F128>, rounds: &[FoldChallenges], x: F64) -> F128 {
    let mut vals: Vec<F128> = row.into_iter().collect();
    assert_eq!(vals.len(), 1 << rounds.len(), "a row holds one value per lane");
    for ch in rounds {
        let half = vals.len() / 2;
        for i in 0..half {
            vals[i] = ch.fold_at(vals[2 * i], vals[2 * i + 1], x);
        }
        vals.truncate(half);
    }
    vals[0]
}

/// Lanes in the clear, coefficient by coefficient: coefficient `c` of lane `l` at `c * stride + l`, the low ones
/// then the high ones the level's folds have added, and the weight over the low ones in the same order.
pub(crate) struct Dense {
    pub(crate) f: Vec<F128>,
    pub(crate) w: Vec<F128>,
    pub(crate) stride: usize,
}

impl Dense {
    /// Columns per task.
    fn cols_per_task(&self) -> usize {
        (CHUNK / self.stride).max(1)
    }

    /// The round's table.
    pub(crate) fn table(&self) -> FoldTable {
        let (s, pairs) = (self.stride, self.stride / 2);
        assert!(s >= 2 && s.is_power_of_two());
        let (f, w) = (&self.f, &self.w);
        let low = w.len() / s;
        let per = self.cols_per_task();
        parallel::map_reduce(
            low.div_ceil(per),
            || [F128::ZERO; 4],
            |t| {
                let cols = t * per..((t + 1) * per).min(low);
                let mut xf = vec![F128::ZERO; cols.len() * pairs];
                crate::xmul::mul_x(f, s, 2, cols.start, &mut xf);
                let mut acc = [F128::ZERO; 4];
                for (c, xf) in cols.zip(xf.chunks_exact(pairs)) {
                    let (lanes, w) = (&f[c * s..][..s], &w[c * s..][..s]);
                    for m in 0..pairs {
                        let (w0, w1, f, g) = (w[2 * m], w[2 * m + 1], lanes[2 * m], lanes[2 * m + 1]);
                        acc[0] += w0 * g;
                        acc[1] += (w0 + w1) * f;
                        acc[2] += w0 * xf[m];
                        acc[3] += w1 * xf[m];
                    }
                }
                acc
            },
            |a, b| std::array::from_fn(|i| a[i] + b[i]),
        )
    }

    /// The round's fold: lanes `P = G + alpha F + beta X F`, one column longer, and the weight at `alpha`.
    pub(crate) fn fold(&mut self, ch: &FoldChallenges) {
        let (s, pairs) = (self.stride, self.stride / 2);
        let n_cols = self.f.len() / s;
        let per = self.cols_per_task();
        let FoldChallenges { alpha, beta } = *ch;
        let f = &self.f;
        let mut next = vec![F128::ZERO; (n_cols + 1) * pairs];
        parallel::chunks_mut(&mut next, per * pairs, |t, out| {
            let first = t * per;
            crate::xmul::mul_x(f, s, 2, first, out);
            for (c, out) in (first..).zip(out.chunks_exact_mut(pairs)) {
                for (m, o) in out.iter_mut().enumerate() {
                    let (f, g) = if c < n_cols {
                        (f[c * s + 2 * m], f[c * s + 2 * m + 1])
                    } else {
                        (F128::ZERO, F128::ZERO)
                    };
                    *o = g + alpha * f + beta * *o;
                }
            }
        });
        (self.f, self.w, self.stride) = (next, fold_pairs(&self.w, alpha), pairs);
    }
}

/// `at(y)` over a stack of `lanes` lanes of `lane_block` words, coefficient by coefficient: coefficient `c` of lane
/// `l`, at stack index `l * lane_block + c`, goes to `c * lanes + l`.
fn interleave(lanes: usize, lane_block: usize, at: impl Fn(usize) -> F128 + Sync) -> Vec<F128> {
    let mut out = vec![F128::ZERO; lanes * lane_block];
    parallel::chunks_mut(&mut out, CHUNK, |i, out| {
        for (d, o) in (i * CHUNK..).zip(out) {
            *o = at(d % lanes * lane_block + d / lanes);
        }
    });
    out
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊128/d⌋` positions as
/// its disjoint d-bit chunks (low bits first), matching the scheme the recursive guest derives (fixed `128/d` per
/// squeeze, dup-tolerant: soundness matches the deployed PCS with the same
/// `config.queries`). Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
///
fn sample_queries_ordered(ch: &mut ProverState, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 128 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let [c0, c1] = ch.sample().to_limbs();
        let word = c0 as u128 | (c1 as u128) << 64;
        for j in 0..per.min(count - out.len()) {
            out.push((word >> (j * d)) as usize & (block_len - 1));
        }
    }
    out
}

/// One level's claims batched into the running one with powers of the level's challenge `lambda`, the running claim
/// keeping `lambda^0 = 1`: claim `tau` (counting from 1) adds `lambda^tau` times its weight and its value.
fn glue<const N: usize>(w: &mut [F128], claim: &mut F128, pending: [(Vec<F128>, F128); N], lambda: F128) {
    let scalars = &powers(lambda, N + 1)[1..];
    for ((b_new, value), &scalar) in pending.iter().zip(scalars) {
        assert_eq!(b_new.len(), w.len());
        *claim += scalar * *value;
    }
    parallel::chunks_mut(w, CHUNK, |i, acc| {
        for ((b_new, _), &scalar) in pending.iter().zip(scalars) {
            for (a, &b) in acc.iter_mut().zip(&b_new[i * CHUNK..]) {
                *a += scalar * b;
            }
        }
    });
}

/// The tail sumcheck on `<w, f> = claim` over the low variables first, each round's message sent before its
/// challenge. Returns the claim it ends on, with `f` and `w` folded to one value each.
fn tail_sumcheck(ps: &mut ProverState, mut f: Vec<F128>, mut w: Vec<F128>, mut claim: F128) -> (F128, F128, F128) {
    while f.len() > 1 {
        let msg = round_msg(&f, &w);
        send_msg(ps, msg);
        let r = ps.sample();
        claim = RoundQuad::from_msg(msg, claim).eval(r);
        (f, w) = (fold_pairs(&f, r), fold_pairs(&w, r));
    }
    (claim, f[0], w[0])
}

/// Prove `Σ_x witness(x) · weight(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is owned: round 2's table reads it last (the end of the level-0 rounds if `initial_k` is 1), and the large
/// committed stack is gone before the level-1 commit allocates.
///
/// `witness` may be shorter than `2^log_n`: it is a whole number of lane blocks, zero past them. The level-0 rounds
/// read only those, while `weight` covers every lane.
///
/// Every level folds its lanes with [`FoldChallenges`], commits the low part of the folded lane (the next level's
/// message) and sends its high part, binds the next level with one OOD point, then opens its own oracle at its
/// queries, whose folded values (corrected by the high part) and column weights are glued into the running claim.
/// The final level sends its folded lane whole and closes with a sumcheck over its low part.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one
/// phase per level. The caller has already bound the initial commitment and target.
pub(crate) fn recursive_prover(
    config: &ProverConfig,
    log_n: usize,
    witness: Vec<F64>,
    weight: Vec<F128>,
    target: F128,
    prover_data: ProverData,
    ps: &mut ProverState,
) {
    let r = config.level_steps;
    let initial_k = config.initial_k;

    assert_eq!(config.level_ks.len(), r);
    assert_eq!(config.log_inv_rates.len(), r + 1);
    assert!(r >= 1);
    assert!(initial_k >= 1);

    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + config.log_inv_rates[0]);
    let num_interleaved_0 = 1usize << initial_k;
    // The committed lanes: only the ones that carry data, so the witness is a
    // whole number of lane blocks but generally NOT `2^log_n` words.
    let lane_block = 1usize << log_msg_cols_0;
    let n_lanes = witness.len() / lane_block;
    assert_eq!(witness.len(), n_lanes * lane_block, "witness is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= num_interleaved_0,
        "at most 2^initial_k lanes"
    );
    assert_eq!(prover_data.codeword.row_words, n_lanes);
    assert_eq!(prover_data.codeword.words.len(), block_len_0 * n_lanes);

    // Nothing is absorbed on entry. The commitment was bound by the `add_root` that
    // transmitted it, and the target is `sum_i lambda^i * claim_i` over claim values bound by their
    // own reads, with lambda drawn from the state: the state already determines both. Every caller
    // must therefore have transmitted its root before opening against it, which is what makes the
    // fold challenges depend on the commitment.
    //
    // The prover's messages never depend on the running claim; it is tracked only to check, in tests, that the
    // rounds keep it.
    let mut claim = target;

    // Level 0's lanes are the stack's lane blocks, the high variables; a later level's are the low ones of the
    // previous level's message.
    assert_eq!(weight.len(), 1 << log_n);
    let span = tracing::info_span!("Interleave").entered();
    let mut p = interleave(num_interleaved_0, lane_block, |y| {
        witness.get(y).map_or(F128::ZERO, |&k| F128::from(k))
    });
    drop(witness);
    let mut w = interleave(num_interleaved_0, lane_block, |y| weight[y]);
    drop((weight, span));
    let mut prover_data = Some(prover_data);
    let mut wtns_prev: Option<LigeroWitness> = None;
    let mut rounds = Vec::new();

    for level in 0..=r {
        let k = if level == 0 {
            initial_k
        } else {
            config.level_ks[level - 1]
        };
        let mut dense = Dense {
            f: p,
            w,
            stride: 1 << k,
        };
        rounds.clear();
        for j in 0..k {
            let _span = tracing::info_span!("Fold round", level, round = j).entered();
            let table = dense.table();
            let ch = fold_round(ps, &table);
            claim = ch.next_claim(claim, &table);
            dense.fold(&ch);
            rounds.push(ch);
        }
        (p, w) = (dense.f, dense.w);
        let mu = w.len().ilog2() as usize;
        assert_eq!(p.len(), (1 << mu) + rounds.len());
        let block_len = wtns_prev.as_ref().map_or(block_len_0, |wt| wt.block_len);

        if level == r {
            let _span = tracing::info_span!("Final level").entered();
            ps.add_scalars(&p);
            ps.grind(QUERY_GRINDING_BITS);
            let queries = sample_queries_ordered(ps, block_len, config.queries[level]);
            let wtns = wtns_prev.as_ref().expect("the final level is not level 0");
            let (rows, paths) = wtns.open(&queries);
            ps.hint_merkle(paths);
            if cfg!(test) {
                for (row, &q) in rows.chunks_exact(wtns.num_interleaved).zip(&queries) {
                    let x = F64(q as u64);
                    let at = novel_sum_at(&p, 0, &novel_basis_at(x, mu));
                    assert_eq!(fold_row(row.iter().copied(), &rounds, x), at, "final row {q}");
                }
            }
            p.truncate(1 << mu);
            let (end, f, b) = tracing::info_span!("Tail").in_scope(|| tail_sumcheck(ps, p, w, claim));
            if cfg!(test) {
                assert_eq!(end, f * b, "the rounds keep the running claim");
            }
            return;
        }

        // Commit the folded lane's low part as the next level's message, then send its high part.
        let p_high = p.split_off(1 << mu);
        let k_next = config.level_ks[level];
        assert!(mu >= k_next);
        let span = tracing::info_span!("Commit", level = level + 1).entered();
        let wtns_next = ligero_commit_ext(&p, mu - k_next, k_next, config.log_inv_rates[level + 1]);
        drop(span);
        ps.add_root(&wtns_next.root());
        ps.add_scalars(&p_high);

        // Bind the next level's list before drawing this level's queries: grind, one OOD point, then its value. The
        // claim stays pending until the level's batching challenge, which the query message draws last.
        ps.grind(OOD_GRINDING_BITS);
        let eq = eq_table(&ps.sample_vec(mu));
        let y = inner_product(&p, &eq);
        ps.add_scalar(y);

        ps.grind(QUERY_GRINDING_BITS);
        let queries = sample_queries_ordered(ps, block_len, config.queries[level]);
        let lambda = ps.sample();
        let weights = powers(lambda, queries.len());

        // The rows at the queries, lanes in fold order.
        let span = tracing::info_span!("Open", level).entered();
        let rows: Vec<F128> = match prover_data.take() {
            Some(prover_data) => {
                let image = |q| prover_data.codeword.row(q);
                // Lane `t` of the codeword is stack block `n_lanes-1-t`: reversing the image puts block `b` at index
                // `b`, and the absent lanes' zeros at the end.
                let mut rows = Vec::with_capacity(queries.len() * num_interleaved_0);
                for &q in &queries {
                    let zeros = std::iter::repeat_n(F128::ZERO, num_interleaved_0 - n_lanes);
                    rows.extend(image(q).iter().rev().map(|&k| F128::from(k)).chain(zeros));
                }
                ps.hint_merkle(prover_data.merkle_tree.open(&queries, num_interleaved_0, image));
                // Nothing reads the L0 codeword or its tree again.
                drop(prover_data);
                rows
            }
            None => {
                let (rows, paths) = wtns_prev.as_ref().expect("a committed level").open(&queries);
                ps.hint_merkle(paths);
                rows
            }
        };
        drop(span);

        // Each query claims `P(x)` by folding its row; less the high part's share, that is `P_low(x)`.
        let span = tracing::info_span!("Induce", level).entered();
        let values: Vec<F128> = rows
            .chunks_exact(1 << rounds.len())
            .zip(&queries)
            .map(|(row, &q)| {
                let x = F64(q as u64);
                let what = novel_basis_at(x, mu);
                let value = fold_row(row.iter().copied(), &rounds, x) + novel_sum_at(&p_high, 1 << mu, &what);
                if cfg!(test) {
                    assert_eq!(value, novel_sum_at(&p, 0, &what), "level {level}, row {q}");
                }
                value
            })
            .collect();
        let enforced = values.iter().zip(&weights).map(|(&v, &wt)| v * wt).sum();
        let basis = induce_basis(mu, block_len.ilog2() as usize - mu, &queries, &weights);
        drop(span);
        let pending = [(eq, y), (basis, enforced)];
        tracing::info_span!("Glue", level).in_scope(|| glue(&mut w, &mut claim, pending, lambda));
        if cfg!(test) {
            assert_eq!(
                claim,
                p.iter().zip(&w).map(|(&a, &b)| a * b).sum(),
                "level {level} keeps the claim"
            );
        }

        wtns_prev = Some(wtns_next);
    }
    unreachable!("the final level returns")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stack_open::{RingSwitchOpen, StackClaim, open_batch_mixed_whir_stacked};
    use primitives::test_rng::Rng;

    /// Committing only the lanes that carry data must be indistinguishable from
    /// committing the whole `2^log_n` witness with an explicit zero tail: same
    /// root and the same proof. The prover's own checks run on the way: every
    /// query value is the folded lane's, and every level keeps the running claim.
    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        for (log_n, lanes) in [(16usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = config_for_rate(log_n, LOG_INV_RATE_0).unwrap();
            let lane_block = 1usize << (log_n - pc.initial_k);
            for &n_lanes in lanes.iter().filter(|&&n| n <= 1 << pc.initial_k) {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                witness[used..].fill(F64::ZERO);
                // The first and the last committed lane, and the whole stack, whose weight reaches past them.
                let lane_vars = log_n - pc.initial_k;
                let claims: Vec<_> = [(0, lane_vars), (used - lane_block, lane_vars), (0, log_n)]
                    .into_iter()
                    .map(|(offset, vars)| {
                        let low_point = rng.ext_vec(vars);
                        let value = inner_product_base_ext(
                            &witness[offset..offset + (1 << vars)],
                            &primitives::multilinear::eq_table(&low_point),
                        );
                        StackClaim::Point {
                            offset,
                            low_point,
                            value,
                        }
                    })
                    .collect();
                let ring = RingSwitchOpen {
                    offset: 0,
                    claims: Vec::new(),
                };

                let prove = |msg: &[F64]| {
                    let (cm, pd) = commit(msg, log_n, pc.initial_k, pc.log_inv_rates[0]);
                    let mut ps = fiat_shamir::transcript::ProverState::from_label(b"whir-test");
                    open_batch_mixed_whir_stacked(&mut ps, log_n, msg.to_vec(), pd, &pc, &claims, &ring);
                    (cm.root, ps.into_proof())
                };
                let (root_trunc, fs_trunc) = prove(&witness[..used]);
                let (root_full, fs_full) = prove(&witness);
                assert_eq!(root_trunc, root_full, "root differs at n_lanes = {n_lanes}");
                assert_eq!(fs_trunc, fs_full, "the proofs differ at n_lanes = {n_lanes}");
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
                let mut xf = vec![F128::ZERO; n_cols + 1];
                crate::xmul::mul_x(&f, 1, 1, 0, &mut xf);
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

    /// `P(x) = sum_c p_c X_c(x)`.
    fn eval_at(p: &[F128], x: F64) -> F128 {
        let mu = (usize::BITS - p.len().leading_zeros()) as usize;
        novel_sum_at(p, 0, &novel_basis_at(x, mu))
    }

    /// After a level's folds, the folded lane at a domain point is the opened codeword row there folded by the
    /// level's challenges, and less its high part's share, its low part there.
    #[test]
    fn folded_lane_matches_the_folded_codeword_rows() {
        let mut rng = Rng::new(0xC0DE);
        for (k, mu, log_inv_rate) in [(1usize, 4usize, 1usize), (2, 6, 2), (4, 8, 1), (4, 10, 3)] {
            let f = rng.ext_vec(1 << (mu + k));
            let wtns = ligero_commit_ext(&f, mu, k, log_inv_rate);
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
            let queries: Vec<usize> = (0..20).map(|_| rng.next_u64() as usize % wtns.block_len).collect();
            let (rows, _) = wtns.open(&queries);
            for (row, &q) in rows.chunks_exact(1 << k).zip(&queries) {
                let x = F64(q as u64);
                let folded = fold_row(row.iter().copied(), &rounds, x);
                assert_eq!(folded, eval_at(&p, x), "k {k}, mu {mu}, position {q}");
                let low = folded + novel_sum_at(&p[1 << mu..], 1 << mu, &novel_basis_at(x, mu));
                assert_eq!(low, eval_at(&p[..1 << mu], x), "low part, k {k}, mu {mu}, position {q}");
            }
        }
    }
}
