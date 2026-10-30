// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! WHIR with `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
//! `E = K[y]/(y^3+y+1)`.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, sumcheck message, basis
//! poly, and post-fold witness is [`F192`]-valued.
//!
//! Representations:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F192` (24 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F192::mul_base`] (3 PMULL) instead of a full E multiplication.
//!
//! Soundness note: [`WhirSecurityConfig`] analyzes the actual challenge
//! field size `q = 2^192`; the committed alphabet remains `K = GF(2^64)`.

use crate::merkle::{self, Hash};
use crate::ntt::{AdditiveNttF64, Encoded, Keep, Kept, Plan, gather_rows};
use fiat_shamir::merkle::PrunedMerklePaths;
use fiat_shamir::transcript::ProverState;
use primitives::field::{
    Acc8, F64, F192, F192Unreduced, F192x8, Prod8, fold_lones8_ext, fold_pairs8_ext, msg_lone8_ext, msg_terms8_ext,
    powers,
};

pub use super::whir_config::{
    FinalBlockConfig, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, LevelShapes, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE,
    ProverConfig, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS,
    SUBSEQUENT_FOLDING_FACTOR, WhirLevelConfig, WhirSecurityConfig, validate_log_inv_rate,
};
#[cfg(test)]
pub use super::whir_config::{default_config, udr_queries};

pub use crate::whir_induce::*;
use crate::whir_ntt_ext::*;

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Build the eq-MLE table at `point`, LSB-first, without dispatching to the worker pool.
pub fn build_eq_table_ext(point: &[F192]) -> Vec<F192> {
    let d = point.len();
    let mut out: Vec<F192> = Vec::with_capacity(1usize << d);
    out.push(F192::ONE);
    for j in 0..d {
        let r_j = point[j];
        let len = 1usize << j;
        out.resize(2 * len, F192::ZERO);
        for i in 0..len {
            let v = out[i];
            let high = v * r_j;
            out[i + len] = high;
            out[i] = v + high;
        }
    }
    out
}

use primitives::multilinear::eq_table as build_eq_table_ext_parallel;

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    if witness.len() < PAR_THRESHOLD {
        return witness
            .iter()
            .zip(b.iter())
            .map(|(&w, &e)| e.mul_base(w))
            .fold(F192::ZERO, |a, v| a + v);
    }
    parallel::map_reduce(
        witness.len(),
        || F192::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive the shared prover/verifier config for a K-witness of `2^log_n` F64
/// elements at L0 inverse-rate logarithm `log_inv_rate`, using the production
/// 128-bit Johnson/OOD profile at `m = log_n + LOG_PACKING`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, String> {
    let sec = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + crate::LOG_PACKING, log_inv_rate)?;
    sec.to_config()
}

// ===================================================================
// Commit: F64 message -> interleaved RS codeword -> Merkle root
// ===================================================================

/// Public commitment for an `F64` message: the L0 Merkle root.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub root: Hash,
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is not stored; the caller retains it for opening.
///
/// With `deep` set, `codeword` holds the rows before the encode's deep layers, which the opening finishes.
/// If it is empty too, the encode kept no rows, and the opening recomputes the sub-blocks a query reads
/// from the message, see `ProverData::l0`.
pub struct ProverData {
    pub codeword: Vec<F64>,
    /// Words per codeword row: the committed lanes, with zero lanes in front up to the vector width.
    row_words: usize,
    pub merkle_tree: merkle::CutTree,
    deep: Option<(AdditiveNttF64, Plan)>,
}

impl ProverData {
    /// Words of the codeword the encode covered, kept or not.
    fn len(&self) -> usize {
        self.deep.as_ref().map_or(self.codeword.len(), |(_, deep)| deep.words())
    }

    /// Whether the opening needs the message to recompute the rows.
    pub(crate) fn rebuilds(&self) -> bool {
        self.deep.is_some() && self.codeword.is_empty()
    }

    /// The codeword as the opening reads it. `stack` is the committed message, `n_lanes` its lanes.
    pub(crate) fn l0<'a>(&'a self, stack: &'a [F64], n_lanes: usize) -> L0Codeword<'a> {
        L0Codeword {
            words: &self.codeword,
            row_words: self.row_words,
            deep: self.deep.as_ref(),
            stack,
            n_lanes,
        }
    }
}

/// The L0 codeword as the opening reads it: kept whole or before its deep layers, or recomputed from the message.
pub(crate) struct L0Codeword<'a> {
    words: &'a [F64],
    row_words: usize,
    deep: Option<&'a (AdditiveNttF64, Plan)>,
    stack: &'a [F64],
    n_lanes: usize,
}

impl L0Codeword<'_> {
    /// The rows at the sorted `positions`, `row_words` words each, back to back.
    fn rows(&self, positions: &[usize]) -> Vec<F64> {
        match self.deep {
            Some((ntt, plan)) if self.words.is_empty() => {
                let kept = Kept::Nothing {
                    msg: self.stack,
                    n_lanes: self.n_lanes,
                    plan: *plan,
                };
                ntt.openings().rows(kept, positions)
            }
            deep => kept_rows(self.words, self.row_words, deep, positions),
        }
    }
}

/// The rows at the sorted `positions` of a codeword kept whole, or kept before its deep layers when `deep` says
/// how to finish them, `row_words` words each, back to back.
fn kept_rows(words: &[F64], row_words: usize, deep: Option<&(AdditiveNttF64, Plan)>, positions: &[usize]) -> Vec<F64> {
    match deep {
        Some((ntt, plan)) => ntt.openings().rows(Kept::BeforeDeep { words, plan: *plan }, positions),
        None => gather_rows(words, row_words, positions),
    }
}

/// Largest L0 codeword the commit keeps, in bytes.
///
/// - Up to it, memory is not the limit, and the codeword saves the opening a rebuild from the stack and the encode a second stage fill.
/// - Above it, the codeword dominates the peak: the commit keeps none, and when one gathered pass covers the layers
///   before the deep pass it encodes half of the cosets at a time.
const KEEP_CODEWORD_MAX_BYTES: usize = 1 << 30;

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
/// state every leaf shares. Only the image's tail, the committed lanes,
/// rides the proof, so a verifier derives `n_lanes` from the announced layout to
/// read a row and supplies the prefix itself.
///
/// The encoded row is padded to a whole AVX-512 vector of lanes with zero lanes
/// in front, so the NTT has no masked tail. The padding is the image's zeros and
/// never rides the proof.
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
    let n_positions = 1usize << k_code;
    let row_words = n_lanes.next_multiple_of(8).min(1usize << log_batch_size);

    // Leaves are hashed as the encode finishes each block of rows.
    let tree = merkle::MerkleBuilder::new(n_positions, row_words, 1usize << log_batch_size);
    let (codeword, deep) = tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = row_words)
        .in_scope(|| {
            let ntt = AdditiveNttF64::standard(k_code);
            let on_rows = |row, rows: &[F64]| tree.absorb(row, rows);
            let keep = if !primitives::REBUILD_OVER_STORE {
                Keep::Whole
            } else if n_positions * row_words * size_of::<F64>() > KEEP_CODEWORD_MAX_BYTES {
                Keep::Nothing
            } else {
                Keep::BeforeDeep
            };
            let Encoded { words, deep } =
                ntt.encode_lane_major(message, n_lanes, row_words, log_inv_rate, keep, &on_rows);
            (words, deep.map(|deep| (ntt, deep)))
        });
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = merkle_tree.root();

    (
        Commitment { root },
        ProverData {
            codeword,
            row_words,
            merkle_tree,
            deep,
        },
    )
}

/// Codeword + Merkle tree for one deeper WHIR commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 24` bytes.
///
/// With `deep` set, `mat` holds the codeword before its deep layers, and
/// [`LigeroWitness::opened_words`] finishes the rows a query opens.
pub(crate) struct LigeroWitness {
    pub mat: Vec<F192>,
    pub tree: merkle::CutTree,
    pub block_len: usize,
    pub num_interleaved: usize,
    deep: Option<(AdditiveNttF64, Plan)>,
}

impl LigeroWitness {
    /// The rows at the sorted `positions`, back to back, each as the K words its Merkle leaf is hashed from.
    fn opened_words(&self, positions: &[usize]) -> Vec<F64> {
        kept_rows(
            words(&self.mat),
            3 * self.num_interleaved,
            self.deep.as_ref(),
            positions,
        )
    }

    /// The rows at `queries`, in order and back to back, and the octopus over them.
    fn open(&self, queries: &[usize]) -> (Vec<F192>, PrunedMerklePaths) {
        let group = self.tree.group_positions(queries);
        let group_rows = self.opened_words(&group);
        let row_words = 3 * self.num_interleaved;
        let row = |q| fetched_row(&group, &group_rows, row_words, q);
        let mut rows = Vec::with_capacity(queries.len() * self.num_interleaved);
        rows.extend(queries.iter().flat_map(|&q| {
            row(q)
                .as_chunks::<3>()
                .0
                .iter()
                .map(|w| F192::new(w[0].0, w[1].0, w[2].0))
        }));
        let paths = self.tree.prune(queries, row_words, row_words, &group_rows, row);
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
    poly: &[F192],
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

    // One leaf per row, its F192s as K words: hashed as the encode finishes each block.
    let row_words = 3 * num_interleaved;
    let builder = merkle::MerkleBuilder::new(block_len, row_words, row_words);
    // The encode writes every matrix element before reading it.
    let encode = |mat: &mut [F192]| {
        tracing::info_span!(
            "NTT",
            kind = "extension encode",
            log_domain = log_block_len,
            lanes = num_interleaved
        )
        .in_scope(|| {
            let on_rows = |row, rows: &[F64]| builder.absorb(row, rows);
            let defer_deep = primitives::REBUILD_OVER_STORE;
            let (mat, msg) = (words_mut(mat), words(poly));
            ntt.encode_interleaved_with(mat, msg, 3 * num_interleaved, log_inv_rate, defer_deep, &on_rows)
                .map(|plan| (ntt, plan))
        })
    };
    let mut deep = None;
    // SAFETY: the fill writes every element before it reads any.
    let mat = unsafe { primitives::filled_vec(block_len * num_interleaved, |mat| deep = encode(mat)) };
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        mat,
        tree,
        block_len,
        num_interleaved,
        deep,
    }
}

// ===================================================================
// Stateful sumcheck over E
// ===================================================================
//
// Each round sends (u_0, u_2) of the quadratic
// q(X) = u_0 + u_1 X + u_2 X^2 with q(0) + q(1) = T_r, verifier derives
// u_1 = T_r + u_2 (char 2), round eval q(r) = u_0 + r T_r + (r + r^2) u_2.
//
// The lane rounds run on E-valued tables projected from the K-witness; the lift after them
// folds the witness itself, and all later rounds are pure E.

/// (u_0, u_2) per round in E.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    pub(crate) u_0: F192,
    pub(crate) u_2: F192,
}

/// Transmit the constant and quadratic coefficients; the claim fixes the linear coefficient.
fn send_msg(ps: &mut ProverState, m: SumcheckMessage, claim: F192) {
    ps.add_round_poly(&[m.u_0, claim + m.u_2, m.u_2], false);
}

/// Round-quadratic in coefficient form `c + b X + a X^2`.
#[derive(Clone, Copy, Debug)]
struct RoundQuad {
    c: F192, // u_0
    b: F192, // u_1 (X coeff), derived from T_r and u_2
    a: F192, // u_2 (X^2 coeff)
}

impl RoundQuad {
    /// The quadratic a round message stands for, given the claim it answers:
    /// `h(0) + h(1) = claim` fixes the linear coefficient.
    #[inline]
    fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    fn eval(&self, r: F192) -> F192 {
        (self.a * r + self.b) * r + self.c
    }
    #[inline]
    fn fold(p1: &Self, p2: &Self, alpha: F192) -> Self {
        Self {
            c: p1.c + alpha * p2.c,
            b: p1.b + alpha * p2.b,
            a: p1.a + alpha * p2.a,
        }
    }
}

/// Characteristic-two interpolation `x0·(1+r) + x1·r = x0 + r·(x0+x1)`: one product rather
/// than two, bit-identical, and still just one reduction.
#[inline]
fn fold_pair(x0: F192, x1: F192, r: F192) -> F192 {
    x0 + r * (x0 + x1)
}

/// [`fold_pair`] against an absent partner: the lane rounds pair the last lane with the
/// stacked witness's zero padding, so the interpolation collapses to `x0·(1+r)`.
#[inline]
fn fold_lone(x0: F192, r: F192) -> F192 {
    x0 + r * x0
}

/// `out[j] = fold_pair(x[2j], x[2j + 1], r)`.
#[inline]
fn fold_adjacent(out: &mut [F192], x: &[F192], r: F192) {
    let (o8, o_r) = out.as_chunks_mut::<8>();
    let (x16, x_r) = x.as_chunks::<16>();
    for (d, c) in o8.iter_mut().zip(x16) {
        let (even, odd) = deinterleave(c);
        *d = fold_pairs8_ext(&even, &odd, r);
    }
    for (d, p) in o_r.iter_mut().zip(x_r.as_chunks::<2>().0.iter()) {
        *d = fold_pair(p[0], p[1], r);
    }
}

/// The even and the odd elements of sixteen consecutive ones.
#[inline]
fn deinterleave(x: &[F192; 16]) -> ([F192; 8], [F192; 8]) {
    let [lo, hi] = x.as_chunks::<8>().0 else { unreachable!() };
    let (even, odd) = F192x8::even_odd(F192x8::from_array(lo), F192x8::from_array(hi));
    (even.to_array(), odd.to_array())
}

/// `(sum f0*b0, sum (f0+f1)*(b0+b1))` over the adjacent pairs `(f[2j], f[2j + 1])`, unreduced, plus,
/// when `ODD`, `sum f1*b1` over the same pairs (the other half of the inner product `sum f*b` once
/// `u_0 = sum f0*b0` is added). A trailing odd element contributes nothing.
#[inline]
pub(crate) fn adjacent_dots<const ODD: bool>(f: &[F192], b: &[F192]) -> (Acc8, Acc8, Acc8) {
    let (f16, f_r) = f.as_chunks::<16>();
    let (b16, b_r) = b.as_chunks::<16>();
    let (mut u_0, mut u_2, mut odd) = (Acc8::ZERO, Acc8::ZERO, Acc8::ZERO);
    for (x, y) in f16.iter().zip(b16) {
        let ((f0, f1), (b0, b1)) = (deinterleave(x), deinterleave(y));
        let (t_0, t_2) = msg_terms8_ext(&f0, &f1, &b0, &b1);
        u_0 ^= t_0;
        u_2 ^= t_2;
        if ODD {
            odd ^= msg_lone8_ext(&f1, &b1);
        }
    }
    // Fewer than eight pairs are left: scalar products, summed before they enter an accumulator.
    let (mut r_0, mut r_2, mut r_odd) = (F192Unreduced::ZERO, F192Unreduced::ZERO, F192Unreduced::ZERO);
    for (p, q) in f_r.as_chunks::<2>().0.iter().zip(b_r.as_chunks::<2>().0.iter()) {
        r_0 ^= p[0].mul_unreduced(q[0]);
        r_2 ^= (p[0] + p[1]).mul_unreduced(q[0] + q[1]);
        if ODD {
            r_odd ^= p[1].mul_unreduced(q[1]);
        }
    }
    u_0 ^= Acc8::from(r_0);
    u_2 ^= Acc8::from(r_2);
    odd ^= Acc8::from(r_odd);
    (u_0, u_2, odd)
}

/// Round message over a witness `f` and a basis `b`.
///
/// Deferred reduction: XOR-accumulate the raw lane products (no reduction tail
/// per term) and reduce once per accumulator. Reduction commutes with XOR, so
/// the message is bit-identical to reducing every term.
fn round_msg_lsb(f: &[F192], b: &[F192]) -> SumcheckMessage {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    // `ROUND_CHUNK` is even, so no pair straddles two tasks.
    let task = |c: usize| {
        let at = c * ROUND_CHUNK..(c * ROUND_CHUNK + ROUND_CHUNK).min(n);
        let (u_0, u_2, _) = adjacent_dots::<false>(&f[at.clone()], &b[at]);
        (u_0, u_2)
    };
    let (u_0, u_2) = accumulate_msg(n.div_ceil(ROUND_CHUNK), n / 2, task);
    SumcheckMessage {
        u_0: u_0.reduce(),
        u_2: u_2.reduce(),
    }
}

/// Build the round message and the full inner product in one pass. For an OOD
/// basis `b = eq(z, ·)`, the inner product is the claimed MLE evaluation.
fn round_msg_and_eval_lsb_ext(f: &[F192], b: &[F192]) -> (SumcheckMessage, F192) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let dots = |at: std::ops::Range<usize>| adjacent_dots::<true>(&f[at.clone()], &b[at]);
    let (u_0, u_2, odd) = if n / 2 < PAR_THRESHOLD {
        dots(0..n)
    } else {
        parallel::map_reduce(
            n.div_ceil(ROUND_CHUNK),
            || (Acc8::ZERO, Acc8::ZERO, Acc8::ZERO),
            |c| dots(c * ROUND_CHUNK..(c * ROUND_CHUNK + ROUND_CHUNK).min(n)),
            |(mut a0, mut a2, mut ao), (b0, b2, bo)| {
                a0 ^= b0;
                a2 ^= b2;
                ao ^= bo;
                (a0, a2, ao)
            },
        )
    };
    let mut y = u_0;
    y ^= odd;
    (
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
        y.reduce(),
    )
}

/// Outputs a fused fold writes before its message reads them, so the reads hit settled stores rather than stores
/// still in flight.
const FOLD_STAGE: usize = 256;

/// Fold outputs of at least this many elements (12 MiB) take streaming stores.
///
/// An output this large is evicted from a worker's share of the L3 before the next round reads it, so an ordinary
/// store only adds the line fetch.
const STREAM_FOLD_MIN: usize = 1 << 19;

/// Fused fold + next-round message: the witness and the basis fold, and the
/// next-round message is built over the freshly folded values in the same pass.
fn fold_and_msg_lsb(f: &[F192], b: &[F192], r: F192) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    // `half` is a power of two and so are `ROUND_CHUNK` and `FOLD_STAGE`: every window has even
    // length and starts at an even index, so no message pair straddles one.
    let stream = half >= STREAM_FOLD_MIN;
    let task = |ci: usize, fc: &mut [F192], bc: &mut [F192]| {
        let base = ci * ROUND_CHUNK;
        let len = fc.len();
        let mut acc = (Acc8::ZERO, Acc8::ZERO);
        let fold = |fo: &mut [F192], bo: &mut [F192], at: std::ops::Range<usize>| {
            fold_adjacent(fo, &f[at.clone()], r);
            fold_adjacent(bo, &b[at], r);
            adjacent_dots::<false>(fo, bo)
        };
        let (mut sf, mut sb) = ([F192::ZERO; FOLD_STAGE], [F192::ZERO; FOLD_STAGE]);
        let st = primitives::stream::Stream::new();
        for s in (0..len).step_by(FOLD_STAGE) {
            let k = FOLD_STAGE.min(len - s);
            let at = 2 * (base + s)..2 * (base + s + k);
            let (u_0, u_2, _) = if stream {
                // Folded in L1, then streamed: an output this large is not read back from cache.
                let d = fold(&mut sf[..k], &mut sb[..k], at);
                st.copy(&mut fc[s..s + k], &sf[..k]);
                st.copy(&mut bc[s..s + k], &sb[..k]);
                d
            } else {
                fold(&mut fc[s..s + k], &mut bc[s..s + k], at)
            };
            acc.0 ^= u_0;
            acc.1 ^= u_2;
        }
        acc
    };
    // One output per input pair, so the tasks write every slot of `nf` and `nb`.
    let mut msg = (Acc8::ZERO, Acc8::ZERO);
    // SAFETY: the fill writes every element before it reads any.
    let [nf, nb] = unsafe {
        primitives::filled_vecs([half; 2], |[nf, nb]| {
            msg = accumulate_msg_chunks(nf, nb, ROUND_CHUNK, task)
        })
    };
    let (u_0, u_2) = msg;
    (
        nf,
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

// ===================================================================
// Lane rounds: the L0 fold binds whole lanes, not adjacent words
// ===================================================================
//
// The committed witness is stored lane-major (lane `l` is the contiguous stack
// block `q[l·H .. (l+1)·H)`, `H = 2^(log_n − initial_k)`), because that is what
// makes the stacked witness's zero padding whole lanes and lets the commitment
// leave them out entirely. The first `initial_k` sumcheck rounds are therefore
// the lane fold: round `j` binds lane bit `j`, pairing block `2i` with block
// `2i+1`, and an odd block count pairs the last one with the absent zero
// padding. They run on the small tables of the initial basis, one block per lane;
// after them the buffers are one `H`-element block and every later round is the
// ordinary adjacent-pair fold.

/// Elements per task wherever a round is chunked.
/// Below this many items a pass runs on the calling thread: a dispatch costs more than it saves.
const PAR_THRESHOLD: usize = 4096;

const ROUND_CHUNK: usize = 2048;

/// Sum the per-task `(u_0, u_2)` accumulators, sequentially for the small
/// instances where dispatch costs more than the work. Unreduced accumulators
/// combine by XOR and `reduce` is linear, so both paths land on the same message.
#[inline]
pub(crate) fn accumulate_msg(
    n_tasks: usize,
    n_pairs: usize,
    task: impl Fn(usize) -> (Acc8, Acc8) + Sync,
) -> (Acc8, Acc8) {
    if n_pairs < PAR_THRESHOLD {
        let mut u_0 = Acc8::ZERO;
        let mut u_2 = Acc8::ZERO;
        for t in 0..n_tasks {
            let (t0, t2) = task(t);
            u_0 ^= t0;
            u_2 ^= t2;
        }
        (u_0, u_2)
    } else {
        parallel::map_reduce(
            n_tasks,
            || (Acc8::ZERO, Acc8::ZERO),
            task,
            |(mut a0, mut a2), (c0, c2)| {
                a0 ^= c0;
                a2 ^= c2;
                (a0, a2)
            },
        )
    }
}

/// [`accumulate_msg`] over the chunks of two output tables, which `task(i, ..)` fills.
#[inline]
fn accumulate_msg_chunks(
    f: &mut [F192],
    b: &mut [F192],
    chunk: usize,
    task: impl Fn(usize, &mut [F192], &mut [F192]) -> (Acc8, Acc8) + Sync,
) -> (Acc8, Acc8) {
    if f.len() < PAR_THRESHOLD {
        let (mut u_0, mut u_2) = (Acc8::ZERO, Acc8::ZERO);
        for (t, (fc, bc)) in f.chunks_mut(chunk).zip(b.chunks_mut(chunk)).enumerate() {
            let (t0, t2) = task(t, fc, bc);
            u_0 ^= t0;
            u_2 ^= t2;
        }
        (u_0, u_2)
    } else {
        parallel::map_reduce_chunks_mut(
            [f, b],
            [chunk; 2],
            || (),
            || (Acc8::ZERO, Acc8::ZERO),
            |(), acc, t, [fc, bc]| {
                let (t0, t2) = task(t, fc, bc);
                acc.0 ^= t0;
                acc.1 ^= t2;
            },
            |(mut a0, mut a2), (c0, c2)| {
                a0 ^= c0;
                a2 ^= c2;
                (a0, a2)
            },
        )
    }
}

/// `(u_0, u_2)` over one pair of blocks, elementwise.
#[inline]
fn msg_terms_pair(f0: &[F192], f1: &[F192], b0: &[F192], b1: &[F192]) -> (Acc8, Acc8) {
    let (mut u_0, mut u_2) = (Acc8::ZERO, Acc8::ZERO);
    let ((f0_8, f0_r), (f1_8, f1_r)) = (f0.as_chunks::<8>(), f1.as_chunks::<8>());
    let ((b0_8, b0_r), (b1_8, b1_r)) = (b0.as_chunks::<8>(), b1.as_chunks::<8>());
    for (((x0, x1), y0), y1) in f0_8.iter().zip(f1_8).zip(b0_8).zip(b1_8) {
        let (t0, t2) = msg_terms8_ext(x0, x1, y0, y1);
        u_0 ^= t0;
        u_2 ^= t2;
    }
    for (((&x0, &x1), &y0), &y1) in f0_r.iter().zip(f1_r).zip(b0_r).zip(b1_r) {
        u_0 ^= Acc8::from(x0.mul_unreduced(y0));
        u_2 ^= Acc8::from((x0 + x1).mul_unreduced(y0 + y1));
    }
    (u_0, u_2)
}

/// [`msg_terms_pair`] against an absent partner block. With `f1 = b1 = 0` both
/// `h(0)` and `h(inf)` collect the same `Σ f0·b0`, so this is NOT a no-op the way
/// a trailing odd element is in an adjacent-pair round.
#[inline]
fn msg_terms_lone(f0: &[F192], b0: &[F192]) -> (Acc8, Acc8) {
    let mut u = Acc8::ZERO;
    let ((f0_8, f0_r), (b0_8, b0_r)) = (f0.as_chunks::<8>(), b0.as_chunks::<8>());
    for (x0, y0) in f0_8.iter().zip(b0_8) {
        u ^= msg_lone8_ext(x0, y0);
    }
    for (&x0, &y0) in f0_r.iter().zip(b0_r) {
        u ^= Acc8::from(x0.mul_unreduced(y0));
    }
    (u, u)
}

/// Round message for a lane round, over `f.len() / block` blocks.
fn round_msg_blocks(f: &[F192], b: &[F192], block: usize) -> SumcheckMessage {
    // Real asserts, not debug ones: the crate is only ever built in release, and a
    // block count that truncates drops the trailing block from BOTH u_0 and u_2,
    // which is a well-formed but wrong round message rather than a panic.
    assert_eq!(b.len(), f.len());
    assert!(block > 0 && f.len().is_multiple_of(block));
    let (mut u_0, mut u_2) = (Acc8::ZERO, Acc8::ZERO);
    for (f, b) in f.chunks(2 * block).zip(b.chunks(2 * block)) {
        let ((f0, f1), (b0, b1)) = (f.split_at(block), b.split_at(block));
        let (t_0, t_2) = if f1.is_empty() {
            msg_terms_lone(f0, b0)
        } else {
            msg_terms_pair(f0, f1, b0, b1)
        };
        u_0 ^= t_0;
        u_2 ^= t_2;
    }
    SumcheckMessage {
        u_0: u_0.reduce(),
        u_2: u_2.reduce(),
    }
}

/// `x` after one lane round: block `2j` and block `2j + 1` fold into block `j`, a last
/// block without a partner against the absent zero padding.
fn fold_blocks(x: &[F192], block: usize, r: F192) -> Vec<F192> {
    let mut out = vec![F192::ZERO; x.len().div_ceil(2 * block) * block];
    for (out, x) in out.chunks_exact_mut(block).zip(x.chunks(2 * block)) {
        let (lo, hi) = x.split_at(block);
        if hi.is_empty() {
            fold_lones_batched(out, lo, r);
        } else {
            fold_pairs_batched(out, lo, hi, r);
        }
    }
    out
}

/// Builds block `h` of the weight over a lane block after every lane round from the witness block `f`, and
/// returns the unreduced message terms of `f` against it.
pub(crate) type LiftBlock<'a> = Box<dyn Fn(usize, &[F192], &mut [F192]) -> (Acc8, Acc8) + Sync + 'a>;

/// The weight over one lane block after every lane round, rebuilt from the term table's last row.
pub(crate) trait LaneLift {
    /// The per-block body for the table row `a`. A block is `2^low_vars` words, the length of the
    /// `f` and `out` it is given.
    fn blocks<'a>(&'a self, a: &[F192]) -> LiftBlock<'a>;
}

/// The basis the sumcheck starts from: the weight as terms, `b(l, x) = sum_t a[l][t] * K_t(x)`,
/// so that for any two lanes `sum_x f(l, x) * b(l', x) = sum_t p[l][t] * a[l'][t]`, with
/// `p[l][t] = sum_x f(l, x) * K_t(x)`. Both tables are lane-major with `block` terms per lane,
/// and the lane rounds run on them in place of the witness and the weight. `lift` rebuilds the
/// weight after the last one.
pub(crate) struct InitialBasis {
    pub(crate) p: Vec<F192>,
    pub(crate) a: Vec<F192>,
    pub(crate) block: usize,
    /// Words of a block the lift takes.
    pub(crate) lift_len: usize,
    pub(crate) lift: Box<dyn LaneLift>,
}

/// `out[i] = fold_pair(x0[i], x1[i], r)`, eight at a time where the multiplier is wide.
#[inline]
fn fold_pairs_batched(out: &mut [F192], x0: &[F192], x1: &[F192], r: F192) {
    let (o8, o_r) = out.as_chunks_mut::<8>();
    let ((a8, a_r), (b8, b_r)) = (x0.as_chunks::<8>(), x1.as_chunks::<8>());
    for ((d, a), b) in o8.iter_mut().zip(a8).zip(b8) {
        *d = fold_pairs8_ext(a, b, r);
    }
    for ((d, &a), &b) in o_r.iter_mut().zip(a_r).zip(b_r) {
        *d = fold_pair(a, b, r);
    }
}

#[inline]
fn fold_lones_batched(out: &mut [F192], x0: &[F192], r: F192) {
    let (o8, o_r) = out.as_chunks_mut::<8>();
    let (a8, a_r) = x0.as_chunks::<8>();
    for (d, a) in o8.iter_mut().zip(a8) {
        *d = fold_lones8_ext(a, r);
    }
    for (d, &a) in o_r.iter_mut().zip(a_r) {
        *d = fold_lone(a, r);
    }
}

/// `acc[j] += s * v[j]`, eight at a time where the multiplier is wide.
#[inline]
fn add_scaled(acc: &mut [F192], v: &[F192], s: F192) {
    let (a8, a_r) = acc.as_chunks_mut::<8>();
    let (v8, v_r) = v.as_chunks::<8>();
    let s8 = F192x8::splat(s);
    for (a, v) in a8.iter_mut().zip(v8) {
        *a = (F192x8::from_array(a) + s8 * F192x8::from_array(v)).to_array();
    }
    for (a, &v) in a_r.iter_mut().zip(v_r) {
        *a += s * v;
    }
}

/// `out[x] = sum_l w_l * cur_l[x]` over `(w_l, cur_l, next_l)`.
///
/// The products stay unreduced across the lanes, one reduction per output, a chunk of outputs at a
/// time so that their accumulators stay in L1. Each line of `cur_l` read also prefetches the same line
/// of `next_l` into L2 (when not empty), so the next block streams in while this one multiplies.
#[inline]
fn lane_sums<'a>(out: &mut [F192], lanes: impl Iterator<Item = (F192, &'a [F64], &'a [F64])> + Clone) {
    const CHUNK: usize = 64;
    for (k, out) in out.as_chunks_mut::<8>().0.chunks_mut(CHUNK).enumerate() {
        let mut acc = [Prod8::ZERO; CHUNK];
        for (w, cur, next) in lanes.clone() {
            for (j, (a, c)) in acc.iter_mut().zip(&cur.as_chunks::<8>().0[CHUNK * k..]).enumerate() {
                prefetch_l2(next, 8 * (CHUNK * k + j));
                *a ^= primitives::field::mul_base_splat8(w, c);
            }
        }
        for (o, a) in out.iter_mut().zip(&acc) {
            *o = a.reduce_each();
        }
    }
}

/// Prefetch the line of `words` at `at` into L2, when it exists. A no-op off x86: Apple silicon's
/// own prefetchers already cover the sweep.
#[inline(always)]
fn prefetch_l2(words: &[F64], at: usize) {
    #[cfg(target_arch = "x86_64")]
    if let Some(line) = words.get(at) {
        // SAFETY: a prefetch never faults.
        unsafe {
            core::arch::x86_64::_mm_prefetch::<{ core::arch::x86_64::_MM_HINT_T1 }>(std::ptr::from_ref(line).cast())
        };
    }
    #[cfg(not(target_arch = "x86_64"))]
    let _ = (words, at);
}

/// The witness and the lifted weight after every lane round, and the message of one against the other.
///
/// The witness is straight from the base lanes: `sum_l eq(rs, l) * base_l`.
///
/// `lift` turns each witness block into its weight block while the witness block is still in cache, and both
/// stream out.
fn fold_all_lanes(
    base: &[F64],
    block: usize,
    rs: &[F192],
    run: usize,
    lift: &LiftBlock,
) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    const TASK: usize = 32;
    let weights = primitives::multilinear::eq_table(rs);
    let mut sums = (Acc8::ZERO, Acc8::ZERO);
    // Every task streams each of its output blocks below.
    // SAFETY: the fill writes every element before it reads any.
    let [f, b] = unsafe {
        primitives::filled_vecs([block; 2], |[f, b]| {
            sums = accumulate_msg_chunks(f, b, TASK * run, |c, f_out, b_out| {
                let out_blocks = f_out.len() / run;
                // The witness block and the weight block stay in L1 and L2; the outputs take only streaming stores,
                // so they are never fetched.
                let mut acc = vec![F192::ZERO; run];
                let mut weight = vec![F192::ZERO; run];
                let (mut u_0, mut u_2) = (Acc8::ZERO, Acc8::ZERO);
                let stream = primitives::stream::Stream::new();
                for i in 0..out_blocks {
                    let h = c * TASK + i;
                    let lanes = base.chunks_exact(block).enumerate().map(|(l, lane)| {
                        // The lane's next block, when this task reads it.
                        let next = if i + 1 < out_blocks {
                            &lane[(h + 1) * run..(h + 2) * run]
                        } else {
                            &[][..]
                        };
                        (weights[l], &lane[h * run..(h + 1) * run], next)
                    });
                    lane_sums(&mut acc, lanes);
                    let (t_0, t_2) = lift(h, &acc, &mut weight);
                    u_0 ^= t_0;
                    u_2 ^= t_2;
                    stream.copy(&mut f_out[i * run..][..run], &acc);
                    stream.copy(&mut b_out[i * run..][..run], &weight);
                }
                (u_0, u_2)
            });
        })
    };
    let (u_0, u_2) = sums;
    let msg = SumcheckMessage {
        u_0: u_0.reduce(),
        u_2: u_2.reduce(),
    };
    (f, b, msg)
}

/// Running sumcheck: the lane rounds on the tables of the initial basis, then extension-field folds.
pub(crate) struct SumcheckProver {
    /// The committed lanes, kept past the lift for [`Self::take_stack`].
    base: Vec<F64>,
    /// The table `P` during the lane rounds, then the folded witness.
    f: Vec<F192>,
    /// The table `A` during the lane rounds, then the single combined basis poly:
    /// `glue_pending(lambda)` folds each claim introduced since the last glue in as
    /// `combined_basis += lambda^tau * b_new`, `tau` counting from 1 (the running claim is `tau = 0`).
    combined_basis: Vec<F192>,
    /// Elements of a lane block of the tables, and of the committed lanes.
    block: usize,
    lane_block: usize,
    /// Words of a block the lift takes.
    lift_len: usize,
    /// Taken by the last lane round.
    lift: Option<Box<dyn LaneLift>>,
    /// The lane challenges so far.
    lane_rs: Vec<F192>,
    /// The running claim and its quadratic; `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    quad: RoundQuad,
    round: usize,
    /// The level's claims, in Protocol 1 step 1 order: the OOD claims, then the
    /// query batch. Drained by `glue_pending`.
    pending: Vec<(Vec<F192>, F192, RoundQuad)>,
}

impl SumcheckProver {
    /// `lane_block` is the lane block size `2^(log_n - initial_k)` of the committed lanes `f`: the
    /// first `initial_k` rounds are the lane fold, so round 0's message already pairs whole
    /// blocks of the tables rather than adjacent words.
    pub(crate) fn new(f: Vec<F64>, b1: InitialBasis, h1: F192, lane_block: usize) -> (Self, SumcheckMessage) {
        let _span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().ilog2()).entered();
        assert!(lane_block > 0 && f.len().is_multiple_of(lane_block));
        let InitialBasis {
            p,
            a,
            block,
            lift_len,
            lift,
        } = b1;
        assert_eq!(p.len(), f.len() / lane_block * block);
        assert!(lane_block.is_multiple_of(lift_len));
        let msg = round_msg_blocks(&p, &a, block);
        let inst = Self {
            base: f,
            f: p,
            combined_basis: a,
            block,
            lane_block,
            lift_len,
            lift: Some(lift),
            lane_rs: Vec::new(),
            t_r: h1,
            quad: RoundQuad::from_msg(msg, h1),
            round: 0,
            pending: Vec::new(),
        };
        (inst, msg)
    }

    /// The claim that fixes the next message's linear coefficient.
    #[inline]
    pub(crate) fn claim(&self) -> F192 {
        self.t_r
    }

    /// One lane round: fold block `2i` with block `2i+1` of both tables (the last one with the
    /// absent zero padding when the block count is odd) and build the message for the round
    /// after it, which is another lane round unless this was the last.
    ///
    /// The last one lifts the tables to the witness and the weight over one lane block, and the
    /// message is the adjacent-pair one over them.
    pub(crate) fn fold_lane(&mut self, r: F192, last: bool) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let _span =
            tracing::info_span!("Sumcheck round", round = self.round, log_size = self.f.len().ilog2()).entered();
        self.lane_rs.push(r);
        self.f = fold_blocks(&self.f, self.block, r);
        self.combined_basis = fold_blocks(&self.combined_basis, self.block, r);
        let msg = if last {
            let lift = self.lift.take().expect("the lift is taken by the last lane round only");
            let blocks = lift.blocks(&self.combined_basis);
            let (f, b, msg) = fold_all_lanes(&self.base, self.lane_block, &self.lane_rs, self.lift_len, &blocks);
            (self.f, self.combined_basis) = (f, b);
            msg
        } else {
            round_msg_blocks(&self.f, &self.combined_basis, self.block)
        };
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// The committed lanes if `keep`, once the lane rounds have read them for the last time. Otherwise they go now.
    fn take_stack(&mut self, keep: bool) -> Vec<F64> {
        assert!(self.lift.is_none(), "the lane rounds are over");
        let base = std::mem::take(&mut self.base);
        if keep { base } else { Vec::new() }
    }

    fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let _span =
            tracing::info_span!("Sumcheck round", round = self.round, log_size = self.f.len().ilog2()).entered();
        let (nf, nb, msg) = fold_and_msg_lsb(&self.f, &self.combined_basis, r);
        // Swap the freshly folded buffers in and drop the consumed ones, so the
        // allocator serves the next round's `filled_vecs` from their memory.
        drop(std::mem::replace(&mut self.f, nf));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    fn introduce_new(&mut self, b_new: Vec<F192>, h_new: F192) -> SumcheckMessage {
        assert_eq!(b_new.len(), self.f.len());
        let msg = round_msg_lsb(&self.f, &b_new);
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        msg
    }

    /// Introduce the OOD basis `eq(z, ·)` and compute its claimed inner product in the same
    /// pass as the round message.
    fn introduce_ood(&mut self, z: &[F192]) -> (SumcheckMessage, F192) {
        assert_eq!(1 << z.len(), self.f.len());
        let b_new = build_eq_table_ext_parallel(z);
        let (msg, h_new) = round_msg_and_eval_lsb_ext(&self.f, &b_new);
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        (msg, h_new)
    }

    /// Batch every claim introduced since the last glue into the running one
    /// with powers of the level's single batching challenge (PCS annex,
    /// Protocol 1 step 1): claim `tau` (counting from 1) contributes
    /// `combined_basis[j] += lambda^tau * b_new[j]`, `T_r += lambda^tau *
    /// h_new`. The running claim keeps `lambda^0 = 1`.
    fn glue_pending(&mut self, lambda: F192) {
        let pending = std::mem::take(&mut self.pending);
        assert!(!pending.is_empty(), "glue without introduce_new");
        let mut scalar = F192::ONE;
        for (b_new, h_new, quad_new) in pending {
            scalar *= lambda;
            assert_eq!(b_new.len(), self.combined_basis.len());
            self.t_r += scalar * h_new;
            self.quad = RoundQuad::fold(&self.quad, &quad_new, scalar);
            let chunk = parallel::recommended_chunk_size(b_new.len());
            parallel::chunks_mut_zip(&mut self.combined_basis, &b_new, chunk, |_, acc, v| {
                add_scaled(acc, v, scalar)
            });
        }
    }

    #[cfg(test)]
    pub(crate) fn basis(&self) -> &[F192] {
        &self.combined_basis
    }

    /// The folded witness, once the lane rounds are done.
    pub(crate) fn f_ext(&self) -> &[F192] {
        &self.f
    }
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊192/d⌋` positions as
/// its disjoint d-bit chunks (low bits first), matching the scheme the recursive guest derives (fixed `192/d` per
/// squeeze, dup-tolerant: soundness matches the deployed PCS with the same
/// `config.queries`). Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
///
fn sample_queries_ordered(ch: &mut ProverState, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = ch.sample();
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [v.c0, v.c1, v.c2];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    out
}

/// Prover side of the OOD claims taken right after a level's root enters the
/// transcript: sample `z`, evaluate the folded witness there, send the claim
/// and its intro message. The claim stays pending: the level's batching
/// challenge is drawn only once its query positions are fixed too, and
/// `glue_pending` then folds every claim of the level in with its own power.
/// A verifier replays it operation for operation.
fn send_ood(sc: &mut SumcheckProver, ps: &mut ProverState, n_vars: usize, count: usize) {
    for _ in 0..count {
        let z = ps.sample_vec(n_vars);
        let (intro, y) = sc.introduce_ood(&z);
        ps.add_scalar(y);
        send_msg(ps, intro, y);
    }
}

/// The row at position `q` out of `rows`, `row_words` each, back to back, which hold the sorted `group` positions.
fn fetched_row<'a>(group: &[usize], rows: &'a [F64], row_words: usize, q: usize) -> &'a [F64] {
    let k = group.binary_search(&q).expect("a fetched row");
    &rows[k * row_words..][..row_words]
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is owned: where the L0 open recomputes the codeword rows it reads, it keeps it until then.
/// Otherwise the lane rounds read it last, and the large committed stack is gone before the level-1 commit allocates.
///
/// PRECONDITION, and the reason `witness` may be shorter than `2^log_n`: it is a
/// whole number of lane blocks, and `b_initial` must stand for the weight restricted to
/// them, with the weight VANISHING at every boolean point of
/// `[witness.len(), 2^log_n)`. The lane rounds treat the absent blocks as zero
/// while a verifier evaluates the weight's closed form over the whole cube,
/// so a weight that is nonzero out there produces a proof that fails only at the
/// terminal check. `stack_open` discharges this by bounding every claim's support
/// by `stack.len()`; `ood_samples[0] == 0` is what keeps a full-tensor OOD weight
/// out of these rounds.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one phase per level. The caller has already bound the initial commitment and target.
pub(crate) fn recursive_prover_with_prepared_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: Vec<F64>,
    b_initial: InitialBasis,
    target: F192,
    prover_data: ProverData,
    ps: &mut ProverState,
) {
    let l0_tree = &prover_data.merkle_tree;
    let r = config.level_steps;
    let initial_k = config.initial_k;

    assert_eq!(config.level_ks.len(), r);
    assert_eq!(config.log_inv_rates.len(), r + 1);
    assert!(r >= 1);
    assert!(initial_k >= 1);
    // L0 takes no OOD sample, and the padding-free truncation now depends on it:
    // the lane rounds are the only ones folding the truncated witness against a
    // weight over the whole `2^log_n` cube, and an OOD weight `eq(z, .)` is a full
    // tensor that does NOT vanish on the absent lanes, unlike every claim weight.
    assert_eq!(config.ood_samples.first().copied().unwrap_or(0), 0);

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
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
    assert_eq!(prover_data.len(), block_len_0 * prover_data.row_words);
    assert!((n_lanes..=num_interleaved_0).contains(&prover_data.row_words));

    // Nothing is absorbed on entry. The commitment was bound by the `add_root` that
    // transmitted it, and the target is `sum_i lambda^i * claim_i` over claim values bound by their
    // own reads, with lambda drawn from the state: the state already determines both. Every caller
    // must therefore have transmitted its root before opening against it, which is what makes the
    // fold challenges depend on the commitment.

    // L0 codeword + tree are borrowed (reused from `commit`); the root itself is never needed
    // here, the caller having transmitted it.
    // The codeword interleaves only the committed lanes, and its lane `t` is stack
    // block `n_lanes-1-t`, so a row IS the tail of the leaf image: the absent lanes
    // are the image's leading zeros (`MerkleBuilder` shares their hash prefix, and only
    // this tail rides the proof).
    // The induce folds a lane-ASCENDING row against the lane eq table: reversing the image puts
    // block `b` at index `b` and the absent lanes' zeros at the end, where they contribute nothing.

    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };

    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc_prover, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, b_initial, target, lane_block));
    send_msg(ps, start_msg, target);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        let r_j = ps.sample();
        let msg = sumcheck_span.in_scope(|| sc_prover.fold_lane(r_j, j + 1 == initial_k));
        send_msg(ps, msg, sc_prover.claim());
        r_lane_fold.push(r_j);
    }
    drop(sumcheck_span);
    // A rebuilding L0 open recomputes its rows from the stack, so that lives until then. Otherwise it goes now.
    let stack = sc_prover.take_stack(prover_data.rebuilds());

    // Commit f^1 = folded (now E-valued) witness as wtns_1.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates[1];
    let span = tracing::info_span!("Commit", level = 1).entered();
    let wtns_1 = ligero_commit_ext(sc_prover.f_ext(), log_msg_cols_1, log_num_interleaved_1, log_inv_rate_1);
    drop(span);
    ps.add_root(&wtns_1.root());

    // Bind the L1 Johnson list before drawing L0 queries. Each claimed random
    // MLE evaluation is introduced into the running sumcheck.
    send_ood(&mut sc_prover, ps, n1, ood_count(1));

    // Query-phase PoW grinding for L0 (0 bits in the production profile; the
    // canonical 0 nonce is still absorbed to keep the transcript in lockstep).
    ps.grind(config.grinding_bits[0] as u32);

    // Open L0; lane-fold weights = r_lane_fold.
    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered(ps, block_len_0, num_queries_0);
    // One batching challenge for the whole level, drawn once every claim it
    // batches is fixed: the OOD claims above and these query positions.
    let lambda_0 = ps.sample();
    let weights_0 = powers(lambda_0, num_queries_0);
    let span = tracing::info_span!("Open", level = 0).entered();
    // Ordered (dup-possible) rows for the local induce math ...
    // The tree keeps no leaves: the rows of whole leaf groups are read back and rehashed.
    let row_words = prover_data.row_words;
    let group_0 = l0_tree.group_positions(&queries_0);
    let group_rows_0 = prover_data.l0(&stack, n_lanes).rows(&group_0);
    let image = |q| &fetched_row(&group_0, &group_rows_0, row_words, q)[row_words - n_lanes..];
    let mut opened_rows_0 = Vec::with_capacity(queries_0.len() * num_interleaved_0);
    for &q in &queries_0 {
        let zeros = std::iter::repeat_n(F64::ZERO, num_interleaved_0 - n_lanes);
        opened_rows_0.extend(image(q).iter().rev().copied().chain(zeros));
    }
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    ps.hint_merkle(l0_tree.prune(&queries_0, row_words, num_interleaved_0, &group_rows_0, image));
    // Nothing reads the L0 codeword, its stack or its tree again, and the next levels' buffers can be served
    // from their memory.
    drop((prover_data, stack));
    drop(span);

    // Induce basis_0 from the L0 opens: the dispatcher picks the sparse transposed NTT wherever the level opens
    // more queries than its blowup.
    let sks_vks_n1 = eval_sk_at_vks(n1);
    let span = tracing::info_span!("Induce", level = 0).entered();
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto_base(
        n1,
        log_inv_rate_0,
        &sks_vks_n1,
        &opened_rows_0,
        &r_lane_fold,
        &queries_0,
        &weights_0,
    );
    drop(span);

    // Introduce basis_0, then batch the level's claims with powers of lambda_0.
    let span = tracing::info_span!("Introduce", level = 0).entered();
    let intro_msg_0 = sc_prover.introduce_new(basis_0_induced, enforced_sum_0);
    send_msg(ps, intro_msg_0, enforced_sum_0);
    sc_prover.glue_pending(lambda_0);
    drop(span);

    // Recursive levels.
    let mut wtns_prev = wtns_1;

    for i in 0..r {
        let k_i = config.level_ks[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let sumcheck_span = tracing::info_span!("Sumcheck");
        for _ in 0..k_i {
            let ri = ps.sample();
            let msg = sumcheck_span.in_scope(|| sc_prover.fold(ri));
            send_msg(ps, msg, sc_prover.claim());
            level_rs.push(ri);
        }
        drop(sumcheck_span);

        if i == r - 1 {
            ps.add_scalars(sc_prover.f_ext());
            // PoW grinding for the last level before sampling its queries.
            ps.grind(config.grinding_bits[i + 1] as u32);
            let num_queries_last = config.queries[i + 1];
            let queries_last = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_last);
            // The final level's batching challenge is drawn only after `yr`
            // and its queries are bound, matching the verifier exactly.
            let lambda_last = ps.sample();
            let weights_last = powers(lambda_last, num_queries_last);
            let span = tracing::info_span!("Final level").entered();
            // Final level: stored (sorted-unique) only, no local induce; the
            // verifier fans these to ordered for its last-level induce.
            let (rows_last, paths) = wtns_prev.open(&queries_last);
            ps.hint_merkle(paths);
            // Tie the last commitment into the running claim through the same
            // intro/glue step as every other level, then finish the remaining
            // sumcheck rounds. This closes on one weight evaluation instead of
            // a sweep over the residual cube.
            let enforced_sum_last = induce_sumcheck_enforced_sum(&rows_last, &level_rs, &queries_last, &weights_last);
            let n_res = sc_prover.f_ext().len().trailing_zeros() as usize;
            let basis_last =
                induce_sumcheck_evaluate_at_residual(n_res, &eval_sk_at_vks(n_res), &queries_last, &weights_last);
            let intro_msg_last = sc_prover.introduce_new(basis_last, enforced_sum_last);
            send_msg(ps, intro_msg_last, enforced_sum_last);
            sc_prover.glue_pending(lambda_last);
            for j in 0..n_res {
                let ri = ps.sample();
                let msg = sc_prover.fold(ri);
                // The last round's message is redundant: the verifier gets that
                // claim from `yr`, so it is never transmitted.
                if j + 1 < n_res {
                    send_msg(ps, msg, sc_prover.claim());
                }
            }
            drop(span);
            return;
        }

        let n_next = sc_prover.f_ext().len().trailing_zeros() as usize;
        let log_num_interleaved_next = config.level_ks[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let log_msg_cols_next = n_next - log_num_interleaved_next;
        let log_inv_rate_next = config.log_inv_rates[i + 2];
        let span = tracing::info_span!("Commit", level = i + 2).entered();
        let wtns_next = ligero_commit_ext(
            sc_prover.f_ext(),
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
        );
        drop(span);
        ps.add_root(&wtns_next.root());

        send_ood(&mut sc_prover, ps, n_next, ood_count(i + 2));

        // PoW grinding for this iteration's query phase.
        ps.grind(config.grinding_bits[i + 1] as u32);
        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_i);
        let lambda_i = ps.sample();
        let weights_i = powers(lambda_i, num_queries_i);
        let span = tracing::info_span!("Open", level = i + 1).entered();
        // Ordered rows for the local induce; sorted-unique rows + octopus stored.
        let (opened_rows_i, paths) = wtns_prev.open(&queries_i);
        ps.hint_merkle(paths);
        drop(span);

        let sks_vks_i = eval_sk_at_vks(n_next);
        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let (basis_i_induced, enforced_sum_i) =
            induce_sumcheck_poly(n_next, &sks_vks_i, &opened_rows_i, &level_rs, &queries_i, &weights_i);
        drop(span);

        let span = tracing::info_span!("Introduce", level = i + 1).entered();
        let intro_msg_i = sc_prover.introduce_new(basis_i_induced, enforced_sum_i);
        send_msg(ps, intro_msg_i, enforced_sum_i);
        sc_prover.glue_pending(lambda_i);
        drop(span);

        wtns_prev = wtns_next;
    }

    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stack_open::{RingSwitchOpen, StackClaim, open_batch_mixed_whir_stacked};
    use crate::whir::QUERY_GRINDING_BITS;
    use crate::whir_config::test_config_for;
    use primitives::test_rng::Rng;

    /// Pin the production 128-bit Johnson/OOD profile rather than the small-
    /// size test fallback.
    #[test]
    fn configs_johnson_profile_shape() {
        let pc = config_for_rate(16, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 16");
        assert_eq!(pc.initial_k, 6);
        assert!(pc.level_steps >= 1);
        assert_eq!(pc.ood_samples[0], 0);
        assert!(pc.ood_samples.iter().skip(1).all(|&s| s >= 1));
        assert!(pc.grinding_bits.iter().all(|&b| b == QUERY_GRINDING_BITS));
        // And log_n = 12 is below the production ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(config_for_rate(12, LOG_INV_RATE_0).is_err());
    }

    /// The parallel eq builder must be byte-identical to the serial one, and
    /// the seeded variant must equal the seed-scaled table, at sizes on both
    /// sides of the internal parallel level floor (2^12 halves, so n = 15
    /// exercises parallel levels; n = 6 stays fully serial).
    #[test]
    fn eq_table_parallel_and_seeded_match_serial() {
        let mut rng = Rng::new(21);
        for n in [0usize, 1, 6, 13, 15] {
            let point: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let serial = build_eq_table_ext(&point);
            assert_eq!(
                &*build_eq_table_ext_parallel(&point),
                &serial[..],
                "parallel mismatch at n={n}"
            );
            let g = rng.ext();
            // SAFETY: the fill writes every element before it reads any.
            let seeded = unsafe {
                primitives::filled_vec(1 << n, |seeded| {
                    primitives::multilinear::fill_eq_table(&point, g, seeded)
                })
            };
            let scaled: Vec<F192> = serial.iter().map(|&e| g * e).collect();
            assert_eq!(&*seeded, &scaled, "seeded mismatch at n={n}");
        }
    }

    /// At log_n = 18 the production profile's L0 has log_msg_cols = 12 and
    /// enough queries to trip the sparse transposed-NTT dispatch; the smaller
    /// shape stays on the dense path (cols < 12).
    #[test]
    fn induce_dispatch_follows_the_shape() {
        let pc = config_for_rate(18, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 18");
        assert!(
            induce_use_ntt_heuristic(18 - pc.initial_k, pc.log_inv_rates[0], pc.queries[0]),
            "shape must select the sparse transposed-NTT induce at L0"
        );
        let pc16 = config_for_rate(16, LOG_INV_RATE_0).unwrap();
        assert!(!induce_use_ntt_heuristic(
            16 - pc16.initial_k,
            pc16.log_inv_rates[0],
            pc16.queries[0]
        ));
    }

    /// Committing only the lanes that carry data must be indistinguishable from
    /// committing the whole `2^log_n` witness with an explicit zero tail: same
    /// root and byte-identical stream, the stored L0 rows differing only by the
    /// zero prefix the truncated proof drops.
    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        for (log_n, lanes) in [(13usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                witness[used..].fill(F64::ZERO);
                // The first and the last committed lane: nothing the weight touches lies past them.
                let lane_vars = log_n - pc.initial_k;
                let claims: Vec<_> = [0, used - lane_block]
                    .into_iter()
                    .map(|offset| StackClaim::Point {
                        offset,
                        low_point: rng.ext_vec(lane_vars),
                        value: rng.ext(),
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
                assert_eq!(
                    fs_trunc.stream, fs_full.stream,
                    "the protocol itself must not change at n_lanes = {n_lanes}"
                );

                // What the two proofs DO differ in, and the point of the exercise: the
                // truncated one stores each L0 row as the committed lanes alone, which is
                // exactly the full image with its leading padding zeros dropped.
                let leaf_words = 1usize << pc.initial_k;
                for (thin, full) in fs_trunc.merkle[0].leaf_data.iter().zip(&fs_full.merkle[0].leaf_data) {
                    assert_eq!(thin.len(), n_lanes);
                    assert_eq!(full.len(), leaf_words);
                    assert_eq!(thin[..], full[leaf_words - n_lanes..], "stored row is the image tail");
                    assert!(
                        full[..leaf_words - n_lanes].iter().all(|w| *w == F64::ZERO),
                        "the words the proof drops are the padding at n_lanes = {n_lanes}"
                    );
                }
            }
        }
    }

    /// The sparse transposed-NTT induce must be byte-identical to the dense
    /// LCH-expansion induce. Covers a domain
    /// of a single window (`log_msg_cols` of 10 or less), and the ones of 2 to 6
    /// layers above the windows of the second pass (`log_msg_cols` 12 to 16).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in [
            (12usize, 1usize, 5usize, 130usize),
            (12, 2, 5, 130),
            (6, 2, 3, 40),
            (7, 3, 3, 40),
            (14, 2, 5, 130),
            (13, 3, 4, 100),
            (16, 1, 5, 130),
        ] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let lanes = 1usize << lanes_log;
            // Distinct sorted query positions plus one aligned random row each.
            let mut qs: Vec<usize> = Vec::new();
            let mut seen = std::collections::HashSet::new();
            while qs.len() < n_queries {
                let q = (rng.next_u64() as usize) % block_len;
                if seen.insert(q) {
                    qs.push(q);
                }
            }
            qs.sort_unstable();
            let rows: Vec<F64> = (0..n_queries * lanes).map(|_| F64(rng.next_u64())).collect();
            let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
            let weights = powers(rng.ext(), n_queries);

            let sks_vks = eval_sk_at_vks(log_msg_cols);
            let dense = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &weights);
            let via_ntt =
                induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, &rows, &v_challenges, &qs, &weights);
            assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
            assert_eq!(&*dense.0, &*via_ntt.0, "basis_poly mismatch");
        }
    }

    /// Scalar `(u_0, u_2)` over adjacent pairs; a trailing odd element is ignored.
    fn msg_ref(f: &[F192], b: &[F192]) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for (p, q) in f.as_chunks::<2>().0.iter().zip(b.as_chunks::<2>().0.iter()) {
            u_0 += p[0] * q[0];
            u_2 += (p[0] + p[1]) * (q[0] + q[1]);
        }
        SumcheckMessage { u_0, u_2 }
    }

    /// The adjacent-pair round kernels agree with scalar references, at the sizes the rounds run.
    #[test]
    fn adjacent_round_kernels_match_scalar() {
        let mut rng = Rng::new(0xADD);
        let r = rng.ext();
        for log in [1usize, 2, 3, 4, 5, 6, 8, 12, 13, 14] {
            let n = 1usize << log;
            let (f, b) = (rng.ext_vec(n), rng.ext_vec(n));
            assert_eq!(round_msg_lsb(&f, &b), msg_ref(&f, &b), "round_msg_lsb, n={n}");

            let (msg, y) = round_msg_and_eval_lsb_ext(&f, &b);
            assert_eq!(msg, msg_ref(&f, &b), "eval message, n={n}");
            assert_eq!(
                y,
                f.iter().zip(&b).fold(F192::ZERO, |a, (&x, &y)| a + x * y),
                "eval, n={n}"
            );

            let fold =
                |x: &[F192]| -> Vec<F192> { x.as_chunks::<2>().0.iter().map(|p| fold_pair(p[0], p[1], r)).collect() };
            let (nb_ref, nf_ref) = (fold(&b), fold(&f));
            let (nf, nb, msg) = fold_and_msg_lsb(&f, &b, r);
            assert_eq!(
                (&nf, &nb, msg),
                (&nf_ref, &nb_ref, msg_ref(&nf_ref, &nb_ref)),
                "fold, n={n}"
            );
        }
    }

    /// `add_scaled` is `acc += s * v` at every length, remainders included.
    #[test]
    fn add_scaled_matches_scalar() {
        let mut rng = Rng::new(0x5CA1E);
        let s = rng.ext();
        for n in [1usize, 2, 7, 8, 9, 16, 18, 64, 4099] {
            let (acc, v) = (rng.ext_vec(n), rng.ext_vec(n));
            let mut got = acc.clone();
            add_scaled(&mut got, &v, s);
            let want: Vec<F192> = acc.iter().zip(&v).map(|(&a, &v)| a + s * v).collect();
            assert_eq!(got, want, "n={n}");
        }
    }
}
