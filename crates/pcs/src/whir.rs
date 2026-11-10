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
//! combiner of [CYWZ26, preprint] rather than multilinearly.
//!
//! Representations:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F128` (16 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F128::mul_base`] (2 PMULL) instead of a full E multiplication.
//!
//! Soundness note: [`WhirSecurityConfig`] analyzes the challenge field
//! `E`; the committed alphabet remains `K = GF(2^64)`.

use crate::merkle::{self, Hash};
use crate::ntt::{AdditiveNttF64, Codeword, Keep};
use crate::stack_open::Terms;
use fiat_shamir::merkle::MerklePath;
use fiat_shamir::transcript::ProverState;
use primitives::field::{
    Acc8, F64, F128, F128Unreduced, F128x8, fold_pairs8_ext, msg_lone8_ext, msg_terms8_ext, powers,
};
use primitives::multilinear::{eq_table, interp};

use super::whir_config::{BATCH_GRINDING_BITS, FOLD_GRINDING_BITS};
pub use super::whir_config::{
    INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, LevelShapes, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE, ProverConfig,
    QUERY_GRINDING_BITS, SECURITY_BITS, WhirSecurityConfig, validate_log_inv_rate,
};
#[cfg(test)]
pub use super::whir_config::{default_config, udr_queries};

pub use crate::whir_induce::*;
use crate::whir_lanes;
use crate::whir_ntt_ext::*;

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F128]) -> F128 {
    assert_eq!(witness.len(), b.len());
    if witness.len() < PAR_THRESHOLD {
        return witness.iter().zip(b.iter()).map(|(&w, &e)| e.mul_base(w)).sum();
    }
    parallel::map_reduce(
        witness.len(),
        || F128::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive the shared prover/verifier config for a K-witness of `2^log_n` F64
/// elements at L0 inverse-rate logarithm `log_inv_rate`, using the production
/// Production Johnson/OOD profile at `m = log_n + LOG_PACKING`.
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
/// itself is not stored; the caller retains it for opening, and an opening of a
/// codeword the encode did not keep recomputes the rows a query reads from it.
pub struct ProverData {
    ntt: AdditiveNttF64,
    codeword: Codeword,
    /// Words per codeword row: the committed lanes, with zero lanes in front up to the vector width.
    row_words: usize,
    pub(crate) merkle_tree: merkle::CutTree,
}

/// The largest L0 codeword the commit keeps where [`primitives::REBUILD_OVER_STORE`], in bytes.
///
/// - Up to it, memory is not the limit: the commit keeps the codeword before its deep layers, which saves the
///   opening a rebuild from the stack and the encode a second stage fill.
/// - Above it, the codeword dominates the peak: when one gathered pass covers the layers before the deep pass,
///   the commit keeps none and encodes half of the cosets at a time; otherwise it keeps them as below.
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
/// state every leaf shares. At most the image's tail, the committed lanes,
/// rides the proof, the opening saying its width and the image's.
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
    let ntt = AdditiveNttF64::standard(k_code);
    let codeword =
        tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = row_words).in_scope(|| {
            let on_rows = |row, rows: &[F64]| tree.absorb(row, rows);
            let keep = if !primitives::REBUILD_OVER_STORE {
                Keep::Whole
            } else if n_positions * row_words * size_of::<F64>() > KEEP_CODEWORD_MAX_BYTES {
                Keep::Nothing
            } else {
                Keep::BeforeDeep
            };
            ntt.encode_lane_major(message, n_lanes, row_words, log_inv_rate, keep, &on_rows)
        });
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = merkle_tree.root();

    (
        Commitment { root },
        ProverData {
            ntt,
            codeword,
            row_words,
            merkle_tree,
        },
    )
}

/// Codeword + Merkle tree for one deeper WHIR commitment level: a row is one position across the
/// `num_interleaved` lanes, one Merkle leaf of `num_interleaved * 16` bytes.
///
/// A codeword kept before its deep layers has them finished on the rows a query opens.
pub(crate) struct LigeroWitness {
    ntt: AdditiveNttF64,
    codeword: Codeword,
    pub tree: merkle::CutTree,
    pub block_len: usize,
    pub num_interleaved: usize,
}

impl LigeroWitness {
    /// The rows at the sorted `positions`, back to back, each as the K words its Merkle leaf is hashed from.
    fn opened_words(&self, positions: &[usize]) -> Vec<F64> {
        self.ntt.rows(&self.codeword, &[], positions)
    }

    /// The rows at `queries`, in order and back to back, and their paths.
    fn open(&self, queries: &[usize]) -> (Vec<F128>, Vec<MerklePath>) {
        let group = self.tree.group_positions(queries);
        let group_rows = self.opened_words(&group);
        let row_words = 2 * self.num_interleaved;
        let row = |q| fetched_row(&group, &group_rows, row_words, q);
        let mut rows = Vec::with_capacity(queries.len() * self.num_interleaved);
        rows.extend(
            queries
                .iter()
                .flat_map(|&q| row(q).as_chunks::<2>().0.iter().map(|w| F128::new(w[0].0, w[1].0))),
        );
        let paths = self.tree.open(queries, row_words, row_words, &group_rows, row);
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

    // One leaf per row, its F128s as K words: hashed as the encode finishes each block.
    let row_words = 2 * num_interleaved;
    let builder = merkle::MerkleBuilder::new(block_len, row_words, row_words);
    let codeword = tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| {
        let on_rows = |row, rows: &[F64]| builder.absorb(row, rows);
        let defer_deep = primitives::REBUILD_OVER_STORE;
        ntt.encode_interleaved_with(words(poly), row_words, log_inv_rate, defer_deep, &on_rows)
    });
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        ntt,
        codeword,
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

/// `out[j] = interp(x[2j], x[2j + 1], r)`.
#[inline]
fn fold_adjacent(out: &mut [F128], x: &[F128], r: F128) {
    let (o8, o_r) = out.as_chunks_mut::<8>();
    let (x16, x_r) = x.as_chunks::<16>();
    for (d, c) in o8.iter_mut().zip(x16) {
        let (even, odd) = deinterleave(c);
        *d = fold_pairs8_ext(&even, &odd, r);
    }
    for (d, p) in o_r.iter_mut().zip(x_r.as_chunks::<2>().0.iter()) {
        *d = interp(p[0], p[1], r);
    }
}

/// The even and the odd elements of sixteen consecutive ones.
#[inline]
fn deinterleave(x: &[F128; 16]) -> ([F128; 8], [F128; 8]) {
    let [lo, hi] = x.as_chunks::<8>().0 else { unreachable!() };
    let (even, odd) = F128x8::even_odd(F128x8::from_array(lo), F128x8::from_array(hi));
    (even.to_array(), odd.to_array())
}

/// `(sum f0*b0, sum (f0+f1)*(b0+b1))` over the adjacent pairs `(f[2j], f[2j + 1])`, unreduced, plus,
/// when `ODD`, `sum f1*b1` over the same pairs (the other half of the inner product `sum f*b` once
/// `u_0 = sum f0*b0` is added). A trailing odd element contributes nothing.
#[inline]
pub(crate) fn adjacent_dots<const ODD: bool>(f: &[F128], b: &[F128]) -> (Acc8, Acc8, Acc8) {
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
    let (mut r_0, mut r_2, mut r_odd) = (F128Unreduced::ZERO, F128Unreduced::ZERO, F128Unreduced::ZERO);
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

/// The round message of `f` against `b`, and with `EVAL` their inner product: for an OOD basis
/// `b = eq(z, ·)`, the claimed MLE evaluation.
fn round_msg_lsb<const EVAL: bool>(f: &[F128], b: &[F128]) -> (SumcheckMessage, F128) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    // `ROUND_CHUNK` is even, so no pair straddles two tasks.
    let dots = |c: usize| {
        let at = c * ROUND_CHUNK..(c * ROUND_CHUNK + ROUND_CHUNK).min(n);
        adjacent_dots::<EVAL>(&f[at.clone()], &b[at])
    };
    let add = |(mut a0, mut a2, mut ao): (Acc8, Acc8, Acc8), (c0, c2, co): (Acc8, Acc8, Acc8)| {
        a0 ^= c0;
        a2 ^= c2;
        ao ^= co;
        (a0, a2, ao)
    };
    let (n_tasks, zero) = (n.div_ceil(ROUND_CHUNK), (Acc8::ZERO, Acc8::ZERO, Acc8::ZERO));
    let (u_0, u_2, odd) = if n / 2 < PAR_THRESHOLD {
        (0..n_tasks).map(dots).fold(zero, add)
    } else {
        parallel::map_reduce(n_tasks, || zero, dots, add)
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

/// Fold outputs of at least this many elements (8 MiB) take streaming stores.
///
/// An output this large is evicted from a worker's share of the L3 before the next round reads it, so an ordinary
/// store only adds the line fetch.
const STREAM_FOLD_MIN: usize = 1 << 19;

/// Fused fold + next-round message: the witness and the basis fold, and the
/// next-round message is built over the freshly folded values in the same pass.
fn fold_and_msg_lsb(f: &[F128], b: &[F128], r: F128) -> (Vec<F128>, Vec<F128>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    // `half` is a power of two and so are `ROUND_CHUNK` and `FOLD_STAGE`: every window has even
    // length and starts at an even index, so no message pair straddles one.
    let stream = half >= STREAM_FOLD_MIN;
    let task = |ci: usize, fc: &mut [F128], bc: &mut [F128]| {
        let base = ci * ROUND_CHUNK;
        let len = fc.len();
        let mut acc = (Acc8::ZERO, Acc8::ZERO);
        let fold = |fo: &mut [F128], bo: &mut [F128], at: std::ops::Range<usize>| {
            fold_adjacent(fo, &f[at.clone()], r);
            fold_adjacent(bo, &b[at], r);
            adjacent_dots::<false>(fo, bo)
        };
        let (mut sf, mut sb) = ([F128::ZERO; FOLD_STAGE], [F128::ZERO; FOLD_STAGE]);
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

/// Below this many items a pass runs on the calling thread: a dispatch costs more than it saves.
const PAR_THRESHOLD: usize = 4096;

/// Elements per task wherever a round is chunked.
const ROUND_CHUNK: usize = 2048;

/// Sum the per-task `(u_0, u_2)` accumulators of `task(i, ..)`, which fills chunk `i` of two output tables,
/// sequentially for the small instances where dispatch costs more than the work. Unreduced accumulators
/// combine by XOR and `reduce` is linear, so both paths land on the same message.
#[inline]
fn accumulate_msg_chunks(
    f: &mut [F128],
    b: &mut [F128],
    chunk: usize,
    task: impl Fn(usize, &mut [F128], &mut [F128]) -> (Acc8, Acc8) + Sync,
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

/// `acc[j] += s * v[j]`, eight at a time where the multiplier is wide.
#[inline]
fn add_scaled(acc: &mut [F128], v: &[F128], s: F128) {
    let (a8, a_r) = acc.as_chunks_mut::<8>();
    let (v8, v_r) = v.as_chunks::<8>();
    let s8 = F128x8::splat(s);
    for (a, v) in a8.iter_mut().zip(v8) {
        *a = (F128x8::from_array(a) + s8 * F128x8::from_array(v)).to_array();
    }
    for (a, &v) in a_r.iter_mut().zip(v_r) {
        *a += s * v;
    }
}

// ===================================================================
// Affine fold rounds [CYWZ26, preprint]
// ===================================================================
//
// A round pairs the lanes `F` (folded bit 0) and `G` (folded bit 1) of a level. After `theta` it sends, with
// `H = F + theta G` and `W_i` the weight on the lanes with folded bit `i`,
//
//     [u0, v0, c0, v1, c1] = [<W_0, G>, <W_0, H>, <W_0, X H>, <W_1, H>, <W_1, X H>],
//
// and after `(gamma, alpha, beta)` the lanes become `P = G + alpha H + beta X H`, one coefficient longer, and the
// weight `W_0 + gamma (W_0 + W_1)`. The weight covers a lane's low `2^mu` coefficients only, and so do the inner
// products; the high coefficients the folds add matter only where the lane is evaluated.

/// The challenges of one fold round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FoldChallenges {
    pub(crate) theta: F128,
    pub(crate) gamma: F128,
    pub(crate) alpha: F128,
    pub(crate) beta: F128,
}

/// What a fold round sends: `[u0, v0, c0, v1, c1]`.
pub(crate) type FoldTable = [F128; 5];

impl FoldChallenges {
    /// The claim after the round, from the claim before it and the round's table: `u1 = claim + v0 + theta u0`.
    pub(crate) fn next_claim(&self, claim: F128, table: &FoldTable) -> F128 {
        let [u0, v0, c0, v1, c1] = *table;
        let u1 = claim + v0 + self.theta * u0;
        (F128::ONE + self.gamma) * (u0 + self.alpha * v0 + self.beta * c0)
            + self.gamma * (u1 + self.alpha * v1 + self.beta * c1)
    }

    /// `G + (alpha + beta x)(F + theta G)`: the folded lane at the domain point `x`, from the two it folds.
    #[inline]
    pub(crate) fn fold_at(&self, f: F128, g: F128, x: F64) -> F128 {
        g + (self.alpha + self.beta.mul_base(x)) * (f + self.theta * g)
    }
}

/// One fold round's transcript: `theta`, the table the prover builds from it, then `(gamma, alpha, beta)`, each
/// sample after its grind.
fn fold_round(ps: &mut ProverState, table: impl FnOnce(F128) -> FoldTable) -> (FoldChallenges, FoldTable) {
    ps.grind(FOLD_GRINDING_BITS);
    let theta = ps.sample();
    let t = table(theta);
    ps.add_scalars(&t);
    ps.grind(FOLD_GRINDING_BITS);
    let (gamma, alpha, beta) = (ps.sample(), ps.sample(), ps.sample());
    (
        FoldChallenges {
            theta,
            gamma,
            alpha,
            beta,
        },
        t,
    )
}

/// An opened row's lanes, in fold order, folded by the level's rounds at the row's domain point `x`.
pub(crate) fn fold_row(row: impl IntoIterator<Item = F128>, rounds: &[FoldChallenges], x: F64) -> F128 {
    let mut vals: Vec<F128> = row.into_iter().collect();
    assert_eq!(vals.len(), 1 << rounds.len(), "a row holds one value per lane");
    for ch in rounds {
        vals = vals
            .as_chunks::<2>()
            .0
            .iter()
            .map(|&[f, g]| ch.fold_at(f, g, x))
            .collect();
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

/// Elements per task of a dense fold round.
const DENSE_CHUNK: usize = 1 << 12;

impl Dense {
    /// Columns per task.
    fn cols_per_task(&self) -> usize {
        (DENSE_CHUNK / self.stride).max(1)
    }

    /// `H = F + theta G` over every column, and the round's table.
    pub(crate) fn table(&self, theta: F128) -> (FoldTable, Vec<F128>) {
        let (s, pairs) = (self.stride, self.stride / 2);
        assert!(s >= 2 && s.is_power_of_two());
        let (f, w) = (&self.f, &self.w);
        let (n_cols, low) = (f.len() / s, w.len() / s);
        // SAFETY: the fill writes every element before it reads any.
        let h = unsafe {
            primitives::filled_vec(n_cols * pairs, |h| {
                parallel::chunks_mut(h, DENSE_CHUNK, |i, out| {
                    let at = 2 * i * DENSE_CHUNK..2 * (i * DENSE_CHUNK + out.len());
                    for (o, p) in out.iter_mut().zip(f[at].as_chunks::<2>().0) {
                        *o = p[0] + theta * p[1];
                    }
                })
            })
        };
        let per = self.cols_per_task();
        let sums = parallel::map_reduce(
            low.div_ceil(per),
            || [F128Unreduced::ZERO; 5],
            |t| {
                let cols = t * per..((t + 1) * per).min(low);
                let mut xh = vec![F128::ZERO; cols.len() * pairs];
                crate::xmul::mul_x(&h, pairs, cols.start, &mut xh);
                let mut acc = [F128Unreduced::ZERO; 5];
                for (i, xh) in xh.chunks_exact(pairs).enumerate() {
                    let c = cols.start + i;
                    let (f, w, h) = (&f[c * s..][..s], &w[c * s..][..s], &h[c * pairs..][..pairs]);
                    for m in 0..pairs {
                        let (w0, w1, g, h, xh) = (w[2 * m], w[2 * m + 1], f[2 * m + 1], h[m], xh[m]);
                        acc[0] ^= w0.mul_unreduced(g);
                        acc[1] ^= w0.mul_unreduced(h);
                        acc[2] ^= w0.mul_unreduced(xh);
                        acc[3] ^= w1.mul_unreduced(h);
                        acc[4] ^= w1.mul_unreduced(xh);
                    }
                }
                acc
            },
            |mut a, b| {
                a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b);
                a
            },
        );
        (sums.map(F128Unreduced::reduce), h)
    }

    /// The round's fold, given its `H`: lanes `P = G + alpha H + beta X H`, one column longer, and the weight by `gamma`.
    pub(crate) fn fold(&mut self, h: &[F128], ch: &FoldChallenges) {
        let (s, pairs) = (self.stride, self.stride / 2);
        let n_cols = self.f.len() / s;
        let per = self.cols_per_task();
        let FoldChallenges { gamma, alpha, beta, .. } = *ch;
        let f = &self.f;
        // SAFETY: the fill writes every element before it reads any.
        let next = unsafe {
            primitives::filled_vec((n_cols + 1) * pairs, |out| {
                parallel::chunks_mut(out, per * pairs, |t, out| {
                    let first = t * per;
                    crate::xmul::mul_x(h, pairs, first, out);
                    for (i, out) in out.chunks_exact_mut(pairs).enumerate() {
                        let c = first + i;
                        if c == n_cols {
                            out.iter_mut().for_each(|o| *o = beta * *o);
                            continue;
                        }
                        let (f, h) = (&f[c * s..][..s], &h[c * pairs..][..pairs]);
                        for (m, o) in out.iter_mut().enumerate() {
                            *o = f[2 * m + 1] + alpha * h[m] + beta * *o;
                        }
                    }
                })
            })
        };
        let w = &self.w;
        // SAFETY: the fill writes every element before it reads any.
        let next_w = unsafe {
            primitives::filled_vec(w.len() / 2, |out| {
                parallel::chunks_mut(out, ROUND_CHUNK, |i, out| {
                    let at = 2 * i * ROUND_CHUNK..2 * (i * ROUND_CHUNK + out.len());
                    fold_adjacent(out, &w[at], gamma);
                })
            })
        };
        (self.f, self.w, self.stride) = (next, next_w, pairs);
    }
}

/// The weight the opening starts from, as terms: the table `A`, one row of `n_terms` per lane, and the
/// terms themselves, which project lanes onto them and lift a row of `A` over a lane.
pub(crate) struct InitialBasis {
    pub(crate) a: Vec<F128>,
    pub(crate) n_terms: usize,
    pub(crate) terms: Terms,
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

/// The row at position `q` out of `rows`, `row_words` each, back to back, which hold the sorted `group` positions.
fn fetched_row<'a>(group: &[usize], rows: &'a [F64], row_words: usize, q: usize) -> &'a [F64] {
    let k = group.binary_search(&q).expect("a fetched row");
    &rows[k * row_words..][..row_words]
}

/// One level's claims batched into the running one with powers of the level's challenge `lambda`, the running claim
/// keeping `lambda^0 = 1`: claim `tau` (counting from 1) adds `lambda^tau` times its weight and its value.
fn glue(w: &mut [F128], claim: &mut F128, pending: Vec<(Vec<F128>, F128)>, lambda: F128) {
    let scalars = &powers(lambda, pending.len() + 1)[1..];
    for ((b_new, value), &scalar) in pending.iter().zip(scalars) {
        assert_eq!(b_new.len(), w.len());
        *claim += scalar * *value;
    }
    let chunk = parallel::recommended_chunk_size(w.len());
    parallel::chunks_mut(w, chunk, |i, acc| {
        let at = i * chunk..i * chunk + acc.len();
        for ((b_new, _), &scalar) in pending.iter().zip(scalars) {
            add_scaled(acc, &b_new[at.clone()], scalar);
        }
    });
}

/// The tail sumcheck on `<w, f> = claim` over the low variables first, each round's message sent before its
/// challenge. Returns the claim it ends on, with `f` and `w` folded to one value each.
fn tail_sumcheck(ps: &mut ProverState, mut f: Vec<F128>, mut w: Vec<F128>, mut claim: F128) -> (F128, F128, F128) {
    let rounds = f.len().ilog2();
    let (mut msg, _) = round_msg_lsb::<false>(&f, &w);
    for j in 0..rounds {
        let _span = tracing::info_span!("Tail round", round = j).entered();
        send_msg(ps, msg);
        let r = ps.sample();
        claim = RoundQuad::from_msg(msg, claim).eval(r);
        if f.len() > 2 {
            (f, w, msg) = fold_and_msg_lsb(&f, &w, r);
        } else {
            (f, w) = (vec![interp(f[0], f[1], r)], vec![interp(w[0], w[1], r)]);
        }
    }
    (claim, f[0], w[0])
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is owned: where the L0 open recomputes the codeword rows it reads, it keeps it until then.
/// Otherwise round 1 reads it last, and the large committed stack is gone before the level-1 commit allocates.
///
/// `witness` may be shorter than `2^log_n`: it is a whole number of lane blocks, zero past them. The level-0 rounds
/// project only those, while `b_initial` keeps the weight over every lane.
///
/// Every level folds its lanes with [`FoldChallenges`], commits the low part of the folded lane (the next level's
/// message) and sends its high part, binds the next level with OOD samples, then opens its own oracle at its
/// queries, whose folded values (corrected by the high part) and column weights are glued into the running claim.
/// The final level sends its folded lane whole and closes with a sumcheck over its low part.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one
/// phase per level. The caller has already bound the initial commitment and target.
pub(crate) fn recursive_prover_with_prepared_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: Vec<F64>,
    b_initial: InitialBasis,
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
    // L0 takes no OOD points here: the caller's OOD sample, right after the root, binds it.
    assert_eq!(config.ood_samples.first().copied().unwrap_or(0), 0);

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
    assert_eq!(prover_data.codeword.plan().words(), block_len_0 * prover_data.row_words);
    assert!((n_lanes..=num_interleaved_0).contains(&prover_data.row_words));

    // Nothing is absorbed on entry. The commitment was bound by the `add_root` that
    // transmitted it, and the target is `sum_i lambda^i * claim_i` over claim values bound by their
    // own reads, with lambda drawn from the state: the state already determines both. Every caller
    // must therefore have transmitted its root before opening against it, which is what makes the
    // fold challenges depend on the commitment.
    //
    // The prover's messages never depend on the running claim; it is tracked only to check, in tests, that the
    // rounds keep it.
    let mut claim = target;

    // Level 0: its rounds run on the weight's terms.
    let mut lanes = whir_lanes::LaneRounds::new(witness, b_initial, lane_block);
    let mut rounds = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        let _span = tracing::info_span!("Fold round", level = 0, round = j).entered();
        let (ch, table) = fold_round(ps, |theta| lanes.table(theta));
        claim = ch.next_claim(claim, &table);
        lanes.fold(&ch);
        rounds.push(ch);
    }
    // A rebuilding L0 open recomputes its rows from the stack, so that lives until then. Otherwise it goes now.
    let (mut p, mut w, mut stack) = lanes.finish(matches!(prover_data.codeword, Codeword::Nothing(..)));
    let mut prover_data = Some(prover_data);
    let mut wtns_prev: Option<LigeroWitness> = None;

    for level in 0..=r {
        if level > 0 {
            // The level's message is the previous one's low part, its lanes the low `level_ks[level - 1]` variables.
            let mut dense = Dense {
                f: p,
                w,
                stride: 1 << config.level_ks[level - 1],
            };
            rounds.clear();
            for j in 0..config.level_ks[level - 1] {
                let _span = tracing::info_span!("Fold round", level, round = j).entered();
                let mut h = Vec::new();
                let (ch, table) = fold_round(ps, |theta| {
                    let (table, hh) = dense.table(theta);
                    h = hh;
                    table
                });
                claim = ch.next_claim(claim, &table);
                dense.fold(&h, &ch);
                rounds.push(ch);
            }
            (p, w) = (dense.f, dense.w);
        }
        let mu = w.len().ilog2() as usize;
        assert_eq!(p.len(), (1 << mu) + rounds.len());
        let block_len = wtns_prev.as_ref().map_or(block_len_0, |wt| wt.block_len);

        if level == r {
            let _span = tracing::info_span!("Final level").entered();
            ps.add_scalars(&p);
            ps.grind(config.grinding_bits[level]);
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

        // Bind the next level's list before drawing this level's queries: the OOD points, one verifier message with
        // no grind, then their values, all in one pass. The claims stay pending until the level's batching challenge.
        let n_ood = config.ood_samples[level + 1];
        let eqs: Vec<Vec<F128>> = (0..n_ood).map(|_| eq_table(&ps.sample_vec(mu))).collect();
        let ys = parallel::map_reduce(
            p.len().div_ceil(ROUND_CHUNK),
            || vec![F128::ZERO; n_ood],
            |t| {
                let at = t * ROUND_CHUNK..((t + 1) * ROUND_CHUNK).min(p.len());
                eqs.iter()
                    .map(|eq| p[at.clone()].iter().zip(&eq[at.clone()]).map(|(&a, &b)| a * b).sum())
                    .collect()
            },
            |a, b| a.iter().zip(&b).map(|(&a, &b)| a + b).collect(),
        );
        ps.add_scalars(&ys);
        let mut pending: Vec<(Vec<F128>, F128)> = eqs.into_iter().zip(ys).collect();

        ps.grind(config.grinding_bits[level]);
        let queries = sample_queries_ordered(ps, block_len, config.queries[level]);
        ps.grind(BATCH_GRINDING_BITS);
        let lambda = ps.sample();
        let weights = powers(lambda, queries.len());

        // The rows at the queries, lanes in fold order.
        let span = tracing::info_span!("Open", level).entered();
        let rows: Vec<F128> = match prover_data.take() {
            Some(prover_data) => {
                let l0_tree = &prover_data.merkle_tree;
                // The tree keeps no leaves: the rows of whole leaf groups are read back and rehashed.
                let row_words = prover_data.row_words;
                let group = l0_tree.group_positions(&queries);
                let group_rows = prover_data.ntt.rows(&prover_data.codeword, &stack, &group);
                let image = |q| &fetched_row(&group, &group_rows, row_words, q)[row_words - n_lanes..];
                // Lane `t` of the codeword is stack block `n_lanes-1-t`: reversing the image puts block `b` at index
                // `b`, and the absent lanes' zeros at the end.
                let mut rows = Vec::with_capacity(queries.len() * num_interleaved_0);
                for &q in &queries {
                    let zeros = std::iter::repeat_n(F128::ZERO, num_interleaved_0 - n_lanes);
                    rows.extend(image(q).iter().rev().map(|&k| F128::from(k)).chain(zeros));
                }
                ps.hint_merkle(l0_tree.open(&queries, row_words, num_interleaved_0, &group_rows, image));
                // Nothing reads the L0 codeword, its stack or its tree again.
                drop((prover_data, std::mem::take(&mut stack)));
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
        let basis = induce_basis_auto(mu, block_len.ilog2() as usize - mu, &queries, &weights);
        drop(span);
        pending.push((basis, enforced));
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
    use crate::whir::QUERY_GRINDING_BITS;
    use crate::whir_config::test_config_for;
    use primitives::test_rng::Rng;

    /// Pin the production Johnson/OOD profile rather than the small-
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
    /// root and the same proof. The prover's own checks run on the way: every
    /// query value is the folded lane's, and every level keeps the running claim.
    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        for (log_n, lanes) in [(13usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = test_config_for(log_n);
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

    /// The sparse transposed-NTT induce must be byte-identical to the dense
    /// LCH-expansion induce. Covers a domain
    /// of a single window (`log_msg_cols` of 10 or less), and the ones of 2 to 6
    /// layers above the windows of the second pass (`log_msg_cols` 12 to 16).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, n_queries) in [
            (12usize, 1usize, 130usize),
            (12, 2, 130),
            (6, 2, 40),
            (7, 3, 40),
            (14, 2, 130),
            (13, 3, 100),
            (16, 1, 130),
        ] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            // Distinct sorted query positions.
            let mut qs: Vec<usize> = Vec::new();
            let mut seen = std::collections::HashSet::new();
            while qs.len() < n_queries {
                let q = (rng.next_u64() as usize) % block_len;
                if seen.insert(q) {
                    qs.push(q);
                }
            }
            qs.sort_unstable();
            let weights = powers(rng.ext(), n_queries);
            let dense = induce_basis(log_msg_cols, &eval_sk_at_vks(log_msg_cols), &qs, &weights);
            let via_ntt = induce_basis_via_ntt(log_msg_cols, log_inv_rate, &qs, &weights);
            assert_eq!(dense, via_ntt, "basis_poly mismatch at log_msg_cols = {log_msg_cols}");
        }
    }

    fn challenges(rng: &mut Rng) -> FoldChallenges {
        FoldChallenges {
            theta: rng.ext(),
            gamma: rng.ext(),
            alpha: rng.ext(),
            beta: rng.ext(),
        }
    }

    /// A dense round's table is the five inner products over the low columns, written out lane by lane, and its fold
    /// is `G + alpha H + beta X H` over every column and the weight's interpolation by `gamma`.
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
            let mut want = [F128::ZERO; 5];
            let mut folded = Vec::new();
            for m in 0..s / 2 {
                let (f, g) = (lane(&dense.f, 2 * m, n_cols), lane(&dense.f, 2 * m + 1, n_cols));
                let (w0, w1) = (lane(&dense.w, 2 * m, low), lane(&dense.w, 2 * m + 1, low));
                let h: Vec<F128> = f.iter().zip(&g).map(|(&f, &g)| f + ch.theta * g).collect();
                let mut xh = vec![F128::ZERO; n_cols + 1];
                crate::xmul::mul_x(&h, 1, 0, &mut xh);
                let ip = |w: &[F128], v: &[F128]| w.iter().zip(v).map(|(&a, &b)| a * b).sum::<F128>();
                for (s, v) in want
                    .iter_mut()
                    .zip([ip(&w0, &g), ip(&w0, &h), ip(&w0, &xh), ip(&w1, &h), ip(&w1, &xh)])
                {
                    *s += v;
                }
                let at = |v: &[F128], c: usize| v.get(c).copied().unwrap_or(F128::ZERO);
                folded.push(
                    (0..=n_cols)
                        .map(|c| at(&g, c) + ch.alpha * at(&h, c) + ch.beta * xh[c])
                        .collect::<Vec<_>>(),
                );
            }
            let w_want: Vec<F128> = dense
                .w
                .as_chunks::<2>()
                .0
                .iter()
                .map(|&[a, b]| interp(a, b, ch.gamma))
                .collect();
            let (table, h) = dense.table(ch.theta);
            assert_eq!(table, want, "table, stride {s}, mu {mu}, high {high}");
            dense.fold(&h, &ch);
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
                let (_, h) = dense.table(ch.theta);
                dense.fold(&h, ch);
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

    /// Scalar `(u_0, u_2)` over adjacent pairs; a trailing odd element is ignored.
    fn msg_ref(f: &[F128], b: &[F128]) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F128::ZERO, F128::ZERO);
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
            assert_eq!(
                round_msg_lsb::<false>(&f, &b).0,
                msg_ref(&f, &b),
                "round_msg_lsb, n={n}"
            );

            let (msg, y) = round_msg_lsb::<true>(&f, &b);
            assert_eq!(msg, msg_ref(&f, &b), "eval message, n={n}");
            assert_eq!(y, f.iter().zip(&b).map(|(&x, &y)| x * y).sum(), "eval, n={n}");

            let fold =
                |x: &[F128]| -> Vec<F128> { x.as_chunks::<2>().0.iter().map(|p| interp(p[0], p[1], r)).collect() };
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
            let want: Vec<F128> = acc.iter().zip(&v).map(|(&a, &v)| a + s * v).collect();
            assert_eq!(got, want, "n={n}");
        }
    }
}
