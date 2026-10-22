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
use crate::ntt::AdditiveNttF64;
use fiat_shamir::merkle::PrunedMerklePaths;
use fiat_shamir::transcript::ProverState;
use primitives::{
    field::{F64, F192, F192Unreduced, powers},
    stream::Stream,
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
    const PAR_THRESHOLD: usize = 4096;
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
pub struct ProverData {
    pub codeword: Vec<F64>,
    pub merkle_tree: Vec<Hash>,
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
/// state every leaf shares. Only the image's tail, the committed lanes,
/// rides the proof, so a verifier derives `n_lanes` from the announced layout to
/// read a row and supplies the prefix itself.
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
    let codeword_len = n_positions * n_lanes;

    // SAFETY: every codeword element is written before it is read.
    // `transpose_lane_major` covers every word of the message region (its tiles are
    // asserted to), and `encode_interleaved_in_place` writes every other replica from
    // it before transforming that region in place.
    let mut codeword = unsafe { primitives::uninit_vec::<F64>(codeword_len) };

    // Leaves are hashed as the encode finishes each block of rows.
    let tree = merkle::MerkleBuilder::new(n_positions, n_lanes, 1usize << log_batch_size);
    tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes).in_scope(|| {
        crate::ntt::transpose_lane_major(&mut codeword[..message.len()], message, n_lanes, log_rows);
        let ntt = AdditiveNttF64::standard(k_code);
        ntt.encode_interleaved_in_place_with(&mut codeword, n_lanes, log_inv_rate, &|row, rows| {
            tree.absorb(row, rows)
        });
    });
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");

    (Commitment { root }, ProverData { codeword, merkle_tree })
}

/// Codeword + Merkle tree for one deeper WHIR commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitness {
    pub mat: Vec<F192>,
    pub tree: Vec<Hash>,
    pub block_len: usize,
    pub num_interleaved: usize,
}

impl LigeroWitness {
    #[inline]
    pub fn row(&self, pos: usize) -> &[F192] {
        let start = pos * self.num_interleaved;
        &self.mat[start..start + self.num_interleaved]
    }

    #[inline]
    pub fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
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
    ntt: &AdditiveNttF64,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    assert!(log_block_len <= ntt.log_domain_size());

    let codeword_len = block_len * num_interleaved;
    // The encode builds the replicas itself, so the codeword starts uninitialized.
    //
    // SAFETY: the encode writes every matrix element before reading it.
    let mut mat = unsafe { primitives::uninit_vec::<F192>(codeword_len) };

    // One leaf per row, its F192s as K words: hashed as the encode finishes each block.
    let row_words = 3 * num_interleaved;
    let builder = merkle::MerkleBuilder::new(block_len, row_words, row_words);
    tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| {
        encode_interleaved_ext(ntt, &mut mat, poly, num_interleaved, log_inv_rate, &|row, rows| {
            builder.absorb(row, rows)
        })
    });
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        mat,
        tree,
        block_len,
        num_interleaved,
    }
}

// ===================================================================
// Stateful sumcheck over E with a two-phase (Base then Ext) witness
// ===================================================================
//
// Each round sends (u_0, u_2) of the quadratic
// q(X) = u_0 + u_1 X + u_2 X^2 with q(0) + q(1) = T_r, verifier derives
// u_1 = T_r + u_2 (char 2), round eval q(r) = u_0 + r T_r + (r + r^2) u_2.
//
// Round 0 pairs the K-witness with the E-basis via `mul_base`; the first fold
// lifts the witness into E and all later rounds are pure E.

/// (u_0, u_2) per round in E.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    u_0: F192,
    u_2: F192,
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

/// Sumcheck witness element: `F64` before the first fold (each product against
/// the E basis is a mixed `mul_base`, 2 PMULL), `F192` after it (full E
/// products, 3 PMULL). The associated accumulator is the matching
/// deferred-reduction type.
trait RoundWitness: Copy + Sync + std::ops::Add<Output = Self> {
    type Acc: Copy + Send + core::ops::BitXorAssign;
    const ZERO_ACC: Self::Acc;
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc;
    fn reduce(acc: Self::Acc) -> F192;
    /// Characteristic-two interpolation `x0·(1+r) + x1·r = x0 + r·(x0+x1)`,
    /// lifting the witness into E. One product rather than two, bit-identical
    /// to the two-product form and still just one reduction.
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192;
    /// [`Self::fold_pair`] against an absent partner: the lane rounds pair the
    /// last committed lane with the stacked witness's zero padding, so the
    /// interpolation collapses to `x0·(1+r)`.
    fn fold_lone(x0: Self, r: F192) -> F192;
}

impl RoundWitness for F64 {
    type Acc = F192Unreduced;
    const ZERO_ACC: Self::Acc = F192Unreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        b.mul_base_unreduced(self)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        F192::from(x0) + r.mul_base(x0 + x1)
    }
    #[inline]
    fn fold_lone(x0: Self, r: F192) -> F192 {
        F192::from(x0) + r.mul_base(x0)
    }
}

impl RoundWitness for F192 {
    type Acc = F192Unreduced;
    const ZERO_ACC: Self::Acc = F192Unreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        self.mul_unreduced(b)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        x0 + r * (x0 + x1)
    }
    #[inline]
    fn fold_lone(x0: Self, r: F192) -> F192 {
        x0 + r * x0
    }
}

/// Round message over a witness `f` and an E basis `b`. Mirror of
/// `whir::round_msg_lsb`.
///
/// Deferred reduction: XOR-accumulate the raw lane products (no reduction tail
/// per term) and reduce once per accumulator. Reduction commutes with XOR, so
/// the message is bit-identical to reducing every term.
fn round_msg_lsb<T: RoundWitness>(f: &[T], b: &[F192]) -> SumcheckMessage {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let half = n / 2;
    let term = |j: usize| -> (T::Acc, T::Acc) {
        let (f0, f1) = (f[2 * j], f[2 * j + 1]);
        let (b0, b1) = (b[2 * j], b[2 * j + 1]);
        (f0.mul_basis_unreduced(b0), (f0 + f1).mul_basis_unreduced(b0 + b1))
    };
    let (u_0, u_2) = accumulate_msg(half, half, T::ZERO_ACC, term);
    SumcheckMessage {
        u_0: T::reduce(u_0),
        u_2: T::reduce(u_2),
    }
}

/// Build the round message and the full inner product in one pass. For an OOD
/// basis `b = eq(z, ·)`, the inner product is the claimed MLE evaluation.
fn round_msg_and_eval_lsb_ext(f: &[F192], b: &[F192]) -> (SumcheckMessage, F192) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let term = |j: usize| {
        let f0 = f[2 * j];
        let f1 = f[2 * j + 1];
        let b0 = b[2 * j];
        let b1 = b[2 * j + 1];
        let e0 = f0 * b0;
        (e0, (f0 + f1) * (b0 + b1), e0 + f1 * b1)
    };
    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    let (u_0, u_2, y) = if half < PAR_THRESHOLD {
        (0..half)
            .map(term)
            .fold((F192::ZERO, F192::ZERO, F192::ZERO), |(a0, a2, ay), (b0, b2, by)| {
                (a0 + b0, a2 + b2, ay + by)
            })
    } else {
        parallel::map_reduce(
            half,
            || (F192::ZERO, F192::ZERO, F192::ZERO),
            term,
            |(a0, a2, ay), (b0, b2, by)| (a0 + b0, a2 + b2, ay + by),
        )
    };
    (SumcheckMessage { u_0, u_2 }, y)
}

/// Uninitialized output for an initial-sumcheck fold.
///
/// # Safety
/// Every element must be written before it is read, which every fold kernel
/// below does: one output slot per input pair.
#[inline]
unsafe fn fold_out_buf(n: usize) -> Vec<F192> {
    // SAFETY: forwarded to the caller's obligation, documented above.
    unsafe { primitives::uninit_vec(n) }
}

/// Unreduced `(u_0, u_2)` over the already-folded E buffers, pair by pair. A
/// trailing odd element contributes nothing, exactly as in the pre-fold
/// message: at the last round `half = 1` and the message is zero.
#[inline]
fn fold_msg_terms(nf: &[F192], nb: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let mut u_0 = F192Unreduced::ZERO;
    let mut u_2 = F192Unreduced::ZERO;
    let mut k = 0;
    while k + 1 < nf.len() {
        let f0 = nf[k];
        let f1 = nf[k + 1];
        let b0 = nb[k];
        let b1 = nb[k + 1];
        u_0 ^= f0.mul_unreduced(b0);
        u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
        k += 2;
    }
    (u_0, u_2)
}

/// Fused fold + next-round message: the witness folds into E, the basis folds
/// in E, and the next-round message is built over the freshly folded E values
/// in the same pass. Mirror of `whir::fold_and_msg_lsb`.
fn fold_and_msg_lsb<T: RoundWitness>(f: &[T], b: &[F192], r: F192) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    let fold_f = |j: usize| -> F192 { T::fold_pair(f[2 * j], f[2 * j + 1], r) };
    let fold_b = |j: usize| -> F192 { F192::fold_pair(b[2 * j], b[2 * j + 1], r) };
    const PAR_THRESHOLD: usize = 4096;
    if half < PAR_THRESHOLD {
        let mut nf = Vec::with_capacity(half);
        let mut nb = Vec::with_capacity(half);
        for j in 0..half {
            nf.push(fold_f(j));
            nb.push(fold_b(j));
        }
        let (u_0, u_2) = fold_msg_terms(&nf, &nb);
        return (
            nf,
            nb,
            SumcheckMessage {
                u_0: u_0.reduce(),
                u_2: u_2.reduce(),
            },
        );
    }

    // Parallel path: `half` is a power of two >= PAR_THRESHOLD and ROUND_CHUNK is a
    // power of two, so every chunk has even length and starts at an even
    // global index (message pairs never straddle a chunk boundary).
    // SAFETY (x2): every slot of `nf`/`nb` is written by the chunked loop below
    // (one output per input pair) before any is read.
    let mut nf = unsafe { fold_out_buf(half) };
    let mut nb = unsafe { fold_out_buf(half) };
    // The fold writes and the message accumulate share one pass per chunk, so
    // the freshly folded values are still in L1 when they are multiplied.
    let nf_base = parallel::SendPtr(nf.as_mut_ptr());
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());
    let (u_0, u_2) = parallel::map_reduce(
        half.div_ceil(ROUND_CHUNK),
        || (F192Unreduced::ZERO, F192Unreduced::ZERO),
        |ci| {
            let base = ci * ROUND_CHUNK;
            let len = ROUND_CHUNK.min(half - base);
            // SAFETY: distinct `ci` own disjoint in-bounds `ROUND_CHUNK`-windows of
            // `nf`/`nb`, and both buffers stay borrowed for the whole dispatch.
            let fc = unsafe { nf_base.slice(base, len) };
            let bc = unsafe { nb_base.slice(base, len) };
            for t in 0..len {
                let j = base + t;
                fc[t] = fold_f(j);
                bc[t] = fold_b(j);
            }
            fold_msg_terms(fc, bc)
        },
        |(mut a0, mut a2), (c0, c2)| {
            a0 ^= c0;
            a2 ^= c2;
            (a0, a2)
        },
    );
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
// padding. After them the buffer is one `H`-element block and every later round
// is the ordinary adjacent-pair fold.

/// Elements per task wherever a round is chunked: the fused adjacent-pair fold,
/// and the lane rounds, whose block is the whole L0 message divided by the
/// interleaving and so has to be fed to the pool from inside a block pair rather
/// than across them.
const ROUND_CHUNK: usize = 2048;

/// Sum the per-task `(u_0, u_2)` accumulators, sequentially for the small
/// instances where dispatch costs more than the work. Unreduced accumulators
/// combine by XOR and `reduce` is linear, so both paths land on the same message.
#[inline]
fn accumulate_msg<A: Copy + Send + core::ops::BitXorAssign>(
    n_tasks: usize,
    n_pairs: usize,
    zero: A,
    task: impl Fn(usize) -> (A, A) + Sync,
) -> (A, A) {
    const PAR_THRESHOLD: usize = 4096;
    if n_pairs < PAR_THRESHOLD {
        let mut u_0 = zero;
        let mut u_2 = zero;
        for t in 0..n_tasks {
            let (t0, t2) = task(t);
            u_0 ^= t0;
            u_2 ^= t2;
        }
        (u_0, u_2)
    } else {
        parallel::map_reduce(
            n_tasks,
            || (zero, zero),
            task,
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
fn msg_terms_pair<T: RoundWitness>(f0: &[T], f1: &[T], b0: &[F192], b1: &[F192]) -> (T::Acc, T::Acc) {
    let mut u_0 = T::ZERO_ACC;
    let mut u_2 = T::ZERO_ACC;
    for (((&x0, &x1), &y0), &y1) in f0.iter().zip(f1).zip(b0).zip(b1) {
        u_0 ^= x0.mul_basis_unreduced(y0);
        u_2 ^= (x0 + x1).mul_basis_unreduced(y0 + y1);
    }
    (u_0, u_2)
}

/// [`msg_terms_pair`] against an absent partner block. With `f1 = b1 = 0` both
/// `h(0)` and `h(inf)` collect the same `Σ f0·b0`, so this is NOT a no-op the way
/// a trailing odd element is in an adjacent-pair round.
#[inline]
fn msg_terms_lone<T: RoundWitness>(f0: &[T], b0: &[F192]) -> (T::Acc, T::Acc) {
    let mut u = T::ZERO_ACC;
    for (&x0, &y0) in f0.iter().zip(b0) {
        u ^= x0.mul_basis_unreduced(y0);
    }
    (u, u)
}

/// Round message for a lane round, over `f.len() / block` blocks.
fn round_msg_blocks<T: RoundWitness>(f: &[T], b: &[F192], block: usize) -> SumcheckMessage {
    // Real asserts, not debug ones: the crate is only ever built in release, and a
    // block count that truncates drops the trailing block from BOTH u_0 and u_2,
    // which is a well-formed but wrong round message rather than a panic.
    assert_eq!(b.len(), f.len());
    assert!(block > 0 && f.len().is_multiple_of(block));
    let n_blocks = f.len() / block;
    let per = block.div_ceil(ROUND_CHUNK);
    let task = |t: usize| -> (T::Acc, T::Acc) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let lo = 2 * i * block + x0;
        if 2 * i + 1 < n_blocks {
            let hi = lo + block;
            msg_terms_pair(&f[lo..lo + len], &f[hi..hi + len], &b[lo..lo + len], &b[hi..hi + len])
        } else {
            msg_terms_lone(&f[lo..lo + len], &b[lo..lo + len])
        }
    };
    let (u_0, u_2) = accumulate_msg(n_blocks.div_ceil(2) * per, f.len() / 2, T::ZERO_ACC, task);
    SumcheckMessage {
        u_0: T::reduce(u_0),
        u_2: T::reduce(u_2),
    }
}

pub(crate) const INITIAL_BASIS_CHUNK: usize = 256;

pub(crate) fn build_initial_basis(
    f: &[F64],
    block: usize,
    fill: impl Fn(usize, &mut [F192]) + Sync,
) -> (Vec<F192>, SumcheckMessage) {
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let n_blocks = f.len() / block;
    let per = block.div_ceil(INITIAL_BASIS_CHUNK);
    // SAFETY: each task fills and publishes its disjoint lane windows before returning.
    let mut basis = unsafe { primitives::uninit_vec::<F192>(f.len()) };
    let dst = parallel::SendPtr(basis.as_mut_ptr());
    let task = |t: usize| {
        let (pair, chunk) = (t / per, t % per);
        let offset = chunk * INITIAL_BASIS_CHUNK;
        let len = INITIAL_BASIS_CHUNK.min(block - offset);
        let lo = 2 * pair * block + offset;
        let mut b0 = [F192::ZERO; INITIAL_BASIS_CHUNK];
        let mut b1 = [F192::ZERO; INITIAL_BASIS_CHUNK];
        fill(lo, &mut b0[..len]);
        let stream = Stream::new();
        let message = if 2 * pair + 1 < n_blocks {
            let hi = lo + block;
            fill(hi, &mut b1[..len]);
            let message = msg_terms_pair(&f[lo..lo + len], &f[hi..hi + len], &b0[..len], &b1[..len]);
            // SAFETY: this task owns the high lane window, disjoint from every other task.
            unsafe { stream.copy(dst.slice(hi, len), &b1[..len]) };
            message
        } else {
            msg_terms_lone(&f[lo..lo + len], &b0[..len])
        };
        // SAFETY: this task owns the low lane window, disjoint from every other task.
        unsafe { stream.copy(dst.slice(lo, len), &b0[..len]) };
        message
    };
    let (u_0, u_2) = accumulate_msg(n_blocks.div_ceil(2) * per, f.len() / 2, F192Unreduced::ZERO, task);
    (
        basis,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Fused lane fold + next-round message. Mirror of [`fold_and_msg_lsb`] for the
/// block pairing: a task owns one output *pair* (so four input blocks), because
/// that is the smallest unit the next round's message is local to.
///
/// `last` says this is the final lane round, so the round after it pairs adjacent
/// elements of the single output block rather than another pair of blocks. Which
/// pairing comes next is what lets the message be built here, while the folded
/// values are still in L1.
fn fold_and_msg_blocks<T: RoundWitness>(
    f: &[T],
    b: &[F192],
    r: F192,
    block: usize,
    last: bool,
) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    assert_eq!(b.len(), f.len());
    assert!(block > 0 && f.len().is_multiple_of(block));
    let n_in = f.len() / block;
    let n_out = n_in.div_ceil(2);
    // Adjacent pairing next round is only possible once the lanes have collapsed
    // to a single block.
    assert!(!last || n_out == 1);

    // SAFETY (x2): the loop below writes every slot of both buffers, one output
    // element per input pair, before any is read.
    let mut nf = unsafe { fold_out_buf(n_out * block) };
    let mut nb = unsafe { fold_out_buf(n_out * block) };
    let nf_base = parallel::SendPtr(nf.as_mut_ptr());
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());

    let per = block.div_ceil(ROUND_CHUNK);
    // Fold into an L1-resident stage rather than straight into `nf`/`nb`. The
    // message reads the folded values back, and reading them here instead of out
    // of the destination is what lets the destination be published with
    // streaming stores: nothing else touches it until the next round, by which
    // time a buffer this size is long evicted, so the fetch an ordinary store
    // would make of every line it overwrites is pure waste.
    const STAGE: usize = 128;
    let fold_block = |stage: &mut [F192], stage_b: &mut [F192], out_blk: usize, x0: usize, stream: &Stream| {
        let len = stage.len();
        let src0 = 2 * out_blk * block + x0;
        // Sliced, not indexed: runs of one length let the bounds checks fall out
        // and the pair fold vectorise, as the adjacent-pair kernel's do.
        let (f_lo, b_lo) = (&f[src0..src0 + len], &b[src0..src0 + len]);
        if 2 * out_blk + 1 < n_in {
            let src1 = src0 + block;
            let (f_hi, b_hi) = (&f[src1..src1 + len], &b[src1..src1 + len]);
            for ((d, &x0), &x1) in stage.iter_mut().zip(f_lo).zip(f_hi) {
                *d = T::fold_pair(x0, x1, r);
            }
            for ((d, &y0), &y1) in stage_b.iter_mut().zip(b_lo).zip(b_hi) {
                *d = F192::fold_pair(y0, y1, r);
            }
        } else {
            for (d, &x0) in stage.iter_mut().zip(f_lo) {
                *d = T::fold_lone(x0, r);
            }
            for (d, &y0) in stage_b.iter_mut().zip(b_lo) {
                *d = F192::fold_lone(y0, r);
            }
        }
        // SAFETY: distinct (out_blk, x0) name disjoint in-bounds windows of `nf`
        // and `nb`, which stay borrowed for the whole dispatch.
        unsafe {
            stream.copy(nf_base.slice(out_blk * block + x0, len), stage);
            stream.copy(nb_base.slice(out_blk * block + x0, len), stage_b);
        }
    };

    let task = |t: usize| -> (F192Unreduced, F192Unreduced) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let stream = Stream::new();
        let mut stage = [[F192::ZERO; STAGE]; 4];
        let mut acc = (F192Unreduced::ZERO, F192Unreduced::ZERO);
        for s in (0..len).step_by(STAGE) {
            let n = STAGE.min(len - s);
            let [lo_f, lo_b, hi_f, hi_b] = &mut stage;
            fold_block(&mut lo_f[..n], &mut lo_b[..n], 2 * i, x0 + s, &stream);
            let (u_0, u_2) = if 2 * i + 1 < n_out {
                fold_block(&mut hi_f[..n], &mut hi_b[..n], 2 * i + 1, x0 + s, &stream);
                msg_terms_pair(&lo_f[..n], &hi_f[..n], &lo_b[..n], &hi_b[..n])
            } else if last {
                // `ROUND_CHUNK`, `STAGE` and `block` are powers of two, so every
                // slice has even length and starts even: no message pair
                // straddles one.
                fold_msg_terms(&lo_f[..n], &lo_b[..n])
            } else {
                msg_terms_lone(&lo_f[..n], &lo_b[..n])
            };
            acc.0 ^= u_0;
            acc.1 ^= u_2;
        }
        acc
    };
    let (u_0, u_2) = accumulate_msg(n_out.div_ceil(2) * per, f.len() / 2, F192Unreduced::ZERO, task);
    (
        nf,
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Two-phase witness: the committed K-message (borrowed from the caller, it
/// is only read until the first fold) before the first fold, an owned
/// E-vector afterwards.
enum Witness<'a> {
    Base(&'a [F64]),
    Ext(Vec<F192>),
}

/// Running sumcheck over the committed base witness and subsequent extension-field folds.
struct SumcheckProver<'a> {
    f: Witness<'a>,
    /// Single combined basis poly: `glue_pending(lambda)` folds each claim
    /// introduced since the last glue in as `combined_basis += lambda^tau *
    /// b_new`, `tau` counting from 1 (the running claim is `tau = 0`).
    combined_basis: Vec<F192>,
    /// The running claim and its quadratic; `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    quad: RoundQuad,
    round: usize,
    /// The level's claims, in Protocol 1 step 1 order: the OOD claims, then the
    /// query batch. Drained by `glue_pending`.
    pending: Vec<(Vec<F192>, F192, RoundQuad)>,
}

impl<'a> SumcheckProver<'a> {
    /// `block` is the lane block size `2^(log_n - initial_k)`: the first
    /// `initial_k` rounds are the lane fold, so round 0's message already pairs
    /// whole blocks rather than adjacent words.
    fn new(
        f: &'a [F64],
        b1: Vec<F192>,
        h1: F192,
        block: usize,
        initial_message: Option<SumcheckMessage>,
    ) -> (Self, SumcheckMessage) {
        let _span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().ilog2()).entered();
        assert_eq!(f.len(), b1.len());
        let msg = initial_message.unwrap_or_else(|| round_msg_blocks(f, &b1, block));
        let inst = Self {
            f: Witness::Base(f),
            combined_basis: b1,
            t_r: h1,
            quad: RoundQuad::from_msg(msg, h1),
            round: 0,
            pending: Vec::new(),
        };
        (inst, msg)
    }

    /// The claim that fixes the next message's linear coefficient.
    #[inline]
    fn claim(&self) -> F192 {
        self.t_r
    }

    /// One lane round: fold block `2i` with block `2i+1` (the last one with the
    /// absent zero padding when the block count is odd) and build the message for
    /// the round after it, which is another lane round unless this was the last.
    fn fold_lane(&mut self, r: F192, block: usize, last: bool) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        // `ilog2` rather than `trailing_zeros`: a lane round's length is
        // `n_lanes * block`, so it is generally not a power of two, and the two
        // kinds of round have to report a comparable number.
        let log_size = match &self.f {
            Witness::Base(f) => f.len().ilog2(),
            Witness::Ext(f) => f.len().ilog2(),
        };
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        let (nf, nb, msg) = match &self.f {
            Witness::Base(f) => fold_and_msg_blocks(f, &self.combined_basis, r, block, last),
            Witness::Ext(f) => fold_and_msg_blocks(f, &self.combined_basis, r, block, last),
        };
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let log_size = match &self.f {
            Witness::Base(f) => f.len().ilog2(),
            Witness::Ext(f) => f.len().ilog2(),
        };
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        let (nf, nb, msg) = match &self.f {
            Witness::Base(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
            Witness::Ext(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
        };
        // Swap the freshly folded buffers in and drop the consumed ones, so the
        // allocator serves the next round's `fold_out_buf` from their memory.
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    fn introduce_new(&mut self, b_new: Vec<F192>, h_new: F192) -> SumcheckMessage {
        let msg = match &self.f {
            Witness::Base(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
            Witness::Ext(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
        };
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        msg
    }

    /// Introduce `b_new` and compute its claimed inner product in the same
    /// pass as the round message. OOD claims only occur after the first fold,
    /// when the witness has already been lifted from K to E.
    fn introduce_new_with_eval(&mut self, b_new: Vec<F192>) -> (SumcheckMessage, F192) {
        let f = match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("OOD claim introduced before the first fold"),
        };
        assert_eq!(b_new.len(), f.len());
        let (msg, h_new) = round_msg_and_eval_lsb_ext(f, &b_new);
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
            const PAR_THRESHOLD: usize = 4096;
            if self.combined_basis.len() < PAR_THRESHOLD {
                for (acc, &v) in self.combined_basis.iter_mut().zip(b_new.iter()) {
                    *acc += scalar * v;
                }
            } else {
                let chunk = parallel::recommended_chunk_size(self.combined_basis.len());
                parallel::chunks_mut_zip(&mut self.combined_basis, &b_new, chunk, |_, accs, news| {
                    for (acc, &v) in accs.iter_mut().zip(news) {
                        *acc += scalar * v;
                    }
                });
            }
            self.t_r += scalar * h_new;
            self.quad = RoundQuad::fold(&self.quad, &quad_new, scalar);
        }
    }

    /// The folded witness (post-first-fold: always E). Panics if called
    /// before the first fold (the base phase never reaches a commit).
    fn f_ext(&self) -> &[F192] {
        match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
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
fn send_ood(sc: &mut SumcheckProver<'_>, ps: &mut ProverState, n_vars: usize, count: usize) {
    for _ in 0..count {
        let z = ps.sample_vec(n_vars);
        let (intro, y) = sc.introduce_new_with_eval(build_eq_table_ext_parallel(&z));
        ps.add_scalar(y);
        send_msg(ps, intro, y);
    }
}

/// An `E` row as the `F64` words its Merkle leaf is hashed from.
fn ext_row_words(row: &[F192]) -> Vec<F64> {
    row.iter().flat_map(|v| [F64(v.c0), F64(v.c1), F64(v.c2)]).collect()
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is borrowed: it is only READ (round-0 message + the first lane
/// fold, which lifts it into an owned E-vector), so callers with a large
/// committed stack pass the slice directly instead of paying a full copy.
///
/// PRECONDITION, and the reason `witness` may be shorter than `2^log_n`: it is a
/// whole number of lane blocks, and `b_initial` must be the weight restricted to
/// them, with the weight VANISHING at every boolean point of
/// `[witness.len(), 2^log_n)`. The lane rounds treat the absent blocks as zero
/// while a verifier evaluates the weight's closed form over the whole cube,
/// so a weight that is nonzero out there produces a proof that fails only at the
/// terminal check. `stack_open` discharges this by bounding every claim's support
/// by `stack.len()`; `ood_samples[0] == 0` is what keeps a full-tensor OOD weight
/// out of these rounds.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one phase per level. The caller has already bound the initial commitment and target.
pub fn recursive_prover_with_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Vec<F192>,
    target: F192,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    ps: &mut ProverState,
) {
    recursive_prover_with_prepared_basis(
        config,
        log_n,
        witness,
        b_initial,
        target,
        l0_codeword,
        l0_tree,
        None,
        ps,
    );
}

pub(crate) fn recursive_prover_with_prepared_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Vec<F192>,
    target: F192,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    initial_message: Option<SumcheckMessage>,
    ps: &mut ProverState,
) {
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
    assert_eq!(b_initial.len(), witness.len());
    assert_eq!(l0_codeword.len(), block_len_0 * n_lanes);
    assert_eq!(l0_tree.len(), 2 * block_len_0 - 1);

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
    let l0_row = |q: usize| -> Vec<F64> { l0_codeword[q * n_lanes..(q + 1) * n_lanes].to_vec() };
    // The same row for the induce, which folds a lane-ASCENDING row against the
    // lane eq table: reversing the image puts block `b` at index `b` and the absent
    // lanes' zeros at the end, where they contribute nothing.
    let l0_fold_row = |q: usize| -> Vec<F64> {
        let mut row = vec![F64::ZERO; num_interleaved_0];
        for (t, &word) in l0_codeword[q * n_lanes..(q + 1) * n_lanes].iter().enumerate() {
            row[n_lanes - 1 - t] = word;
        }
        row
    };

    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };

    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc_prover, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, b_initial, target, lane_block, initial_message));
    send_msg(ps, start_msg, target);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        let r_j = ps.sample();
        let msg = sumcheck_span.in_scope(|| sc_prover.fold_lane(r_j, lane_block, j + 1 == initial_k));
        send_msg(ps, msg, sc_prover.claim());
        r_lane_fold.push(r_j);
    }
    drop(sumcheck_span);

    // Commit f^1 = folded (now E-valued) witness as wtns_1.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates[1];
    let span = tracing::info_span!("Commit", level = 1).entered();
    let ntt_1 = AdditiveNttF64::standard(log_msg_cols_1 + log_inv_rate_1);
    let wtns_1 = ligero_commit_ext(
        sc_prover.f_ext(),
        log_msg_cols_1,
        log_num_interleaved_1,
        log_inv_rate_1,
        &ntt_1,
    );
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
    let opened_rows_0: Vec<Vec<F64>> = queries_0.iter().map(|&q| l0_fold_row(q)).collect();
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    ps.hint_merkle(PrunedMerklePaths::prune(l0_tree, block_len_0, &queries_0, l0_row));
    drop(span);

    // Induce basis_0 from the L0 opens. The dispatcher picks the sparse-prefix
    // transposed NTT wherever a level opens more queries than its blowup.
    let sks_vks_n1 = eval_sk_at_vks(n1);
    let span = tracing::info_span!("Induce", level = 0).entered();
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto(
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
            ps.hint_merkle(PrunedMerklePaths::prune(
                &wtns_prev.tree,
                wtns_prev.block_len,
                &queries_last,
                |q| ext_row_words(wtns_prev.row(q)),
            ));
            // Tie the last commitment into the running claim through the same
            // intro/glue step as every other level, then finish the remaining
            // sumcheck rounds. This closes on one weight evaluation instead of
            // a sweep over the residual cube.
            let rows_last: Vec<Vec<F192>> = queries_last.iter().map(|&q| wtns_prev.row(q).to_vec()).collect();
            let enforced_sum_last = induce_sumcheck_enforced_sum(&rows_last, &level_rs, &queries_last, &weights_last);
            let n_res = sc_prover.f_ext().len().trailing_zeros() as usize;
            let basis_last = induce_sumcheck_evaluate_at_residual(
                n_res,
                &eval_sk_at_vks(n_res),
                &queries_last,
                &weights_last,
                &[],
                n_res,
            );
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
        let ntt_next = AdditiveNttF64::standard(log_msg_cols_next + log_inv_rate_next);
        let wtns_next = ligero_commit_ext(
            sc_prover.f_ext(),
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
            &ntt_next,
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
        let opened_rows_i: Vec<Vec<F192>> = queries_i.iter().map(|&q| wtns_prev.row(q).to_vec()).collect();
        ps.hint_merkle(PrunedMerklePaths::prune(
            &wtns_prev.tree,
            wtns_prev.block_len,
            &queries_i,
            |q| ext_row_words(wtns_prev.row(q)),
        ));
        drop(span);

        let sks_vks_i = eval_sk_at_vks(n_next);
        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let (basis_i_induced, enforced_sum_i) = induce_sumcheck_poly_auto(
            n_next,
            config.log_inv_rates[i + 1],
            &sks_vks_i,
            &opened_rows_i,
            &level_rs,
            &queries_i,
            &weights_i,
        );
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
            let mut seeded = Box::new_uninit_slice(1 << n).into_vec();
            primitives::multilinear::fill_eq_table_uninit(&point, g, &mut seeded);
            // SAFETY: fill_eq_table_uninit initializes every entry.
            let seeded = unsafe { seeded.into_boxed_slice().assume_init() }.into_vec();
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
        // `log_n = 18` puts the lane block over `ROUND_CHUNK`, so the fold runs several
        // x-chunks per block; at 13 it is one chunk per block. Both matter: the chunked
        // path is what production takes, and it is where a message pair could straddle
        // a task.
        for (log_n, lanes) in [(13usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                let mut b_initial: Vec<F192> = (0..1usize << log_n).map(|_| rng.ext()).collect();
                witness[used..].fill(F64::ZERO);
                b_initial[used..].fill(F192::ZERO);
                let target = inner_product_base_ext(&witness, &b_initial);

                let prove = |msg: &[F64], b: &[F192]| {
                    let (cm, pd) = commit(msg, log_n, pc.initial_k, pc.log_inv_rates[0]);
                    let mut ps = fiat_shamir::transcript::ProverState::from_label(b"whir-test");
                    recursive_prover_with_basis(
                        &pc,
                        log_n,
                        msg,
                        b.to_vec(),
                        target,
                        &pd.codeword,
                        &pd.merkle_tree,
                        &mut ps,
                    );
                    (cm.root, ps.into_proof())
                };
                let (root_trunc, fs_trunc) = prove(&witness[..used], &b_initial[..used]);
                let (root_full, fs_full) = prove(&witness, &b_initial);
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
    /// LCH-expansion induce (same guarantee the original pins). Covers both
    /// the windowed sparse-prefix path (log_block >= 12, k = 8) and the
    /// scatter + full-dense-transpose path (log_block < 12, k = 0).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in [(12usize, 1usize, 5usize, 130usize), (6, 2, 3, 40)] {
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
            let rows: Vec<Vec<F64>> = (0..n_queries)
                .map(|_| (0..lanes).map(|_| F64(rng.next_u64())).collect())
                .collect();
            let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
            let weights = powers(rng.ext(), n_queries);

            let sks_vks = eval_sk_at_vks(log_msg_cols);
            let dense = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &weights);
            let via_ntt = induce_sumcheck_poly_via_ntt(log_msg_cols, log_inv_rate, &rows, &v_challenges, &qs, &weights);
            assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
            assert_eq!(&*dense.0, &*via_ntt.0, "basis_poly mismatch");
        }
    }

    #[test]
    fn initial_basis_message_matches_materialized_weights() {
        let mut rng = Rng::new(0xBA515);
        for block in [1, 16, INITIAL_BASIS_CHUNK, 4 * INITIAL_BASIS_CHUNK] {
            for lanes in [1, 2, 3, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                let expected = rng.ext_vec(f.len());
                let expected_message = round_msg_blocks(&f, &expected, block);
                let (actual, message) = build_initial_basis(&f, block, |start, out| {
                    out.copy_from_slice(&expected[start..start + out.len()]);
                });
                assert_eq!(&*actual, expected, "block={block}, lanes={lanes}");
                assert_eq!(message, expected_message, "block={block}, lanes={lanes}");
            }
        }
    }
}
