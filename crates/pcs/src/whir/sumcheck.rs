// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The opening's sumcheck prover: its round messages, the fold kernels, and the
//! running claim every level's queries are batched into. The first lane rounds
//! come out of one pass, in [`first_pass`].

use crate::stack_open::StackWeight;
use core::ops::BitXorAssign;
use fiat_shamir::transcript::{Receiver, TranscriptError, Transmitter};
use first_pass::{LaneWeight, WeightFold};
use parallel::SendPtr;
use primitives::field::{F64, F192, F192Unreduced};
use primitives::multilinear::eq_table;
use primitives::stream::Stream;
use std::ops::Add;

mod first_pass;

pub(crate) use first_pass::{InitialRounds, initial_rounds};

// ===================================================================
// Tuning constants
// ===================================================================
//
// Prover-side work sizes, gathered here so they can be found and tuned together.
// The round messages do not depend on them.

/// Lane rounds whose messages come out of [`first_pass`].
const PRECOMPUTED_ROUNDS: usize = 4;

/// Work items below which a loop runs on the calling thread, where dispatch costs more than the work.
const PAR_THRESHOLD: usize = 4096;

/// [`PAR_THRESHOLD`] for the first pass, counted in words over all its lanes.
const FIRST_PASS_PAR_THRESHOLD: usize = 8192;

/// Elements per task wherever a round is chunked: the fused adjacent-pair fold,
/// and the lane rounds, whose block is the whole L0 message divided by the
/// interleaving and so has to be fed to the pool from inside a block pair rather
/// than across them.
const ROUND_CHUNK: usize = 2048;

/// Words of the initial weight one fill call writes: a chunk, aligned to its size.
///
/// A lane block below this size is filled whole.
pub(crate) const INITIAL_BASIS_CHUNK: usize = 256;

/// Elements a stored (dense) weight's lane fold stages in L1 before publishing them.
const DENSE_STAGE: usize = 128;

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
pub(super) fn send_msg(ps: &mut impl Transmitter, m: SumcheckMessage, claim: F192) {
    ps.add_round_poly(&[m.u_0, claim + m.u_2, m.u_2], false);
}

/// Verifier mirror of [`send_msg`]. The round polynomial already travels in the
/// coefficient form the folds use.
pub(super) fn recv_quad(vs: &mut impl Receiver, claim: F192) -> Result<RoundQuad, TranscriptError> {
    let h = vs.next_round_poly(3, claim, None)?;
    Ok(RoundQuad {
        c: h[0],
        b: h[1],
        a: h[2],
    })
}

/// Round-quadratic in coefficient form `c + b X + a X^2` (verifier side).
#[derive(Clone, Copy, Debug)]
pub(super) struct RoundQuad {
    c: F192, // u_0
    b: F192, // u_1 (X coeff), derived from T_r and u_2
    a: F192, // u_2 (X^2 coeff)
}

impl RoundQuad {
    /// The quadratic a round message stands for, given the claim it answers:
    /// `h(0) + h(1) = claim` fixes the linear coefficient.
    #[inline]
    pub(super) fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    pub(super) fn eval(&self, r: F192) -> F192 {
        (self.a * r + self.b) * r + self.c
    }
    #[inline]
    pub(super) fn fold(p1: &Self, p2: &Self, alpha: F192) -> Self {
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
trait RoundWitness: Copy + Sync + Add<Output = Self> {
    type Acc: Copy + Send + BitXorAssign;
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
    /// Add `e·x` over one lane's window `xs` to a fold of several lane bits at once.
    fn add_weighted_lane(acc: &mut WeightFold, e: &LaneWeight, xs: &[Self]);
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
    #[inline]
    fn add_weighted_lane(acc: &mut WeightFold, e: &LaneWeight, xs: &[Self]) {
        acc.add_base(e, xs);
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
    #[inline]
    fn add_weighted_lane(acc: &mut WeightFold, e: &LaneWeight, xs: &[Self]) {
        acc.add(e, xs);
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
    let mut nf = Box::new_uninit_slice(half);
    let mut nb = Box::new_uninit_slice(half);
    // The fold writes and the message accumulate share one pass per chunk, so
    // the freshly folded values are still in L1 when they are multiplied.
    let nf_base = SendPtr(nf.as_mut_ptr());
    let nb_base = SendPtr(nb.as_mut_ptr());
    let (u_0, u_2) = parallel::map_reduce(
        half.div_ceil(ROUND_CHUNK),
        || (F192Unreduced::ZERO, F192Unreduced::ZERO),
        |ci| {
            let base = ci * ROUND_CHUNK;
            let len = ROUND_CHUNK.min(half - base);
            // SAFETY: distinct `ci` own disjoint in-bounds `ROUND_CHUNK`-windows of
            // `nf`/`nb`, and both buffers stay borrowed for the whole dispatch.
            let fc = unsafe { nf_base.slice(base, len) };
            // SAFETY: as for `fc`, the same window of `nb`.
            let bc = unsafe { nb_base.slice(base, len) };
            for t in 0..len {
                let j = base + t;
                fc[t].write(fold_f(j));
                bc[t].write(fold_b(j));
            }
            // SAFETY: the loop just wrote both windows.
            unsafe { fold_msg_terms(fc.assume_init_ref(), bc.assume_init_ref()) }
        },
        |(mut a0, mut a2), (c0, c2)| {
            a0 ^= c0;
            a2 ^= c2;
            (a0, a2)
        },
    );
    // SAFETY: the tasks wrote every slot of both, one output per pair or group of input blocks.
    let (nf, nb) = unsafe { (nf.assume_init().into_vec(), nb.assume_init().into_vec()) };
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

/// Sum the per-task `(u_0, u_2)` accumulators, sequentially for the small
/// instances where dispatch costs more than the work. Unreduced accumulators
/// combine by XOR and `reduce` is linear, so both paths land on the same message.
#[inline]
fn accumulate_msg<A: Copy + Send + BitXorAssign>(
    n_tasks: usize,
    n_pairs: usize,
    zero: A,
    task: impl Fn(usize) -> (A, A) + Sync,
) -> (A, A) {
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

/// The weight the opening's sumcheck folds against.
pub(crate) enum Basis<'a> {
    /// One E value per word, in memory.
    Dense(Vec<F192>),
    /// Regenerated when read, by chunks of the initial fill size.
    ///
    /// Only the first pass and the first fold read it, so it is never stored.
    Virtual(&'a StackWeight<'a>),
}

impl Basis<'_> {
    /// The weight in memory.
    ///
    /// # Panics
    ///
    /// Panics before the first fold has folded a regenerated weight.
    fn dense(&self) -> &Vec<F192> {
        match self {
            Basis::Dense(b) => b,
            Basis::Virtual(_) => panic!("the regenerated weight is read by the first fold only"),
        }
    }

    /// The weight in memory, to update.
    fn dense_mut(&mut self) -> &mut Vec<F192> {
        match self {
            Basis::Dense(b) => b,
            Basis::Virtual(_) => panic!("the regenerated weight is read by the first fold only"),
        }
    }
}

/// A window of the weight: sliced from memory, or refilled into a scratch of its own.
fn window<'r>(b: &'r Basis<'_>, raw: &'r mut [F192; INITIAL_BASIS_CHUNK], at: usize, len: usize) -> &'r [F192] {
    match b {
        Basis::Dense(b) => &b[at..at + len],
        Basis::Virtual(weight) => {
            weight.fill(at, &mut raw[..len]);
            &raw[..len]
        }
    }
}

/// Fused lane fold + next-round message. Mirror of [`fold_and_msg_lsb`] for the
/// block pairing: `rs` binds the next `rs.len()` lane bits, so `2^rs.len()` input
/// blocks fold into each output block, and a task owns one output *pair*, because
/// that is the smallest unit the next round's message is local to.
///
/// `last` says this is the final lane round, so the round after it pairs adjacent
/// elements of the single output block rather than another pair of blocks. Which
/// pairing comes next is what lets the message be built here, while the folded
/// values are still in L1.
fn fold_and_msg_blocks<T: RoundWitness>(
    f: &[T],
    b: &Basis<'_>,
    rs: &[F192],
    block: usize,
    last: bool,
) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    if let Basis::Dense(b) = b {
        assert_eq!(b.len(), f.len());
    }
    assert!(block > 0 && f.len().is_multiple_of(block));
    assert!(!rs.is_empty());
    let n_in = f.len() / block;
    let n_out = n_in.div_ceil(1 << rs.len());
    // Adjacent pairing next round is only possible once the lanes have collapsed
    // to a single block.
    assert!(!last || n_out == 1);
    // Several bits at once fold each output against the input blocks' eq weights.
    let eq = eq_table(rs);
    let eq_weights: Vec<LaneWeight> = if rs.len() > 1 {
        eq.iter().map(|&e| LaneWeight::new(e)).collect()
    } else {
        Vec::new()
    };
    // A regenerated weight folds its point claims in closed form, so only its ring-switched part goes lane by lane.
    let points = match b {
        Basis::Virtual(weight) if rs.len() > 1 => Some(weight.fold_points(rs, n_out * block)),
        _ => None,
    };

    let mut nf = Box::new_uninit_slice(n_out * block);
    let mut nb = Box::new_uninit_slice(n_out * block);
    let nf_base = SendPtr(nf.as_mut_ptr());
    let nb_base = SendPtr(nb.as_mut_ptr());

    let per = block.div_ceil(ROUND_CHUNK);
    // Fold into an L1-resident stage rather than straight into `nf`/`nb`. The
    // message reads the folded values back, and reading them here instead of out
    // of the destination is what lets the destination be published with
    // streaming stores: nothing else touches it until the next round, by which
    // time a buffer this size is long evicted, so the fetch an ordinary store
    // would make of every line it overwrites is pure waste.
    //
    // A regenerated weight is refilled one fill chunk at a time, the unit its fill is written for.
    const STAGE_MAX: usize = INITIAL_BASIS_CHUNK;
    let stage_len = match b {
        Basis::Dense(_) => DENSE_STAGE,
        Basis::Virtual(_) => STAGE_MAX,
    };
    let fold_block = |stage: &mut [F192],
                      stage_b: &mut [F192],
                      raw: &mut [[F192; STAGE_MAX]; 2],
                      out_blk: usize,
                      x0: usize,
                      stream: &Stream| {
        let len = stage.len();
        let src0 = eq.len() * out_blk * block + x0;
        let [raw_lo, raw_hi] = raw;
        // Sliced, not indexed: runs of one length let the bounds checks fall out
        // and the pair fold vectorise, as the adjacent-pair kernel's do.
        let f_lo = &f[src0..src0 + len];
        if let [r] = *rs {
            let b_lo = window(b, raw_lo, src0, len);
            if 2 * out_blk + 1 < n_in {
                let src1 = src0 + block;
                let b_hi = window(b, raw_hi, src1, len);
                let f_hi = &f[src1..src1 + len];
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
        } else {
            // One unreduced sum per output over its input blocks; absent ones are the zero padding.
            let (mut acc_f, mut acc_b) = (WeightFold::default(), WeightFold::default());
            for (l, e) in eq_weights.iter().enumerate() {
                let src = src0 + l * block;
                if src >= f.len() {
                    break;
                }
                T::add_weighted_lane(&mut acc_f, e, &f[src..src + len]);
                match b {
                    Basis::Dense(b) => acc_b.add(e, &b[src..src + len]),
                    // A lane with no ring-switched words adds nothing.
                    Basis::Virtual(weight) => {
                        if weight.fill_rings(src, &mut raw_lo[..len]) {
                            acc_b.add(e, &raw_lo[..len]);
                        }
                    }
                }
            }
            acc_f.write(stage);
            acc_b.write(stage_b);
            if let Some(points) = &points {
                points.add(out_blk * block + x0, stage_b);
            }
        }
        // SAFETY: distinct (out_blk, x0) name disjoint in-bounds windows of `nf`
        // and `nb`, which stay borrowed for the whole dispatch.
        unsafe {
            stream.write(nf_base.slice(out_blk * block + x0, len), stage);
            stream.write(nb_base.slice(out_blk * block + x0, len), stage_b);
        }
    };

    let task = |t: usize| -> (F192Unreduced, F192Unreduced) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let stream = Stream::new();
        let mut stage = [[F192::ZERO; STAGE_MAX]; 4];
        let mut raw = [[F192::ZERO; STAGE_MAX]; 2];
        let mut acc = (F192Unreduced::ZERO, F192Unreduced::ZERO);
        for s in (0..len).step_by(stage_len) {
            let n = stage_len.min(len - s);
            let [lo_f, lo_b, hi_f, hi_b] = &mut stage;
            fold_block(&mut lo_f[..n], &mut lo_b[..n], &mut raw, 2 * i, x0 + s, &stream);
            let (u_0, u_2) = if 2 * i + 1 < n_out {
                fold_block(&mut hi_f[..n], &mut hi_b[..n], &mut raw, 2 * i + 1, x0 + s, &stream);
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
    // SAFETY: the tasks wrote every slot of both, one output per pair or group of input blocks.
    let (nf, nb) = unsafe { (nf.assume_init().into_vec(), nb.assume_init().into_vec()) };
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
pub(super) struct SumcheckProver<'a> {
    f: Witness<'a>,
    /// Single combined basis poly: `glue_pending(lambda)` folds each claim
    /// introduced since the last glue in as `combined_basis += lambda^tau *
    /// b_new`, `tau` counting from 1 (the running claim is `tau = 0`).
    combined_basis: Basis<'a>,
    /// The running claim and its quadratic; `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    quad: RoundQuad,
    round: usize,
    /// The first pass's sums, which give the first lane rounds' messages.
    initial: InitialRounds,
    /// The lane challenges drawn while those rounds defer their fold.
    lane_rs: Vec<F192>,
    /// The level's claims, in Protocol 1 step 1 order: the OOD claims, then the
    /// query batch. Drained by `glue_pending`.
    pending: Vec<(Vec<F192>, F192, RoundQuad)>,
}

impl<'a> SumcheckProver<'a> {
    /// `block` is the lane block size `2^(log_n - initial_k)`: the first
    /// `initial_k` rounds are the lane fold, so round 0's message already pairs
    /// whole blocks rather than adjacent words.
    pub(super) fn new(
        f: &'a [F64],
        b1: Basis<'a>,
        h1: F192,
        block: usize,
        initial_k: usize,
        initial: Option<InitialRounds>,
    ) -> (Self, SumcheckMessage) {
        let _span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().ilog2()).entered();
        let initial = initial.unwrap_or_else(|| initial_rounds(f, block, initial_k, &b1));
        assert!(initial.rounds <= initial_k);
        let msg = initial.message(0, &[]);
        let inst = Self {
            f: Witness::Base(f),
            combined_basis: b1,
            t_r: h1,
            quad: RoundQuad::from_msg(msg, h1),
            round: 0,
            lane_rs: Vec::with_capacity(initial.rounds),
            initial,
            pending: Vec::new(),
        };
        (inst, msg)
    }

    /// The claim that fixes the next message's linear coefficient.
    #[inline]
    pub(super) const fn claim(&self) -> F192 {
        self.t_r
    }

    /// One lane round: fold block `2i` with block `2i+1` (the last one with the
    /// absent zero padding when the block count is odd) and build the message for
    /// the round after it, which is another lane round unless this was the last.
    ///
    /// The first pass's rounds defer their fold: their messages are interpolated,
    /// and the last of them folds all their lane bits at once.
    pub(super) fn fold_lane(&mut self, r: F192, block: usize, last: bool) -> SumcheckMessage {
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
        let deferred = self.round <= self.initial.rounds;
        if deferred {
            self.lane_rs.push(r);
            if self.round < self.initial.rounds {
                let msg = self.initial.message(self.round, &self.lane_rs);
                self.quad = RoundQuad::from_msg(msg, self.t_r);
                return msg;
            }
        }
        let rs = if deferred { &self.lane_rs[..] } else { &[r][..] };
        let (nf, nb, msg) = match &self.f {
            Witness::Base(f) => fold_and_msg_blocks(f, &self.combined_basis, rs, block, last),
            Witness::Ext(f) => fold_and_msg_blocks(f, &self.combined_basis, rs, block, last),
        };
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, Basis::Dense(nb)));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    pub(super) fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let log_size = match &self.f {
            Witness::Base(f) => f.len().ilog2(),
            Witness::Ext(f) => f.len().ilog2(),
        };
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        let (nf, nb, msg) = match &self.f {
            Witness::Base(f) => fold_and_msg_lsb(f, self.combined_basis.dense(), r),
            Witness::Ext(f) => fold_and_msg_lsb(f, self.combined_basis.dense(), r),
        };
        // Swap the folded buffers in and drop the consumed ones.
        // Why: the allocator then serves the next round's fold from their memory.
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, Basis::Dense(nb)));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    pub(super) fn introduce_new(&mut self, b_new: Vec<F192>, h_new: F192) -> SumcheckMessage {
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
    pub(super) fn introduce_new_with_eval(&mut self, b_new: Vec<F192>) -> (SumcheckMessage, F192) {
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
    pub(super) fn glue_pending(&mut self, lambda: F192) {
        let pending = std::mem::take(&mut self.pending);
        assert!(!pending.is_empty(), "glue without introduce_new");
        let mut scalar = F192::ONE;
        for (b_new, h_new, quad_new) in pending {
            scalar *= lambda;
            let combined = self.combined_basis.dense_mut();
            assert_eq!(b_new.len(), combined.len());
            if combined.len() < PAR_THRESHOLD {
                for (acc, &v) in combined.iter_mut().zip(b_new.iter()) {
                    *acc += scalar * v;
                }
            } else {
                let chunk = parallel::recommended_chunk_size(combined.len());
                parallel::chunks_mut_zip(combined, &b_new, chunk, |_, accs, news| {
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
    pub(super) fn f_ext(&self) -> &[F192] {
        match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stack_open::tests::RandomWeight;
    use crate::whir_config::INITIAL_FOLDING_FACTOR;
    use primitives::multilinear::inner_product;
    use primitives::test_util::Rng;

    /// Round message for a lane round, over `f.len() / block` blocks: the reference the first pass is tested against.
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

    #[test]
    fn a_regenerated_weight_folds_like_the_stored_one() {
        // Invariant: a lane fold writes the same fold and message from either weight, one lane bit at a time
        // or several, where the point claims fold in closed form.
        let mut rng = Rng::new(0xF111);
        // Fixture state: blocks below, at and above one fill chunk and one task chunk.
        for block in [1, 16, INITIAL_BASIS_CHUNK, 4 * INITIAL_BASIS_CHUNK, 2 * ROUND_CHUNK] {
            // An odd lane count leaves a lone block, and a partial group absent lanes, folded as zero.
            for lanes in [1, 2, 3, 17, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                let fixture = RandomWeight::new(&mut rng, lanes, block);
                let (stored, weight) = (Basis::Dense(fixture.dense()), fixture.weight());
                for bits in [1, 2, PRECOMPUTED_ROUNDS] {
                    let rs = rng.ext_vec(bits);
                    // The last lane round is the one whose output is a single block.
                    let last = lanes <= 1 << bits;
                    let label = format!("block={block}, lanes={lanes}, bits={bits}");

                    let (nf_s, nb_s, msg_s) = fold_and_msg_blocks(&f, &stored, &rs, block, last);
                    let (nf_r, nb_r, msg_r) = fold_and_msg_blocks(&f, &Basis::Virtual(&weight), &rs, block, last);
                    assert_eq!(&*nf_s, &*nf_r, "fold, {label}");
                    assert_eq!(&*nb_s, &*nb_r, "weight fold, {label}");
                    assert_eq!(msg_s, msg_r, "message, {label}");
                }
            }
        }
    }

    #[test]
    fn precomputed_lane_rounds_match_round_by_round_folds() {
        // Invariant: the first pass's interpolated messages and its many-bit fold are the
        // messages and the witness of folding one lane bit a round, from either weight.
        let mut rng = Rng::new(0xBA515);
        for initial_k in [1, 2, 3, PRECOMPUTED_ROUNDS, INITIAL_FOLDING_FACTOR] {
            let full = 1usize << initial_k;
            for block in [1, 16, INITIAL_BASIS_CHUNK, 2 * ROUND_CHUNK] {
                // Partial groups and odd counts meet the absent zero lanes.
                for lanes in [1, 2, 3, 5, full - 1, full, 37]
                    .into_iter()
                    .filter(|&l| l >= 1 && l <= full)
                {
                    let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                    let fixture = RandomWeight::new(&mut rng, lanes, block);
                    let weight = fixture.dense();
                    let rs = rng.ext_vec(initial_k);
                    let label = format!("initial_k={initial_k}, block={block}, lanes={lanes}");

                    let mut expected = vec![round_msg_blocks(&f, &weight, block)];
                    let stored = Basis::Dense(weight.to_vec());
                    let (mut nf, mut nb, msg) = fold_and_msg_blocks(&f, &stored, &rs[..1], block, initial_k == 1);
                    expected.push(msg);
                    for (j, r) in rs.iter().enumerate().skip(1) {
                        let msg;
                        (nf, nb, msg) = fold_and_msg_blocks(
                            &nf,
                            &Basis::Dense(nb),
                            std::slice::from_ref(r),
                            block,
                            j + 1 == initial_k,
                        );
                        expected.push(msg);
                    }

                    let regenerated = fixture.weight();
                    for basis in [Basis::Dense(weight.to_vec()), Basis::Virtual(&regenerated)] {
                        let (mut sc, msg) = SumcheckProver::new(&f, basis, F192::ZERO, block, initial_k, None);
                        let mut actual = vec![msg];
                        for (j, &r) in rs.iter().enumerate() {
                            actual.push(sc.fold_lane(r, block, j + 1 == initial_k));
                        }
                        assert_eq!(actual, expected, "messages, {label}");
                        assert_eq!(sc.f_ext(), &*nf, "witness, {label}");
                        assert_eq!(&**sc.combined_basis.dense(), &*nb, "weight, {label}");
                    }
                }
            }
        }
    }

    #[test]
    fn the_folds_bind_the_rotated_point() {
        // Invariant: after every round, the witness and the weight are their multilinear extensions at the round
        // challenges rotated left by the lane fold, which is the point the verifier hands its weight closure.
        let mut rng = Rng::new(0x707A7E);
        let dense_mle = |table: &[F192], point: &[F192]| inner_product(table, &eq_table(point));
        // Fixture state: `log_n = 15` puts the lane block over the fold's task chunk; the lane counts below the
        // interleaving leave absent lanes, zero in the dense tables.
        for (log_n, initial_k, lanes) in [(9usize, 3usize, &[1usize, 5, 8][..]), (15, 3, &[3, 8][..])] {
            let block = 1usize << (log_n - initial_k);
            for &n_lanes in lanes {
                let used = n_lanes * block;
                let mut f = vec![F64::ZERO; 1 << log_n];
                f[..used].iter_mut().for_each(|w| *w = F64(rng.next_u64()));
                let mut b = vec![F192::ZERO; 1 << log_n];
                b[..used].copy_from_slice(&rng.ext_vec(used));

                let (mut sc, _) = SumcheckProver::new(
                    &f[..used],
                    Basis::Dense(b[..used].to_vec()),
                    F192::ZERO,
                    block,
                    initial_k,
                    None,
                );
                let rounds = rng.ext_vec(log_n);
                for (j, &r) in rounds[..initial_k].iter().enumerate() {
                    sc.fold_lane(r, block, j + 1 == initial_k);
                }
                for &r in &rounds[initial_k..] {
                    sc.fold(r);
                }

                let mut point = rounds;
                point.rotate_left(initial_k);
                let lifted: Vec<F192> = f.iter().map(|&w| F192::from(w)).collect();
                assert_eq!(
                    sc.f_ext(),
                    [dense_mle(&lifted, &point)],
                    "witness, log_n={log_n}, lanes={n_lanes}"
                );
                assert_eq!(
                    sc.combined_basis.dense()[..],
                    [dense_mle(&b, &point)],
                    "weight, log_n={log_n}, lanes={n_lanes}"
                );
            }
        }
    }
}
