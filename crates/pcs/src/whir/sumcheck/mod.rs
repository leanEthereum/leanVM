// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The opening's sumcheck prover: round messages, fold kernels, and the running claim each level's queries join.
//!
//! The first lane rounds' messages come from one pass over the witness and the initial weight, in a submodule.

use core::ops::BitXorAssign;
use fiat_shamir::transcript::Transmitter;
use first_pass::{LaneWeight, WeightFold};
use parallel::SendPtr;
use primitives::field::{F64, F192, F192Unreduced};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::field::{F192x4, F192x4Unreduced};
use primitives::multilinear::eq_table;
use primitives::stream::Stream;
use std::mem::MaybeUninit;
use std::sync::Arc;

mod first_pass;

use first_pass::{InitialRounds, first_pass};

// Tuning constants: prover-side work sizes, kept in one place so they are tuned together.
// The round messages do not depend on them.

/// Lane rounds whose messages the first pass precomputes.
const PRECOMPUTED_ROUNDS: usize = 4;

/// Work items below which a loop runs on the calling thread, where dispatch costs more than the work.
const PAR_THRESHOLD: usize = 4096;

/// The same threshold for the first pass, counted in words over all its lanes.
const FIRST_PASS_PAR_THRESHOLD: usize = 8192;

/// Elements per task wherever a round is chunked: the adjacent-pair fold and the lane rounds.
///
/// A lane block is the whole witness divided by the lane count, so its tasks must split inside a block pair.
const ROUND_CHUNK: usize = 2048;

/// Words of the initial weight one fill call writes: one chunk, aligned to its size.
///
/// A lane block smaller than this is filled whole.
pub(crate) const INITIAL_BASIS_CHUNK: usize = 256;

// Sumcheck over `E`, the witness in `K` until the first fold and in `E` after it.
//
// A round's polynomial is `h(X) = u_0 + u_1 X + u_2 X^2`, with `h(0) + h(1) = T_r` the running claim.
// The prover sends `u_0` and `u_2`; in characteristic 2 the verifier derives `u_1 = T_r + u_2`, and then:
//
//     h(r) = u_0 + r T_r + (r + r^2) u_2
//
// The lane rounds pair the `K` witness with the `E` weight by mixed products; their fold lifts the witness to `E`.

/// One round's message, both coefficients in `E`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    /// `h(0)`, the constant coefficient.
    u_0: F192,
    /// The coefficient of `X^2`, also written `h(inf)`.
    u_2: F192,
}

/// Sends the constant and quadratic coefficients; the claim fixes the linear one, so it is not sent.
pub(super) fn send_msg(ps: &mut impl Transmitter, m: SumcheckMessage, claim: F192) {
    ps.add_round_poly(&[m.u_0, claim + m.u_2, m.u_2], false);
}

/// A round's quadratic `c + b X + a X^2`: the prover's copy of the verifier's running round.
#[derive(Clone, Copy, Debug)]
pub(super) struct RoundQuad {
    /// `u_0`, the constant coefficient.
    c: F192,
    /// `u_1`, the linear coefficient, derived from the claim and `u_2`.
    b: F192,
    /// `u_2`, the quadratic coefficient.
    a: F192,
}

impl RoundQuad {
    /// The quadratic a message stands for, given the claim `t_r` it answers.
    ///
    /// `h(0) + h(1) = t_r` fixes the linear coefficient.
    #[inline]
    pub(super) fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    /// `h(r)`, by Horner's rule.
    #[inline]
    pub(super) fn eval(&self, r: F192) -> F192 {
        (self.a * r + self.b) * r + self.c
    }
    /// `p1 + alpha * p2`, coefficient by coefficient: two claims' quadratics batched by `alpha`.
    #[inline]
    pub(super) fn fold(p1: &Self, p2: &Self, alpha: F192) -> Self {
        Self {
            c: p1.c + alpha * p2.c,
            b: p1.b + alpha * p2.b,
            a: p1.a + alpha * p2.a,
        }
    }
}

/// Folds each pair of a run at `r`, handing `x0 + r * (x0 + x1)` to `out` with its index.
///
/// That is the line through `x0` at 0 and `x1` at 1, evaluated at `r`.
/// It takes four pairs at a time in vector lanes where the target has them.
#[inline(always)]
fn fold_pairs(
    n: usize,
    x0: impl Fn(usize) -> F192,
    x1: impl Fn(usize) -> F192,
    r: F192,
    mut out: impl FnMut(usize, F192),
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    let done = {
        let r4 = F192x4::splat(r);
        for i in (0..n / 4 * 4).step_by(4) {
            let (a, b) = (lanes(&x0, i), lanes(&x1, i));
            for (k, v) in (a + r4 * (a + b)).to_array().into_iter().enumerate() {
                out(i + k, v);
            }
        }
        n / 4 * 4
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    let done = 0;
    for i in done..n {
        let (a, b) = (x0(i), x1(i));
        out(i, a + r * (a + b));
    }
}

/// A round message's unreduced coefficients over a run of witness pairs `(x0, x1)` and weight pairs `(y0, y1)`.
///
/// The sum of `x0 * y0` is `h(0)`, and the sum of `(x0 + x1) * (y0 + y1)` is `h(inf)`.
#[inline(always)]
fn pair_terms(
    n: usize,
    x0: impl Fn(usize) -> F192,
    x1: impl Fn(usize) -> F192,
    y0: impl Fn(usize) -> F192,
    y1: impl Fn(usize) -> F192,
) -> (F192Unreduced, F192Unreduced) {
    let [u_0, u_2, _] = pair_sums::<false>(n, x0, x1, y0, y1);
    (u_0, u_2)
}

/// Unreduced sums over a run of pairs: of `x0 * y0`, of `(x0 + x1) * (y0 + y1)`, and of `x1 * y1`.
///
/// The third sum is computed only when `ODD` is set, and is zero otherwise.
/// It takes four pairs at a time in vector lanes where the target has them.
#[inline(always)]
fn pair_sums<const ODD: bool>(
    n: usize,
    x0: impl Fn(usize) -> F192,
    x1: impl Fn(usize) -> F192,
    y0: impl Fn(usize) -> F192,
    y1: impl Fn(usize) -> F192,
) -> [F192Unreduced; 3] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    let (done, mut sums) = {
        let (mut u_0, mut u_2, mut odd) = (
            F192x4Unreduced::zero(),
            F192x4Unreduced::zero(),
            F192x4Unreduced::zero(),
        );
        for i in (0..n / 4 * 4).step_by(4) {
            let (a0, a1, b0, b1) = (lanes(&x0, i), lanes(&x1, i), lanes(&y0, i), lanes(&y1, i));
            u_0 ^= a0.mul_unreduced(b0);
            u_2 ^= (a0 + a1).mul_unreduced(b0 + b1);
            if ODD {
                odd ^= a1.mul_unreduced(b1);
            }
        }
        (n / 4 * 4, [u_0.sum(), u_2.sum(), odd.sum()])
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    let (done, mut sums) = (0, [F192Unreduced::ZERO; 3]);
    for i in done..n {
        sums[0] ^= x0(i).mul_unreduced(y0(i));
        sums[1] ^= (x0(i) + x1(i)).mul_unreduced(y0(i) + y1(i));
        if ODD {
            sums[2] ^= x1(i).mul_unreduced(y1(i));
        }
    }
    sums
}

/// Four consecutive values, one per lane.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline(always)]
fn lanes(v: &impl Fn(usize) -> F192, i: usize) -> F192x4 {
    F192x4::new(std::array::from_fn(|k| v(i + k)))
}

/// The round message over a witness `f` and a weight `b`, both in `E`, pairing adjacent words.
///
/// Products accumulate unreduced, combined by XOR, and each sum is reduced once.
/// Reduction is linear, so the message equals the one with every product reduced.
fn round_msg_lsb(f: &[F192], b: &[F192]) -> SumcheckMessage {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let half = n / 2;
    let task = |t: usize| {
        let base = t * ROUND_CHUNK;
        let (f, b) = (&f[2 * base..], &b[2 * base..]);
        pair_terms(
            ROUND_CHUNK.min(half - base),
            |j| f[2 * j],
            |j| f[2 * j + 1],
            |j| b[2 * j],
            |j| b[2 * j + 1],
        )
    };
    let (u_0, u_2) = accumulate_msg(half.div_ceil(ROUND_CHUNK), half, task);
    SumcheckMessage {
        u_0: u_0.reduce(),
        u_2: u_2.reduce(),
    }
}

/// The round message and the full inner product `sum_x f(x) * b(x)`, in one pass.
///
/// For an out-of-domain weight `b = eq(z, .)`, the inner product is the claimed evaluation `MLE(f)(z)`.
fn round_msg_and_eval_lsb_ext(f: &[F192], b: &[F192]) -> (SumcheckMessage, F192) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let half = n / 2;
    // The message, and the odd elements' products: with the even ones', the inner product.
    let task = |t: usize| -> [F192Unreduced; 3] {
        let base = t * ROUND_CHUNK;
        let (f, b) = (&f[2 * base..], &b[2 * base..]);
        pair_sums::<true>(
            ROUND_CHUNK.min(half - base),
            |j| f[2 * j],
            |j| f[2 * j + 1],
            |j| b[2 * j],
            |j| b[2 * j + 1],
        )
    };
    let n_tasks = half.div_ceil(ROUND_CHUNK);
    let xor = |mut a: [F192Unreduced; 3], c: [F192Unreduced; 3]| {
        a.iter_mut().zip(c).for_each(|(a, c)| *a ^= c);
        a
    };
    let [u_0, u_2, odd] = if half < PAR_THRESHOLD {
        (0..n_tasks).map(task).fold([F192Unreduced::ZERO; 3], xor)
    } else {
        parallel::map_reduce(n_tasks, || [F192Unreduced::ZERO; 3], task, xor)
    };
    let (u_0, u_2, y) = (u_0.reduce(), u_2.reduce(), (u_0 ^ odd).reduce());
    (SumcheckMessage { u_0, u_2 }, y)
}

/// Unreduced `(u_0, u_2)` over folded `E` buffers, pairing adjacent words.
///
/// A trailing odd word adds nothing, so when the fold leaves a single word the message is zero.
#[inline]
fn fold_msg_terms(nf: &[F192], nb: &[F192]) -> (F192Unreduced, F192Unreduced) {
    pair_terms(
        nf.len() / 2,
        |k| nf[2 * k],
        |k| nf[2 * k + 1],
        |k| nb[2 * k],
        |k| nb[2 * k + 1],
    )
}

/// Folds the witness and the weight at `r` by adjacent pairs, and builds the next round's message in the same pass.
///
/// # Returns
///
/// The folded witness, the folded weight, and the message over them.
fn fold_and_msg_lsb(f: &[F192], b: &[F192], r: F192) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    // Fold a window of pairs of the witness and of the weight.
    let fold = |base: usize, fc: &mut [MaybeUninit<F192>], bc: &mut [MaybeUninit<F192>]| {
        let (f, b) = (&f[2 * base..], &b[2 * base..]);
        fold_pairs(fc.len(), |j| f[2 * j], |j| f[2 * j + 1], r, |j, v| _ = fc[j].write(v));
        fold_pairs(bc.len(), |j| b[2 * j], |j| b[2 * j + 1], r, |j, v| _ = bc[j].write(v));
    };
    if half < PAR_THRESHOLD {
        let mut nf = Vec::with_capacity(half);
        let mut nb = Vec::with_capacity(half);
        fold(
            0,
            &mut nf.spare_capacity_mut()[..half],
            &mut nb.spare_capacity_mut()[..half],
        );
        // SAFETY: the fold wrote all `half` slots of both.
        unsafe {
            nf.set_len(half);
            nb.set_len(half);
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

    // Parallel path: `half` and `ROUND_CHUNK` are powers of two, and `half >= PAR_THRESHOLD >= ROUND_CHUNK`.
    // So every chunk is whole and starts at an even index: no message pair straddles two chunks.
    let mut nf = Box::new_uninit_slice(half);
    let mut nb = Box::new_uninit_slice(half);
    // Why: each chunk folds, then accumulates its message, so the folded values are still in L1 when multiplied.
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
            fold(base, fc, bc);
            // SAFETY: the loop just wrote both windows.
            unsafe { fold_msg_terms(fc.assume_init_ref(), bc.assume_init_ref()) }
        },
        |(mut a0, mut a2), (c0, c2)| {
            a0 ^= c0;
            a2 ^= c2;
            (a0, a2)
        },
    );
    // SAFETY: the tasks wrote every slot of both, one output per pair of inputs.
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

// Lane rounds: the first `initial_k` rounds bind whole lanes, not adjacent words.
//
// The committed witness is lane-major: lane `l` is the stack block `q[l * H .. (l + 1) * H)`.
// Here `H = 2^(log_n - initial_k)`, and the layout makes the stack's zero padding whole lanes the commitment omits.
//
// - Round `j` binds lane bit `j`, pairing block `2i` with block `2i + 1` of the current buffer.
// - With an odd block count, the last block pairs with the absent zero padding.
// - After these rounds one `H`-word block is left, and every later round folds adjacent pairs.

/// The sum of the tasks' `(u_0, u_2)` accumulators, on the calling thread when there are few pairs.
///
/// Unreduced accumulators combine by XOR and reduction is linear, so both paths give the same message.
#[inline]
fn accumulate_msg<A: Copy + Send + BitXorAssign + Default>(
    n_tasks: usize,
    n_pairs: usize,
    task: impl Fn(usize) -> (A, A) + Sync,
) -> (A, A) {
    let xor = |(mut a0, mut a2): (A, A), (c0, c2): (A, A)| {
        a0 ^= c0;
        a2 ^= c2;
        (a0, a2)
    };
    if n_pairs < PAR_THRESHOLD {
        (0..n_tasks).map(task).fold((A::default(), A::default()), xor)
    } else {
        parallel::map_reduce(n_tasks, || (A::default(), A::default()), task, xor)
    }
}

/// Unreduced `(u_0, u_2)` over one pair of blocks, word `i` of one against word `i` of the other.
///
/// # Panics
///
/// If the four slices differ in length.
#[inline]
fn msg_terms_pair(f0: &[F192], f1: &[F192], b0: &[F192], b1: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let n = f0.len();
    assert!(f1.len() == n && b0.len() == n && b1.len() == n);
    pair_terms(n, |i| f0[i], |i| f1[i], |i| b0[i], |i| b1[i])
}

/// Unreduced `(u_0, u_2)` over a block whose partner is the absent zero padding.
///
/// With `f1 = b1 = 0`, both `h(0)` and `h(inf)` are `sum f0 * b0`.
/// So a lone block is not a no-op, unlike a trailing odd word in an adjacent-pair round.
#[inline]
fn msg_terms_lone(f0: &[F192], b0: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let mut u = F192Unreduced::ZERO;
    for (&x0, &y0) in f0.iter().zip(b0) {
        u ^= x0.mul_unreduced(y0);
    }
    (u, u)
}

/// The opening's initial weight, never stored whole.
///
/// - The first pass reads it one aligned chunk at a time.
/// - The first fold reads it folded over its lane bits, which its claims give in closed form.
pub(crate) trait InitialWeight: Sync {
    /// Writes the weights of words `start..start + out.len()` into `out`.
    ///
    /// The window is one chunk of `INITIAL_BASIS_CHUNK` words, aligned to its size.
    /// When a lane block is smaller than a chunk, the window is one whole block.
    fn fill(&self, start: usize, out: &mut [F192]);

    /// The weight folded over its lowest `|rs|` lane bits at the challenges `rs`, absent lanes counting as zero.
    ///
    /// ```text
    ///     word x of output block o  =  sum_j eq(rs, j) * w((o * 2^|rs| + j) * block + x)
    /// ```
    ///
    /// - `block` is the lane block length, and bit `i` of `j` meets `rs[i]`.
    /// - The output has `ceil(n_lanes / 2^|rs|)` blocks.
    fn fold_lanes(&self, rs: &[F192]) -> Vec<F192>;
}

/// The weight the opening's sumcheck folds against.
pub(crate) enum Basis<'a> {
    /// The initial weight, read by the first pass and folded by the first fold.
    Initial(&'a dyn InitialWeight),
    /// One E value per word, in memory: every weight after the first fold.
    Dense(Vec<F192>),
}

impl Basis<'_> {
    /// The weight in memory.
    ///
    /// # Panics
    ///
    /// Panics before the first fold.
    fn dense(&self) -> &Vec<F192> {
        match self {
            Basis::Dense(b) => b,
            Basis::Initial(_) => panic!("the initial weight is read folded"),
        }
    }

    /// The weight in memory, to update.
    ///
    /// # Panics
    ///
    /// Panics before the first fold.
    fn dense_mut(&mut self) -> &mut Vec<F192> {
        match self {
            Basis::Dense(b) => b,
            Basis::Initial(_) => panic!("the initial weight is read folded"),
        }
    }
}

/// Words a lane round's fold stages in L1 before publishing them.
const STAGE: usize = INITIAL_BASIS_CHUNK;

/// One lane round's witness fold, and the next round's message against the already folded weight `nb`.
///
/// # Arguments
///
/// - `n_out`: the number of output blocks, each of `block` words.
/// - `nb`: the folded weight, `n_out * block` words.
/// - `last`: the next round pairs adjacent words of the single output block, not two blocks.
/// - `fold_window(out_blk, x0, stage)`: writes the folded witness of words `x0..x0 + stage.len()` of block `out_blk`.
///
/// A task owns one `ROUND_CHUNK` window of one output pair of blocks, the unit the next message is local to.
///
/// The witness folds into an L1 stage, which the message reads, and the stage goes out by streaming stores.
/// Why: nothing reads the destination again before the next round.
///
/// # Panics
///
/// If `nb` is not `n_out * block` words, or if `last` is set with more than one output block.
fn fold_witness_and_msg(
    n_out: usize,
    block: usize,
    nb: &[F192],
    last: bool,
    fold_window: impl Fn(usize, usize, &mut [F192]) + Sync,
) -> (Vec<F192>, SumcheckMessage) {
    assert_eq!(nb.len(), n_out * block);
    // Adjacent pairing next round is only possible once the lanes have collapsed to a single block.
    assert!(!last || n_out == 1);

    let mut nf = Box::new_uninit_slice(n_out * block);
    let nf_base = SendPtr(nf.as_mut_ptr());
    let per = block.div_ceil(ROUND_CHUNK);
    let task = |t: usize| {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let stream = Stream::new();
        let mut stage = [[F192::ZERO; STAGE]; 2];
        let mut acc = (F192Unreduced::ZERO, F192Unreduced::ZERO);
        for s in (0..len).step_by(STAGE) {
            let n = STAGE.min(len - s);
            let [lo, hi] = &mut stage;
            // Fold one output block's window into the stage, then publish it.
            let fold = |out_blk: usize, stage: &mut [F192]| -> &[F192] {
                let at = out_blk * block + x0 + s;
                fold_window(out_blk, x0 + s, stage);
                // SAFETY: distinct `(out_blk, x0 + s)` name disjoint in-bounds windows of `nf`.
                // `nf` stays borrowed for the whole dispatch.
                unsafe { stream.write(nf_base.slice(at, n), stage) };
                &nb[at..at + n]
            };
            let lo_b = fold(2 * i, &mut lo[..n]);
            // The next round pairs output block `2i` with `2i + 1`, or a lone last block with zeros.
            let (u_0, u_2) = if 2 * i + 1 < n_out {
                let hi_b = fold(2 * i + 1, &mut hi[..n]);
                msg_terms_pair(&lo[..n], &hi[..n], lo_b, hi_b)
            } else if last {
                // `ROUND_CHUNK`, `STAGE` and `block` are powers of two, so every slice starts at an even word.
                // Its length is even too unless the block is one word, so no message pair straddles two slices.
                fold_msg_terms(&lo[..n], lo_b)
            } else {
                msg_terms_lone(&lo[..n], lo_b)
            };
            acc.0 ^= u_0;
            acc.1 ^= u_2;
        }
        acc
    };
    let (u_0, u_2) = accumulate_msg(n_out.div_ceil(2) * per, nb.len() / 2, task);
    // SAFETY: the tasks wrote every window of every output block once.
    let nf = unsafe { nf.assume_init() }.into_vec();
    (
        nf,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Folds the `K` witness over its lowest `|rs|` lane bits, and builds the next round's message against `nb`.
///
/// Output block `o` is `sum_j eq(rs, j) * f_(o * 2^|rs| + j)`, absent lanes counting as zero padding.
fn fold_lanes_base(f: &[F64], block: usize, rs: &[F192], nb: &[F192], last: bool) -> (Vec<F192>, SumcheckMessage) {
    let n_lanes = f.len() / block;
    let weights: Vec<LaneWeight> = eq_table(rs).into_iter().map(LaneWeight::new).collect();
    let n_out = n_lanes.div_ceil(weights.len());
    fold_witness_and_msg(n_out, block, nb, last, |out_blk, x0, stage| {
        let mut acc = WeightFold::default();
        let first = out_blk * weights.len();
        for (e, lane) in weights.iter().zip(first..n_lanes) {
            let src = lane * block + x0;
            acc.add_base(e, &f[src..src + stage.len()]);
        }
        acc.write(stage);
    })
}

/// Writes window `x0..x0 + stage.len()` of output block `out_blk` of `src` folded by one lane bit at `r`.
///
/// Block `2 out_blk` folds with block `2 out_blk + 1`, or with the absent zero padding when it is the last.
#[inline]
fn fold_block_pair(src: &[F192], block: usize, r: F192, out_blk: usize, x0: usize, stage: &mut [F192]) {
    let n = stage.len();
    let lo = &src[2 * out_blk * block + x0..][..n];
    if (2 * out_blk + 1) * block < src.len() {
        let hi = &src[(2 * out_blk + 1) * block + x0..][..n];
        fold_pairs(n, |i| lo[i], |i| hi[i], r, |i, v| stage[i] = v);
    } else {
        // No partner block: `x + r * (x + 0)`.
        for (d, &x) in stage.iter_mut().zip(lo) {
            *d = x + r * x;
        }
    }
}

/// The two-phase witness: the committed `K` words until the first fold, an `E` vector after it.
enum Witness<'a> {
    /// The caller's committed words, read only until the first fold.
    Base(&'a [F64]),
    /// The folded witness, shared with the level commitment that keeps it.
    Ext(Arc<Vec<F192>>),
}

/// The running sumcheck over the committed base witness and its folds in `E`.
pub(super) struct SumcheckProver<'a> {
    /// The witness, in `K` until the first fold and in `E` after it.
    f: Witness<'a>,
    /// The one combined weight: batching adds each new claim `tau` as `lambda^tau * b_new`.
    ///
    /// `tau` counts from 1, the running claim keeping `lambda^0 = 1`.
    combined_basis: Basis<'a>,
    /// The running claim: `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    /// The current round's quadratic.
    quad: RoundQuad,
    /// The number of rounds folded so far.
    round: usize,
    /// The first pass's sums, which give the first lane rounds' messages.
    initial: InitialRounds,
    /// The lane challenges drawn while those rounds defer their fold.
    lane_rs: Vec<F192>,
    /// The level's new claims, each its weight, claimed sum and quadratic, until the next batching.
    ///
    /// They come in Protocol 1 step 1 order: the out-of-domain claims, then the query batch.
    pending: Vec<(Vec<F192>, F192, RoundQuad)>,
}

impl<'a> SumcheckProver<'a> {
    /// The sumcheck of `sum_x f(x) * w(x) = h1`, and its first message.
    ///
    /// `block` is the lane block length `2^(log_n - initial_k)`.
    /// The first `initial_k` rounds are the lane fold, so round 0's message already pairs whole blocks.
    pub(super) fn new(
        f: &'a [F64],
        w: &'a dyn InitialWeight,
        h1: F192,
        block: usize,
        initial_k: usize,
    ) -> (Self, SumcheckMessage) {
        let initial = tracing::info_span!("First pass").in_scope(|| first_pass(f, block, initial_k, w));
        assert!(initial.rounds <= initial_k);
        let msg = initial.message(0, &[]);
        let inst = Self {
            f: Witness::Base(f),
            combined_basis: Basis::Initial(w),
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

    /// The base-two logarithm of the witness's length, rounded down, for the round spans.
    ///
    /// A lane round's length is `n_lanes * block`, generally not a power of two.
    fn log_size(&self) -> u32 {
        match &self.f {
            Witness::Base(f) => f.len().ilog2(),
            Witness::Ext(f) => f.len().ilog2(),
        }
    }

    /// One lane round at challenge `r`: folds block `2i` with block `2i + 1` and returns the next round's message.
    ///
    /// - With an odd block count, the last block folds with the absent zero padding.
    /// - `last` says the next round pairs adjacent words rather than blocks.
    /// - During the first pass's rounds the fold waits, and each message is interpolated from the pass's sums.
    /// - The last of those rounds folds all their lane bits at once.
    pub(super) fn fold_lane(&mut self, r: F192, block: usize, last: bool) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size = self.log_size()).entered();
        let (nf, nb, msg) = match (&self.f, &self.combined_basis) {
            (Witness::Base(f), Basis::Initial(w)) => {
                self.lane_rs.push(r);
                if self.round < self.initial.rounds {
                    let msg = self.initial.message(self.round, &self.lane_rs);
                    self.quad = RoundQuad::from_msg(msg, self.t_r);
                    return msg;
                }
                // The weight folds in closed form, the witness by its lanes' eq weights.
                let nb = tracing::info_span!("Fold weight").in_scope(|| w.fold_lanes(&self.lane_rs));
                let (nf, msg) = fold_lanes_base(f, block, &self.lane_rs, &nb, last);
                (nf, nb, msg)
            }
            (Witness::Ext(f), Basis::Dense(b)) => {
                let n_out = (f.len() / block).div_ceil(2);
                let nb = fold_blocks(b, block, r);
                let (nf, msg) = fold_witness_and_msg(n_out, block, &nb, last, |out_blk, x0, stage| {
                    fold_block_pair(f, block, r, out_blk, x0, stage);
                });
                (nf, nb, msg)
            }
            _ => unreachable!("the first fold lifts the witness and folds the initial weight together"),
        };
        self.f = Witness::Ext(Arc::new(nf));
        self.combined_basis = Basis::Dense(nb);
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// One adjacent-pair round at challenge `r`: folds the witness and the weight, and returns the next message.
    ///
    /// # Panics
    ///
    /// Panics before the first fold.
    pub(super) fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size = self.log_size()).entered();
        let (nf, nb, msg) = fold_and_msg_lsb(self.f_ext(), self.combined_basis.dense(), r);
        // Swap the folded buffers in and drop the consumed ones.
        // Why: the allocator then serves the next round's fold from their memory.
        drop(std::mem::replace(&mut self.f, Witness::Ext(Arc::new(nf))));
        drop(std::mem::replace(&mut self.combined_basis, Basis::Dense(nb)));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// Adds a claim with weight `b_new` and claimed sum `h_new`, and returns its message at the current round.
    ///
    /// The message is that of `sum_x f(x) * b_new(x)`; the claim joins the running one at the next batching.
    ///
    /// # Panics
    ///
    /// Before the first fold, or if `b_new` is not as long as the witness.
    pub(super) fn introduce_new(&mut self, b_new: Vec<F192>, h_new: F192) -> SumcheckMessage {
        let f = self.f_ext();
        assert_eq!(b_new.len(), f.len());
        let msg = round_msg_lsb(f, &b_new);
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        msg
    }

    /// Adds a claim with weight `b_new`, computing its claimed sum in the same pass as its message.
    ///
    /// Out-of-domain claims come only after the first fold, when the witness is already in `E`.
    ///
    /// # Panics
    ///
    /// Before the first fold, or if `b_new` is not as long as the witness.
    pub(super) fn introduce_new_with_eval(&mut self, b_new: Vec<F192>) -> (SumcheckMessage, F192) {
        let f = self.f_ext();
        assert_eq!(b_new.len(), f.len());
        let (msg, h_new) = round_msg_and_eval_lsb_ext(f, &b_new);
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        (msg, h_new)
    }

    /// Batches every claim added since the last batching into the running one, by powers of `lambda`.
    ///
    /// Claim `tau`, counting from 1, adds `lambda^tau * b_new` to the weight and `lambda^tau * h_new` to the claim.
    /// The running claim keeps `lambda^0 = 1` (PCS annex, Protocol 1 step 1).
    ///
    /// # Panics
    ///
    /// If no claim was added.
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

    /// The folded witness, always in `E`.
    ///
    /// # Panics
    ///
    /// Before the first fold; the base phase never reaches a commitment.
    pub(super) fn f_ext(&self) -> &[F192] {
        self.shared_ext()
    }

    /// The folded witness, shared: a later fold replaces it here but leaves it to its other holders.
    ///
    /// # Panics
    ///
    /// Before the first fold.
    pub(super) fn shared_ext(&self) -> &Arc<Vec<F192>> {
        match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
    }
}

/// An `E` vector of blocks folded by one lane bit at `r`: block `2i` with `2i + 1`, a lone last block with zeros.
fn fold_blocks(b: &[F192], block: usize, r: F192) -> Vec<F192> {
    let n_out = (b.len() / block).div_ceil(2);
    let mut out = vec![F192::ZERO; n_out * block];
    let chunk = block.min(ROUND_CHUNK);
    let per = block / chunk;
    let fold = |i: usize, dst: &mut [F192]| fold_block_pair(b, block, r, i / per, (i % per) * chunk, dst);
    if out.len() < PAR_THRESHOLD {
        out.chunks_mut(chunk).enumerate().for_each(|(i, dst)| fold(i, dst));
    } else {
        parallel::chunks_mut(&mut out, chunk, fold);
    }
    out
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::whir::config::INITIAL_FOLDING_FACTOR;
    use primitives::multilinear::inner_product;
    use primitives::test_util::Rng;

    /// An initial weight held whole, its lane fold the definition: the tests' stand-in for a regenerated one.
    pub(in crate::whir) struct Table {
        /// The weight, one value per word.
        pub(in crate::whir) weight: Vec<F192>,
        /// The lane block length.
        pub(in crate::whir) block: usize,
    }

    impl InitialWeight for Table {
        fn fill(&self, start: usize, out: &mut [F192]) {
            out.copy_from_slice(&self.weight[start..start + out.len()]);
        }

        fn fold_lanes(&self, rs: &[F192]) -> Vec<F192> {
            let eq = eq_table(rs);
            let lanes = self.weight.len() / self.block;
            let mut out = vec![F192::ZERO; lanes.div_ceil(eq.len()) * self.block];
            for (word, o) in out.iter_mut().enumerate() {
                let (group, x) = (word / self.block, word % self.block);
                for (lane, &e) in (group * eq.len()..lanes).zip(&eq) {
                    *o += e * self.weight[lane * self.block + x];
                }
            }
            out
        }
    }

    /// One lane bit folded the naive way: block `2i` with block `2i + 1`, the last with zeros.
    fn fold_lane_bit(v: &[F192], block: usize, r: F192) -> Vec<F192> {
        let lanes = v.len() / block;
        let mut out = vec![F192::ZERO; lanes.div_ceil(2) * block];
        for (word, o) in out.iter_mut().enumerate() {
            let (pair, x) = (word / block, word % block);
            let lo = v[2 * pair * block + x];
            let hi = if 2 * pair + 1 < lanes {
                v[(2 * pair + 1) * block + x]
            } else {
                F192::ZERO
            };
            *o = lo + r * (lo + hi);
        }
        out
    }

    /// A lane round's message the naive way: `h(0)` and `h(inf)` summed over block pairs, the last against zeros.
    fn lane_message(f: &[F192], b: &[F192], block: usize) -> SumcheckMessage {
        let lanes = f.len() / block;
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for pair in 0..lanes.div_ceil(2) {
            for x in 0..block {
                let lo = 2 * pair * block + x;
                let (f1, b1) = if 2 * pair + 1 < lanes {
                    (f[lo + block], b[lo + block])
                } else {
                    (F192::ZERO, F192::ZERO)
                };
                u_0 += f[lo] * b[lo];
                u_2 += (f[lo] + f1) * (b[lo] + b1);
            }
        }
        SumcheckMessage { u_0, u_2 }
    }

    /// An adjacent-pair round's message the naive way.
    fn pair_message(f: &[F192], b: &[F192]) -> SumcheckMessage {
        let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
        for (f, b) in f.chunks_exact(2).zip(b.chunks_exact(2)) {
            u_0 += f[0] * b[0];
            u_2 += (f[0] + f[1]) * (b[0] + b[1]);
        }
        SumcheckMessage { u_0, u_2 }
    }

    #[test]
    fn the_lane_rounds_are_one_bit_folds() {
        // Invariant: the first pass's interpolated messages and many-bit fold match folding one lane bit a round.
        // Invariant: so do the later lane rounds' single-bit folds.
        let mut rng = Rng::new(0xBA515);
        for initial_k in [1, 2, 3, PRECOMPUTED_ROUNDS, INITIAL_FOLDING_FACTOR] {
            let full = 1usize << initial_k;
            // Fixture state: blocks below and above one fill chunk and one task chunk.
            for block in [1, 16, INITIAL_BASIS_CHUNK, 2 * ROUND_CHUNK] {
                // Partial groups and odd counts meet the absent zero lanes.
                for lanes in [1, 2, 3, 5, full - 1, full, 37]
                    .into_iter()
                    .filter(|&l| l >= 1 && l <= full)
                {
                    let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                    let table = Table {
                        weight: rng.ext_vec(f.len()),
                        block,
                    };
                    let rs = rng.ext_vec(initial_k);
                    let label = format!("initial_k={initial_k}, block={block}, lanes={lanes}");

                    // The reference: lift, then one naive lane fold a round, the last handing over to adjacent pairs.
                    let mut nf: Vec<F192> = f.iter().map(|&w| F192::from(w)).collect();
                    let mut nb = table.weight.clone();
                    let mut expected = vec![lane_message(&nf, &nb, block)];
                    for (j, &r) in rs.iter().enumerate() {
                        nf = fold_lane_bit(&nf, block, r);
                        nb = fold_lane_bit(&nb, block, r);
                        expected.push(if j + 1 == initial_k {
                            pair_message(&nf, &nb)
                        } else {
                            lane_message(&nf, &nb, block)
                        });
                    }

                    let (mut sc, msg) = SumcheckProver::new(&f, &table, F192::ZERO, block, initial_k);
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

    #[test]
    fn the_folds_bind_the_rotated_point() {
        // Invariant: at the end, the witness and the weight are their MLEs at the challenges rotated by `initial_k`.
        // Why: that rotated point is the one the verifier evaluates its weight at.
        let mut rng = Rng::new(0x707A7E);
        let dense_mle = |table: &[F192], point: &[F192]| inner_product(table, &eq_table(point));
        // Fixture state: `log_n = 15` makes the lane block longer than one fold task.
        // Fixture state: lane counts below `2^initial_k` leave absent lanes, zero in the dense tables.
        for (log_n, initial_k, lanes) in [(9usize, 3usize, &[1usize, 5, 8][..]), (15, 3, &[3, 8][..])] {
            let block = 1usize << (log_n - initial_k);
            for &n_lanes in lanes {
                let used = n_lanes * block;
                let mut f = vec![F64::ZERO; 1 << log_n];
                f[..used].iter_mut().for_each(|w| *w = F64(rng.next_u64()));
                let mut b = vec![F192::ZERO; 1 << log_n];
                b[..used].copy_from_slice(&rng.ext_vec(used));

                let table = Table {
                    weight: b[..used].to_vec(),
                    block,
                };
                let (mut sc, _) = SumcheckProver::new(&f[..used], &table, F192::ZERO, block, initial_k);
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
