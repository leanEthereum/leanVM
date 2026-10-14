// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The succinct WHIR verifier.
//!
//! It replays the transcript and checks the terminal claim through closed forms, never building a weight.
//!
//! It is written once over the opening verifier's operations.
//! So the native verifier and the recursion machine's rows run the same steps.
//!
//! Every query opens a full row along the path its bits name.
//! So the recursion machine's rows never depend on which codeword rows are opened.

use crate::ntt::NovelBasis;
use crate::verifier::OpeningVerifier;
use crate::whir::config::{Config, ConfigError};
use crate::whir::query::Padding;
use crate::whir::sumcheck::RoundQuad;
use fiat_shamir::TranscriptError;
use fiat_shamir::arith::{Arith, Stage};
use primitives::field::{F64, F192};
use thiserror::Error;

/// Why a WHIR opening is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum WhirError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The opening's size and rate have no configuration.
    #[error(transparent)]
    Config(#[from] ConfigError),
    /// The announced layout stores no lanes, or more than a leaf holds.
    #[error("{n_lanes} committed lanes, and a leaf holds 1 to {max}")]
    LaneCount {
        /// The announced number of committed lanes.
        n_lanes: usize,
        /// The lanes a leaf holds.
        max: usize,
    },
    /// A level of the configuration does not fit the witness.
    #[error("level {level} of the configuration does not fit the witness")]
    InvalidShape {
        /// The index of the level that does not fit.
        level: usize,
    },
    /// The immutable commitment record has a different shape or domain context.
    #[error("the immutable commitment record does not match its public context")]
    CommitmentMismatch,
    /// A hiding commitment received as an anchored one, an anchored one as a hiding one, or opened by a weighted claim.
    ///
    /// A hiding commitment has no anchor: its value would publish an evaluation of the hidden stack.
    #[error("a hiding commitment has no anchor, and an anchored one opens through its statement")]
    Anchoring,
    /// The opening has no ring-switched claim.
    #[error("the opening has no ring-switched claim")]
    NoRingClaim,
    /// A ring-switched region is no aligned slice of the committed cube, or a claim on it does not span it.
    #[error("ring-switched region {index} is no aligned slice of the cube spanned by its claims")]
    Region {
        /// The region's position in the statement.
        index: usize,
    },
    /// A point claim reaches past the committed cube.
    #[error("point claim {index} reaches past the committed cube")]
    PointClaim {
        /// The claim's position in the statement.
        index: usize,
    },
    /// The final folded value does not match the claimed evaluation.
    #[error("the final sumcheck claim does not match the opening")]
    TerminalMismatch,
    /// The running claim a hiding opening reveals after the lane fold is not the one its rounds reach.
    #[error("the revealed running claim does not match the lane fold")]
    RevealedClaim,
    /// A weighted claim's weight is no power of two of committed words.
    #[error("a weighted claim's weight is no power of two of committed words")]
    WeightedClaim,
}

/// An out-of-domain claim on a level's oracle: its point, its value, and its intro round.
struct Ood<E> {
    /// The sampled point.
    z: Vec<E>,
    /// The claimed value of the folded witness at `z`.
    y: E,
    /// The claim's first round polynomial.
    intro: RoundQuad<E>,
}

/// What a level's query batch leaves for the terminal weight.
struct LevelCtx<Q, E> {
    /// Variables of the folded witness the batch's claims are on.
    log_msg_cols: usize,
    /// The query positions, in query order.
    queries: Vec<Q>,
    /// One power of the level's batching challenge per query.
    weights: Vec<E>,
    /// Where the fold challenges after the batch start among all of them.
    ris_start: usize,
    /// The level's power in the running claim.
    beta: E,
}

/// What an out-of-domain claim leaves for the terminal weight.
struct OodCtx<E> {
    /// The claim's point.
    z: Vec<E>,
    /// Where the fold challenges after the claim start among all of them.
    ris_start: usize,
    /// The claim's power in the running claim.
    beta: E,
}

/// The oracle the next query batch opens.
struct Oracle<R> {
    /// Its Merkle root.
    root: R,
    /// Log of the elements of `E` in one row.
    log_num_interleaved: usize,
    /// Log of the message length of each lane.
    log_msg_cols: usize,
    /// Its code's inverse-rate logarithm.
    log_inv_rate: usize,
}

/// One level's query batch: its grinding, its index width and its count.
#[derive(Clone, Copy)]
struct QueryPhase {
    /// Proof-of-work bits checked before the queries are drawn.
    grinding: u32,
    /// Bits of a query position.
    depth: usize,
    /// Queries in the batch.
    count: usize,
}

/// The succinct WHIR verifier's state.
///
/// It holds no borrow: the configuration is passed to each step that reads it.
struct WhirReplay<V: OpeningVerifier> {
    /// The running claim.
    t_r: V::E,
    /// The current round's quadratic.
    quad: RoundQuad<V::E>,
    /// Every fold challenge so far, in round order.
    ris: Vec<V::E>,
    /// Every query batch's contribution to the terminal weight.
    levels: Vec<LevelCtx<V::Query, V::E>>,
    /// Every OOD claim's contribution to the terminal weight.
    oods: Vec<OodCtx<V::E>>,
}

/// The level-0 rows a query batch opened, one per query, of committed words.
struct BaseRows<K>(Vec<Vec<K>>);

/// A hiding opening's padding, folded by the lane challenges.
struct FoldedPadding<E> {
    /// The fold `g_1`, one element per padding coefficient.
    g1: Vec<E>,
    /// The padding, whose share each query takes off.
    padding: Padding,
}

/// A later level's rows a query batch opened, one per query, of elements of `E`.
struct ExtRows<E>(Vec<Vec<E>>);

impl<E: Copy> Ood<E> {
    /// Draw an out-of-domain point, then read its value and its intro round.
    fn replay<V: OpeningVerifier<E = E>>(v: &mut V, n_vars: usize) -> Result<Self, TranscriptError> {
        let z = v.verifier_messages(n_vars);
        let y = v.prover_message()?;
        let intro = RoundQuad::read(v, y)?;
        Ok(Self { z, y, intro })
    }

    /// Replay `count` out-of-domain claims in order, stopping at the first malformed one.
    ///
    /// An explicit loop rather than a collecting closure, so no closure captures the verifier.
    fn replay_all<V: OpeningVerifier<E = E>>(
        v: &mut V,
        count: usize,
        n_vars: usize,
    ) -> Result<Vec<Self>, TranscriptError> {
        let mut oods = Vec::new();
        let mut i = 0;
        while i < count {
            oods.push(Self::replay(v, n_vars)?);
            i += 1;
        }
        Ok(oods)
    }
}

impl<E: Copy> OodCtx<E> {
    /// `beta * prod_j (1 + z_j + x_j)`, with `x` the fold challenges `head` then `tail`, over the common length.
    ///
    /// It needs only arithmetic, so it is generic over `Arith` rather than the opening verifier.
    fn term<A: Arith<E = E>>(&self, a: &mut A, head: &[E], tail: &[E]) -> E {
        let n = self.z.len().min(head.len() + tail.len());
        let mut scalar = self.beta;
        let mut j = 0;
        while j < n {
            let x = if j < head.len() { head[j] } else { tail[j - head.len()] };
            let s = a.add(self.z[j], x);
            scalar = a.times_one_plus(scalar, s);
            j += 1;
        }
        scalar
    }
}

impl<Q, E: Copy> LevelCtx<Q, E> {
    /// The multilinear extension of the level's induced basis at `point`, in closed form.
    ///
    /// ```text
    ///     sum_i w_i prod_k (1 + p_k (1 + s_k(q_i) / s_k(v_k)))
    /// ```
    ///
    /// Here `q_i` is query `i`'s position read as an element of `K`, and `s_k` the `k`-th subspace polynomial.
    fn basis_at<V: OpeningVerifier<E = E, Query = Q>>(&self, v: &mut V, point: &[E]) -> E {
        assert_eq!(point.len(), self.log_msg_cols, "a point of the level's cube");
        let basis = NovelBasis::new(self.log_msg_cols);
        // Each factor is affine in `s`: `1 + p (1 + s / sigma) = (1 + p) + (p / sigma) s`.
        let lin = affine_factors(v, point, basis.inverses());
        let zero = v.zero();
        let mut acc = zero;
        for i in 0..self.queries.len().min(self.weights.len()) {
            let s = v.query_point(&self.queries[i]);
            let product = basis_product(v, &lin, &basis, s);
            acc = v.mul_add(self.weights[i], product, acc);
        }
        acc
    }
}

// The basis loops need only arithmetic, so they are generic over `Arith` and take the basis by reference.

/// The affine factors `(1 + p_k, p_k / s_k(v_k))`, one per coordinate of the point.
fn affine_factors<E: Copy, A: Arith<E = E>>(a: &mut A, point: &[E], inverses: &[F64]) -> Vec<(E, E)> {
    let mut lin = Vec::with_capacity(point.len());
    let mut k = 0;
    while k < point.len() {
        let p = point[k];
        let one_plus = a.add_const(p, F192::ONE);
        let c = a.mul_const(p, F192::from(inverses[k]));
        lin.push((one_plus, c));
        k += 1;
    }
    lin
}

/// One query's product `prod_k ((1 + p_k) + (p_k / s_k(v_k)) s_k(q))`, from `s_0(q) = s`.
fn basis_product<E: Copy, A: Arith<E = E>>(a: &mut A, lin: &[(E, E)], basis: &NovelBasis, mut s: E) -> E {
    let mut product = a.one();
    let mut k = 0;
    while k < lin.len() {
        let (one_plus, c) = lin[k];
        if k > 0 {
            s = basis.next(a, s, k - 1);
        }
        let f = a.mul_add(c, s, one_plus);
        product = a.mul(product, f);
        k += 1;
    }
    product
}

impl QueryPhase {
    /// The batch's queries.
    fn sample<V: OpeningVerifier>(self, v: &mut V) -> Vec<V::Query> {
        v.sample_queries(self.depth, self.count)
    }
}

impl<R> Oracle<R> {
    /// The width of a query's index bits.
    const fn depth(&self) -> usize {
        self.log_msg_cols + self.log_inv_rate
    }

    /// Open each query's row of `E` elements, three words each.
    fn open_e_rows<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        queries: &[V::Query],
    ) -> Result<ExtRows<V::E>, TranscriptError> {
        let leaf_words = 3 << self.log_num_interleaved;
        let words = v.open_rows(&self.root, self.depth(), queries, leaf_words, leaf_words)?;
        let mut rows = Vec::with_capacity(words.len());
        let mut q = 0;
        while q < words.len() {
            rows.push(e_row(v, &words[q]));
            q += 1;
        }
        Ok(ExtRows(rows))
    }
}

/// A row of `E` elements from its words, three limbs each, lowest first.
fn e_row<E, K: Copy, V: OpeningVerifier<E = E, K = K>>(v: &mut V, words: &[K]) -> Vec<E> {
    let n = words.len().div_ceil(3);
    let mut row = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let at = 3 * i;
        row.push(v.e_of_limbs([words[at], words[at + 1], words[at + 2]]));
        i += 1;
    }
    row
}

/// A caller's terminal weight, evaluated once with static dispatch.
/// The consumed provider keeps borrowed statement data within verification's lifetime without allocating a callback.
/// The element type is a parameter, so the call's point and value name it directly rather than through `V`.
pub(crate) trait WeightAt<E, V: OpeningVerifier<E = E>> {
    fn call(self, v: &mut V, point: &[E]) -> E;
}

/// A query batch whose rows scope has begun but whose sum is not yet replayed.
struct PendingQuery<Q, E> {
    /// The query positions, in query order.
    queries: Vec<Q>,
    /// One power of the batching challenge per query.
    weights: Vec<E>,
    /// The batching challenge.
    lambda: E,
}

/// Verify `sum_x f(x) * w(x) = target` for the witness `f` of `2^log_n` words committed at `root`.
///
/// It takes no dense weight: `weight_at` evaluates the multilinear extension of `w` once, at the terminal point.
/// That point is indexed by witness coordinate.
///
/// # Why the point is rotated
///
/// - The fold challenges arrive in round order.
/// - The first `initial_k` rounds, the lane fold, bind the witness's top `initial_k` coordinates.
/// - So the point is rotated left by `initial_k` before `weight_at` sees it.
///
/// # What is never built
///
/// - A level's induced weight: its sum is recomputed from its opened rows, its value taken in closed form.
/// - The absent lanes: the L0 rows the proof stores are the `n_lanes` committed ones.
///
/// Under a configuration that pads, the commitment is a hiding one, and after the lane fold's last challenge:
///
/// - a transcript still hidden is revealed: the verifier reads the running claim and checks it;
/// - it reads the padding's lane fold, and each level-0 query takes the padding's share off its folded row.
///
/// # Errors
///
/// - A lane count a leaf cannot hold, or a configuration that does not fit the witness.
/// - A malformed stream, a revealed claim the lane fold does not reach, or a terminal claim the opening does not reproduce.
pub(crate) fn verify<V: OpeningVerifier>(
    v: &mut V,
    config: &Config,
    log_n: usize,
    n_lanes: usize,
    target: V::E,
    root: V::Root,
    weight_at: impl WeightAt<V::E, V>,
) -> Result<(), WhirError> {
    // The typed wrapper checks shape before reading its record frame; keep
    // direct internal callers safe too, without duplicating record binding.
    check_config_shape(config, log_n)?;
    let initial_k = config.initial_k();
    let max = 1usize << initial_k;
    if n_lanes == 0 || n_lanes > max {
        return Err(WhirError::LaneCount { n_lanes, max });
    }
    let quad = RoundQuad::read(v, target)?;
    let mut w = WhirReplay {
        t_r: target,
        quad,
        ris: Vec::new(),
        levels: Vec::new(),
        oods: Vec::new(),
    };
    let mut n_current = log_n
        .checked_sub(initial_k)
        .ok_or(WhirError::InvalidShape { level: 0 })?;
    // The lane fold.
    // A hiding opening reveals between its last challenge and the next round's message.
    let mut lane_fold = w.fold_rounds(v, initial_k - 1)?;
    lane_fold.push(w.fold_challenge(v));
    let padding = if config.padding() > 0 {
        Some(w.reveal(v, config, n_current)?)
    } else {
        None
    };
    w.quad = RoundQuad::read(v, w.t_r)?;
    let root_1 = v.next_root()?;
    let oods = Ood::replay_all(v, config.ood_samples()[1], n_current)?;
    let phase = WhirReplay::<V>::phase(config, 0, n_current + config.log_inv_rates()[0]);
    // The proof stores the committed lanes, the image's tail, lane-descending.
    // Reversed, block `b` sits at index `b`.
    let batch = WhirReplay::begin_query(v, phase)?;
    let sum = match v.open_rows(&root, phase.depth, &batch.queries, n_lanes, max) {
        Ok(mut rows) => {
            let mut r = 0;
            while r < rows.len() {
                rows[r].reverse();
                r += 1;
            }
            Ok(BaseRows(rows).enforced_sum(v, &lane_fold, &batch.weights, &batch.queries, padding.as_ref()))
        }
        Err(error) => Err(error),
    };
    w.finish_query(v, batch, oods, n_current, sum)?;

    let mut oracle = WhirReplay::<V>::oracle(config, root_1, 0, n_current)?;
    for i in 0..config.level_steps() {
        let k = config.level_ks()[i];
        if n_current < k {
            return Err(WhirError::InvalidShape { level: i });
        }
        let level_rs = w.fold_rounds(v, k)?;
        n_current -= k;
        if i + 1 == config.level_steps() {
            return w.last_level(v, config, &oracle, &level_rs, n_current, weight_at);
        }
        let root = v.next_root()?;
        let oods = Ood::replay_all(v, config.ood_samples()[i + 2], n_current)?;
        let phase = WhirReplay::<V>::phase(config, i + 1, oracle.depth());
        let batch = WhirReplay::begin_query(v, phase)?;
        let sum = match oracle.open_e_rows(v, &batch.queries) {
            Ok(rows) => Ok(rows.enforced_sum(v, &level_rs, &batch.weights)),
            Err(error) => Err(error),
        };
        w.finish_query(v, batch, oods, n_current, sum)?;
        oracle = WhirReplay::<V>::oracle(config, root, i + 1, n_current)?;
    }
    unreachable!("the configuration has at least one level")
}

/// Check all source-dependent dimensions before shifts, reads or challenges.
pub(crate) fn check_config_shape(config: &Config, log_n: usize) -> Result<(), WhirError> {
    let bits = usize::BITS as usize;
    let initial_k = config.initial_k();
    if log_n >= bits || log_n <= initial_k {
        return Err(WhirError::InvalidShape { level: 0 });
    }
    let mut remaining = log_n - initial_k;
    if !remaining
        .checked_add(config.log_inv_rates()[0])
        .is_some_and(|depth| depth < bits)
    {
        return Err(WhirError::InvalidShape { level: 0 });
    }
    let mut level = 0;
    let mut result = Ok(());
    while level < config.level_ks().len() && result.is_ok() {
        let k = config.level_ks()[level];
        // An extension-field row holds three base words per interleaved value.
        if k >= bits - 2 {
            result = Err(WhirError::InvalidShape { level });
        } else {
            match remaining.checked_sub(k) {
                None => result = Err(WhirError::InvalidShape { level }),
                Some(next) => {
                    remaining = next;
                    if !remaining
                        .checked_add(config.log_inv_rates()[level + 1])
                        .is_some_and(|depth| depth > 0 && depth < bits)
                    {
                        result = Err(WhirError::InvalidShape { level });
                    }
                }
            }
        }
        level += 1;
    }
    result
}

impl<V: OpeningVerifier> WhirReplay<V> {
    /// Level `level`'s query batch over indices of `depth` bits.
    fn phase(config: &Config, level: usize, depth: usize) -> QueryPhase {
        // The message `expect` would print, spelled out so the panic formats nothing.
        let Ok(grinding) = u32::try_from(config.grinding_bits()[level]) else {
            panic!("a few grinding bits: TryFromIntError(())")
        };
        QueryPhase {
            grinding,
            depth,
            count: config.queries()[level],
        }
    }

    /// The oracle a level's fold commits, on the variables left after it.
    ///
    /// # Errors
    ///
    /// Returns the level when the oracle's interleaving exceeds the variables left.
    fn oracle(config: &Config, root: V::Root, level: usize, n_current: usize) -> Result<Oracle<V::Root>, WhirError> {
        let k = config.level_ks()[level];
        Ok(Oracle {
            root,
            log_num_interleaved: k,
            log_msg_cols: n_current.checked_sub(k).ok_or(WhirError::InvalidShape { level })?,
            log_inv_rate: config.log_inv_rates()[level + 1],
        })
    }

    /// `k` fold rounds: each draws a challenge, evaluates the running quadratic there, and reads the next one.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the proof.
    fn fold_rounds(&mut self, v: &mut V, k: usize) -> Result<Vec<V::E>, TranscriptError> {
        let mut rs = Vec::with_capacity(k);
        for _ in 0..k {
            rs.push(self.fold_challenge(v));
            self.quad = RoundQuad::read(v, self.t_r)?;
        }
        Ok(rs)
    }

    /// A fold round's challenge, and the running claim it takes the round's quadratic to.
    fn fold_challenge(&mut self, v: &mut V) -> V::E {
        let ri = v.verifier_message();
        self.t_r = self.quad.eval(v, ri);
        self.ris.push(ri);
        ri
    }

    /// What a hiding opening reveals after the lane fold.
    ///
    /// - A transcript still hidden is revealed: the running claim, in the clear, must be the one the rounds reached.
    /// - Then the padding's lane fold.
    fn reveal(&mut self, v: &mut V, config: &Config, log_msg_cols: usize) -> Result<FoldedPadding<V::E>, WhirError> {
        if v.is_hidden() {
            // Every message from here on is public.
            v.set_hidden(false);
            let a = v.prover_message()?;
            v.ensure_eq(self.t_r, a, || WhirError::RevealedClaim)?;
            self.t_r = a;
        }
        Ok(FoldedPadding {
            g1: v.prover_messages(config.padding())?,
            padding: Padding::new(log_msg_cols, config.log_inv_rates()[0]),
        })
    }

    /// Begin a query batch: check the proof of work, draw the queries, then the batching challenge `lambda` and its powers, then begin the rows scope.
    ///
    /// The caller opens the queries and computes their `lambda`-weighted sum at the level's fold point before [`Self::finish_query`] ends the scope.
    ///
    /// # Errors
    ///
    /// Returns a failed proof of work.
    fn begin_query(v: &mut V, phase: QueryPhase) -> Result<PendingQuery<V::Query, V::E>, TranscriptError> {
        v.check_pow(phase.grinding)?;
        let queries = phase.sample(v);
        let lambda = v.verifier_message();
        let weights = v.powers(lambda, phase.count);
        v.begin_scope(Stage::Rows);
        Ok(PendingQuery {
            queries,
            weights,
            lambda,
        })
    }

    /// End the rows scope even on an opening failure, then read the consistency claims' intro round and batch the level's claims.
    ///
    /// The running claim keeps `lambda^0`, each OOD claim takes the next power, and the query batch the one after.
    ///
    /// # Errors
    ///
    /// Returns a missing or unauthenticated opening, or the end of the proof.
    fn finish_query(
        &mut self,
        v: &mut V,
        batch: PendingQuery<V::Query, V::E>,
        oods: Vec<Ood<V::E>>,
        log_msg_cols: usize,
        sum: Result<V::E, TranscriptError>,
    ) -> Result<(), TranscriptError> {
        v.end_scope();
        let sum = sum?;
        let PendingQuery {
            queries,
            weights,
            lambda,
        } = batch;
        let intro = RoundQuad::read(v, sum)?;

        // Batch the OOD claims, then the query batch, each at the next power of the level's challenge.
        let ris_start = self.ris.len();
        let mut scalar = batch_oods(
            v,
            oods,
            lambda,
            ris_start,
            &mut self.quad,
            &mut self.t_r,
            &mut self.oods,
        );
        scalar = v.mul(scalar, lambda);
        self.quad = self.quad.fold(v, intro, scalar);
        self.t_r = v.mul_add(scalar, sum, self.t_r);
        self.levels.push(LevelCtx {
            log_msg_cols,
            queries,
            weights,
            ris_start,
            beta: scalar,
        });
        Ok(())
    }

    /// The last level: its residual polynomial, its query batch, the residual rounds, then the terminal check.
    ///
    /// The last residual round reads no polynomial: the terminal check evaluates `yr` at the final point instead.
    ///
    /// # Errors
    ///
    /// Returns a malformed stream or a terminal mismatch.
    fn last_level(
        mut self,
        v: &mut V,
        config: &Config,
        oracle: &Oracle<V::Root>,
        level_rs: &[V::E],
        n_current: usize,
        weight_at: impl WeightAt<V::E, V>,
    ) -> Result<(), WhirError> {
        let yr = v.prover_messages(1 << n_current)?;
        let phase = Self::phase(config, config.level_steps(), oracle.depth());
        let batch = Self::begin_query(v, phase)?;
        let sum = match oracle.open_e_rows(v, &batch.queries) {
            Ok(rows) => Ok(rows.enforced_sum(v, level_rs, &batch.weights)),
            Err(error) => Err(error),
        };
        self.finish_query(v, batch, Vec::new(), n_current, sum)?;
        let mut ris_tail = Vec::with_capacity(n_current);
        for j in 0..n_current {
            let ri = v.verifier_message();
            self.t_r = self.quad.eval(v, ri);
            ris_tail.push(ri);
            if j + 1 < n_current {
                self.quad = RoundQuad::read(v, self.t_r)?;
            }
        }
        v.begin_scope(Stage::Terminal);
        let result = self.terminal(v, config, &yr, &ris_tail, weight_at);
        v.end_scope();
        result
    }

    /// Check `weight * <yr, eq(ris_tail)> = t_r`.
    ///
    /// `weight` is the batched weight at the full point.
    /// It sums each level's induced basis and each OOD claim's `eq(z, .)`, each at its power, and the caller's weight.
    ///
    /// # Errors
    ///
    /// Returns a terminal mismatch.
    fn terminal(
        &self,
        v: &mut V,
        config: &Config,
        yr: &[V::E],
        ris_tail: &[V::E],
        weight_at: impl WeightAt<V::E, V>,
    ) -> Result<(), WhirError> {
        let tail = ris_tail.len();
        let zero = v.zero();
        let mut weight = zero;
        for i in 0..self.levels.len() {
            let ctx = &self.levels[i];
            let folded = ctx.log_msg_cols - tail;
            let mut point = self.ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
            point.extend_from_slice(ris_tail);
            let at = ctx.basis_at(v, &point);
            weight = v.mul_add(ctx.beta, at, weight);
        }
        weight = add_ood_terms(v, &self.oods, &self.ris, ris_tail, weight);
        // Why rotate: `ris ++ ris_tail` is the fold challenges in round order.
        // - The first `initial_k` rounds are the lane fold, which binds the witness's top `initial_k` variables.
        // - Rotating left by `initial_k` indexes the point by witness variable, as the caller's weight expects.
        let mut full_point = self.ris.clone();
        full_point.extend_from_slice(ris_tail);
        full_point.rotate_left(config.initial_k());
        let caller = weight_at.call(v, &full_point);
        let weight = v.add(weight, caller);
        let folded_yr = v.mle(yr, ris_tail);
        let lhs = v.mul(weight, folded_yr);
        v.ensure_eq(lhs, self.t_r, || WhirError::TerminalMismatch)
    }
}

impl<K: Copy> BaseRows<K> {
    /// The level-0 enforced sum over rows of `K`.
    ///
    /// ```text
    ///     sum_i w_i (<row_i, eq(point, .)> + p(q_i))
    /// ```
    ///
    /// `p` is the padding's share of the folded codeword, zero without padding.
    ///
    /// Each row's inner product is taken alone, then scaled by its weight.
    /// So the first query's weight, one, costs no product in rows.
    #[expect(
        clippy::option_if_let_else,
        reason = "a closure would capture the verifier, which the extraction does not translate"
    )]
    fn enforced_sum<V: OpeningVerifier<K = K>>(
        &self,
        v: &mut V,
        point: &[V::E],
        weights: &[V::E],
        queries: &[V::Query],
        padding: Option<&FoldedPadding<V::E>>,
    ) -> V::E {
        let rows = &self.0;
        let eq = v.eq_table_prefix(point, rows[0].len());
        let zero = v.zero();
        let mut acc = zero;
        let mut i = 0;
        while i < rows.len().min(weights.len()).min(queries.len()) {
            let start = match padding {
                Some(p) => {
                    let x = v.query_point(&queries[i]);
                    p.padding.share(v, x, &p.g1)
                }
                None => zero,
            };
            let inner = base_inner(v, &eq, &rows[i], start);
            acc = v.mul_add(weights[i], inner, acc);
            i += 1;
        }
        acc
    }
}

/// Batch the OOD claims in order, each at the next power of `lambda`: fold its intro round into `quad` and its value into `t_r`, and record its context.
///
/// Returns the last power taken, one when there is no claim.
/// It needs only arithmetic, so it is generic over `Arith`, and the loop runs under no borrow of the replay.
fn batch_oods<E: Copy, A: Arith<E = E>>(
    a: &mut A,
    oods: Vec<Ood<E>>,
    lambda: E,
    ris_start: usize,
    quad: &mut RoundQuad<E>,
    t_r: &mut E,
    ctxs: &mut Vec<OodCtx<E>>,
) -> E {
    let mut scalar = a.one();
    for ood in oods {
        scalar = a.mul(scalar, lambda);
        *quad = quad.fold(a, ood.intro, scalar);
        *t_r = a.mul_add(scalar, ood.y, *t_r);
        ctxs.push(OodCtx {
            z: ood.z,
            ris_start,
            beta: scalar,
        });
    }
    scalar
}

/// `start + sum_j eq_j k_j` over the common length, one `mul_k_add` per term in order.
fn base_inner<E: Copy, K: Copy, V: OpeningVerifier<E = E, K = K>>(v: &mut V, eq: &[E], row: &[K], start: E) -> E {
    let mut s = start;
    let mut j = 0;
    while j < eq.len().min(row.len()) {
        s = v.mul_k_add(eq[j], row[j], s);
        j += 1;
    }
    s
}

impl<E: Copy> ExtRows<E> {
    /// A later level's enforced sum over rows of `E`: `sum_l eq(point, l) sum_i w_i row_i[l]`.
    fn enforced_sum<V: OpeningVerifier<E = E>>(&self, v: &mut V, point: &[E], weights: &[E]) -> E {
        let rows = &self.0;
        let eq = v.eq_table_prefix(point, rows[0].len());
        let zero = v.zero();
        ext_sum(v, rows, weights, &eq, zero)
    }
}

/// `zero + sum_l eq_l column_l`, in order; it needs only `Arith`.
fn ext_sum<E: Copy, A: Arith<E = E>>(a: &mut A, rows: &[Vec<E>], weights: &[E], eq: &[E], zero: E) -> E {
    let mut acc = zero;
    let mut l = 0;
    while l < eq.len() {
        let column = ext_column(a, rows, weights, l, zero);
        acc = a.mul_add(eq[l], column, acc);
        l += 1;
    }
    acc
}

/// `zero + sum_i w_i row_i[l]` over the common length of `rows` and `weights`, in order.
fn ext_column<E: Copy, A: Arith<E = E>>(a: &mut A, rows: &[Vec<E>], weights: &[E], l: usize, zero: E) -> E {
    let mut s = zero;
    let mut i = 0;
    while i < rows.len().min(weights.len()) {
        s = a.mul_add(weights[i], rows[i][l], s);
        i += 1;
    }
    s
}

/// `weight + sum_j term_j` over the OOD claims in order, each at its suffix of the fold challenges; it needs only `Arith`.
fn add_ood_terms<E: Copy, A: Arith<E = E>>(
    a: &mut A,
    oods: &[OodCtx<E>],
    ris: &[E],
    ris_tail: &[E],
    mut weight: E,
) -> E {
    let tail = ris_tail.len();
    let mut i = 0;
    while i < oods.len() {
        let ctx = &oods[i];
        let folded = ctx.z.len() - tail;
        let scalar = ctx.term(a, &ris[ctx.ris_start..ctx.ris_start + folded], ris_tail);
        weight = a.add(weight, scalar);
        i += 1;
    }
    weight
}
