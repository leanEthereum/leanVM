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

use super::Hiding;
use crate::verifier::OpeningVerifier;
use crate::whir::config::{Config, ConfigError};
use crate::whir::query::{Normalizers, padding_shift};
use fiat_shamir::transcript::TranscriptError;
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
}

/// A round's quadratic `c + b X + a X^2`.
#[derive(Clone, Copy)]
struct Quad<E> {
    /// The constant coefficient.
    c: E,
    /// The linear coefficient.
    b: E,
    /// The quadratic coefficient.
    a: E,
}

/// An out-of-domain claim on a level's oracle: its point, its value, and its intro round.
struct Ood<E> {
    /// The sampled point.
    z: Vec<E>,
    /// The claimed value of the folded witness at `z`.
    y: E,
    /// The claim's first round polynomial.
    intro: Quad<E>,
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
struct WhirReplay<'c, V: OpeningVerifier> {
    /// The opening's configuration.
    config: &'c Config,
    /// The running claim.
    t_r: V::E,
    /// The current round's quadratic.
    quad: Quad<V::E>,
    /// Every fold challenge so far, in round order.
    ris: Vec<V::E>,
    /// Every query batch's contribution to the terminal weight.
    levels: Vec<LevelCtx<V::Query, V::E>>,
    /// Every OOD claim's contribution to the terminal weight.
    oods: Vec<OodCtx<V::E>>,
}

/// The level-0 rows a query batch opened, one per query, of committed words.
struct BaseRows<K>(Vec<Vec<K>>);

/// A hiding opening's padding folded by the lane challenges, `g_1`, past lanes of `2^log_msg_cols` words, and its factor's shift [`padding_shift`].
struct FoldedPadding<E> {
    g1: Vec<E>,
    log_msg_cols: usize,
    shift: F64,
}

/// A later level's rows a query batch opened, one per query, of elements of `E`.
struct ExtRows<E>(Vec<Vec<E>>);

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
/// With `hiding` the commitment is a hiding one: after the lane fold's last challenge the verifier turns hiding off, reads and checks the revealed running claim if `hidden_claim`, then reads the padding's lane fold `g_1`, which each level-0 query takes off its folded row.
///
/// # Errors
///
/// - A lane count a leaf cannot hold, or a configuration that does not fit the witness.
/// - A malformed stream, a revealed claim the lane fold does not reach, or a terminal claim the opening does not reproduce.
#[expect(
    clippy::too_many_arguments,
    reason = "The verifier keeps its independent inputs explicit, as the prover does."
)]
pub(crate) fn verify<V: OpeningVerifier>(
    v: &mut V,
    config: &Config,
    log_n: usize,
    n_lanes: usize,
    target: V::E,
    root: V::Root,
    hiding: Option<Hiding>,
    weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
) -> Result<(), WhirError> {
    WhirReplay::run(v, config, log_n, n_lanes, target, root, hiding, weight_at)
}

impl<E: Copy> Quad<E> {
    /// The next round's quadratic, its linear coefficient fixed by the running claim.
    fn recv<V: OpeningVerifier<E = E>>(v: &mut V, claim: E) -> Result<Self, TranscriptError> {
        let h = v.next_round_poly(3, claim, None)?;
        Ok(Self {
            c: h[0],
            b: h[1],
            a: h[2],
        })
    }

    /// The quadratic at `x`, by Horner's rule.
    fn eval<V: OpeningVerifier<E = E>>(self, v: &mut V, x: E) -> E {
        let u = v.mul_add(self.a, x, self.b);
        v.mul_add(u, x, self.c)
    }

    /// `self + s * other`.
    fn fold<V: OpeningVerifier<E = E>>(self, v: &mut V, other: Self, s: E) -> Self {
        Self {
            c: v.mul_add(s, other.c, self.c),
            b: v.mul_add(s, other.b, self.b),
            a: v.mul_add(s, other.a, self.a),
        }
    }
}

impl<E: Copy> Ood<E> {
    /// Draw an out-of-domain point, then read its value and its intro round.
    fn replay<V: OpeningVerifier<E = E>>(v: &mut V, n_vars: usize) -> Result<Self, TranscriptError> {
        let z = v.sample_vec(n_vars);
        let y = v.next_scalar()?;
        let intro = Quad::recv(v, y)?;
        Ok(Self { z, y, intro })
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
        let normalizers = Normalizers::new(self.log_msg_cols);
        let sks = normalizers.at_roots();
        // Each factor is affine in `s`: `1 + p (1 + s / sigma) = (1 + p) + (p / sigma) s`.
        let lin: Vec<(E, E)> = (point.iter().zip(normalizers.inverses()))
            .map(|(&p, &inv)| (v.add_const(p, F192::ONE), v.mul_const(p, F192::from(inv))))
            .collect();
        let zero = v.zero();
        (self.queries.iter().zip(&self.weights)).fold(zero, |acc, (query, &w)| {
            let mut s = v.query_point(query);
            let mut product = v.one();
            for (k, &(a, c)) in lin.iter().enumerate() {
                if k > 0 {
                    // The subspace polynomials' recurrence `s_k = s_{k-1}^2 + s_{k-1}(v_{k-1}) s_{k-1}`.
                    let u = v.mul_const(s, F192::from(sks[k - 1]));
                    s = v.mul_add(s, s, u);
                }
                let f = v.mul_add(c, s, a);
                product = v.mul(product, f);
            }
            v.mul_add(w, product, acc)
        })
    }
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
        let rows = v.open_rows(&self.root, self.depth(), queries, leaf_words, leaf_words)?;
        let rows = (rows.into_iter())
            .map(|words| words.chunks(3).map(|c| v.e_of_limbs([c[0], c[1], c[2]])).collect())
            .collect();
        Ok(ExtRows(rows))
    }
}

impl<'c, V: OpeningVerifier> WhirReplay<'c, V> {
    /// Replay the whole opening, then check the terminal claim.
    ///
    /// The caller's weight is evaluated once, at the terminal point indexed by witness coordinate.
    ///
    /// # Errors
    ///
    /// Returns the errors listed on the opening's entry point.
    #[expect(
        clippy::too_many_arguments,
        reason = "The verifier keeps its independent inputs explicit, as the prover does."
    )]
    fn run(
        v: &mut V,
        config: &'c Config,
        log_n: usize,
        n_lanes: usize,
        target: V::E,
        root: V::Root,
        hiding: Option<Hiding>,
        weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
    ) -> Result<(), WhirError> {
        let initial_k = config.initial_k();
        let max = 1usize << initial_k;
        if n_lanes == 0 || n_lanes > max {
            return Err(WhirError::LaneCount { n_lanes, max });
        }
        let quad = Quad::recv(v, target)?;
        let mut w = Self {
            config,
            t_r: target,
            quad,
            ris: Vec::new(),
            levels: Vec::new(),
            oods: Vec::new(),
        };
        let mut n_current = log_n
            .checked_sub(initial_k)
            .ok_or(WhirError::InvalidShape { level: 0 })?;
        // The lane fold, the padding revealed between its last challenge and the round after it.
        let mut lane_fold = w.fold_rounds(v, initial_k - 1)?;
        lane_fold.push(w.fold_challenge(v));
        let padding = match hiding {
            Some(h) => Some(w.reveal(v, h, n_current)?),
            None => None,
        };
        w.quad = Quad::recv(v, w.t_r)?;
        let root_1 = v.next_root()?;
        let oods = (0..config.ood_samples()[1])
            .map(|_| Ood::replay(v, n_current))
            .collect::<Result<_, _>>()?;
        let phase = w.phase(0, n_current + config.log_inv_rates()[0]);
        // The proof stores the committed lanes, the image's tail, lane-descending.
        // Reversed, block `b` sits at index `b`.
        w.query(v, phase, oods, n_current, |v, queries, weights| {
            let mut rows = v.open_rows(&root, phase.depth, queries, n_lanes, max)?;
            for row in &mut rows {
                row.reverse();
            }
            Ok(BaseRows(rows).enforced_sum(v, &lane_fold, weights, queries, padding.as_ref()))
        })?;

        let mut oracle = w.oracle(root_1, 0, n_current)?;
        for i in 0..config.level_steps() {
            let k = config.level_ks()[i];
            if n_current < k {
                return Err(WhirError::InvalidShape { level: i });
            }
            let level_rs = w.fold_rounds(v, k)?;
            n_current -= k;
            if i + 1 == config.level_steps() {
                return w.last_level(v, &oracle, &level_rs, n_current, weight_at);
            }
            let root = v.next_root()?;
            let oods = (0..config.ood_samples()[i + 2])
                .map(|_| Ood::replay(v, n_current))
                .collect::<Result<_, _>>()?;
            let phase = w.phase(i + 1, oracle.depth());
            w.query(v, phase, oods, n_current, |v, queries, weights| {
                let rows = oracle.open_e_rows(v, queries)?;
                Ok(rows.enforced_sum(v, &level_rs, weights))
            })?;
            oracle = w.oracle(root, i + 1, n_current)?;
        }
        unreachable!("the configuration has at least one level")
    }

    /// Level `level`'s query batch over indices of `depth` bits.
    fn phase(&self, level: usize, depth: usize) -> QueryPhase {
        QueryPhase {
            grinding: u32::try_from(self.config.grinding_bits()[level]).expect("a few grinding bits"),
            depth,
            count: self.config.queries()[level],
        }
    }

    /// The oracle a level's fold commits, on the variables left after it.
    ///
    /// # Errors
    ///
    /// Returns the level when the oracle's interleaving exceeds the variables left.
    fn oracle(&self, root: V::Root, level: usize, n_current: usize) -> Result<Oracle<V::Root>, WhirError> {
        let k = self.config.level_ks()[level];
        Ok(Oracle {
            root,
            log_num_interleaved: k,
            log_msg_cols: n_current.checked_sub(k).ok_or(WhirError::InvalidShape { level })?,
            log_inv_rate: self.config.log_inv_rates()[level + 1],
        })
    }

    /// `k` fold rounds: each draws a challenge, evaluates the running quadratic there, and reads the next one.
    ///
    /// # Errors
    ///
    /// Returns an error past the end of the stream.
    fn fold_rounds(&mut self, v: &mut V, k: usize) -> Result<Vec<V::E>, TranscriptError> {
        let mut rs = Vec::with_capacity(k);
        for _ in 0..k {
            rs.push(self.fold_challenge(v));
            self.quad = Quad::recv(v, self.t_r)?;
        }
        Ok(rs)
    }

    /// A fold round's challenge, and the running claim it takes the round's quadratic to.
    fn fold_challenge(&mut self, v: &mut V) -> V::E {
        let ri = v.sample();
        self.t_r = self.quad.eval(v, ri);
        self.ris.push(ri);
        ri
    }

    /// What a hiding opening reveals after the lane fold: with `hidden_claim`, the running claim in the clear, which must be the one the rounds reached; then the padding's lane fold.
    fn reveal(&mut self, v: &mut V, hiding: Hiding, log_msg_cols: usize) -> Result<FoldedPadding<V::E>, WhirError> {
        if hiding.hidden_claim {
            v.set_hidden(false);
            let a = v.next_scalar()?;
            v.ensure_eq(self.t_r, a, || WhirError::RevealedClaim)?;
            self.t_r = a;
        }
        Ok(FoldedPadding {
            g1: v.next_scalars(self.config.padding())?,
            log_msg_cols,
            shift: padding_shift(log_msg_cols, self.config.log_inv_rates()[0]),
        })
    }

    /// One query batch, then the batching of the level's claims.
    ///
    /// Transcript order:
    ///
    /// 1. check the proof of work,
    /// 2. draw the queries, then the batching challenge `lambda`,
    /// 3. `enforced` opens the queries and returns their `lambda`-weighted sum at the level's fold point,
    /// 4. read the consistency claims' intro round.
    ///
    /// The running claim keeps `lambda^0`, each OOD claim takes the next power, and the query batch the one after.
    ///
    /// # Errors
    ///
    /// Returns a failed proof of work, a missing or unauthenticated opening, or the end of the stream.
    fn query(
        &mut self,
        v: &mut V,
        phase: QueryPhase,
        oods: Vec<Ood<V::E>>,
        log_msg_cols: usize,
        enforced: impl FnOnce(&mut V, &[V::Query], &[V::E]) -> Result<V::E, TranscriptError>,
    ) -> Result<(), TranscriptError> {
        v.grind_check(phase.grinding)?;
        let queries = phase.sample(v);
        let lambda = v.sample();
        let weights = v.powers(lambda, phase.count);
        let sum = v.scope("rows", |v| enforced(v, &queries, &weights))?;
        let intro = Quad::recv(v, sum)?;

        // Batch the OOD claims, then the query batch, each at the next power of the level's challenge.
        let ris_start = self.ris.len();
        let mut scalar = v.one();
        for ood in oods {
            scalar = v.mul(scalar, lambda);
            self.quad = self.quad.fold(v, ood.intro, scalar);
            self.t_r = v.mul_add(scalar, ood.y, self.t_r);
            self.oods.push(OodCtx {
                z: ood.z,
                ris_start,
                beta: scalar,
            });
        }
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
        oracle: &Oracle<V::Root>,
        level_rs: &[V::E],
        n_current: usize,
        weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
    ) -> Result<(), WhirError> {
        let yr = v.next_scalars(1 << n_current)?;
        let phase = self.phase(self.config.level_steps(), oracle.depth());
        self.query(v, phase, Vec::new(), n_current, |v, queries, weights| {
            let rows = oracle.open_e_rows(v, queries)?;
            Ok(rows.enforced_sum(v, level_rs, weights))
        })?;
        let mut ris_tail = Vec::with_capacity(n_current);
        for j in 0..n_current {
            let ri = v.sample();
            self.t_r = self.quad.eval(v, ri);
            ris_tail.push(ri);
            if j + 1 < n_current {
                self.quad = Quad::recv(v, self.t_r)?;
            }
        }
        v.scope("terminal", |v| self.terminal(v, &yr, &ris_tail, weight_at))
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
        yr: &[V::E],
        ris_tail: &[V::E],
        weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
    ) -> Result<(), WhirError> {
        let tail = ris_tail.len();
        let zero = v.zero();
        let mut weight = zero;
        for ctx in &self.levels {
            let folded = ctx.log_msg_cols - tail;
            let mut point = self.ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
            point.extend_from_slice(ris_tail);
            let at = ctx.basis_at(v, &point);
            weight = v.mul_add(ctx.beta, at, weight);
        }
        for ctx in &self.oods {
            let folded = ctx.z.len() - tail;
            let at = self.ris[ctx.ris_start..ctx.ris_start + folded].iter().chain(ris_tail);
            let mut scalar = ctx.beta;
            for (&z, &x) in ctx.z.iter().zip(at) {
                let s = v.add(z, x);
                scalar = v.times_one_plus(scalar, s);
            }
            weight = v.add(weight, scalar);
        }
        // Why rotate: `ris ++ ris_tail` is the fold challenges in round order.
        // - The first `initial_k` rounds are the lane fold, which binds the witness's top `initial_k` variables.
        // - Rotating left by `initial_k` indexes the point by witness variable, as the caller's weight expects.
        let mut full_point = self.ris.clone();
        full_point.extend_from_slice(ris_tail);
        full_point.rotate_left(self.config.initial_k());
        let caller = weight_at(v, &full_point);
        let weight = v.add(weight, caller);
        let folded_yr = v.mle(yr, ris_tail);
        let lhs = v.mul(weight, folded_yr);
        v.ensure_eq(lhs, self.t_r, || WhirError::TerminalMismatch)
    }
}

impl<K: Copy> BaseRows<K> {
    /// The level-0 enforced sum over rows of `K`: `sum_i w_i (<row_i, eq(point, .)> + p(q_i))`, `p` the padding's share of the folded codeword, if any.
    ///
    /// Each row's inner product is taken alone, then scaled by its weight.
    /// So the first query's weight, one, costs no product in rows.
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
        (rows.iter().zip(weights).zip(queries)).fold(zero, |acc, ((row, &w), query)| {
            let start = padding.map_or(zero, |p| p.at(v, query));
            let inner = (eq.iter().zip(row)).fold(start, |s, (&e, &k)| v.mul_k_add(e, k, s));
            v.mul_add(w, inner, acc)
        })
    }
}

impl<E: Copy> FoldedPadding<E> {
    /// `W_m(x + s) sum_j g_1[j] X_j(x)` at a query's point `x`: the padding's share of the folded codeword there, which taking off (adding, in characteristic two) leaves the folded message's codeword.
    ///
    /// `X_j` is the product of the normalized subspace polynomials `W_b` over the bits `b` of `j`, so the sum folds the top bit of `j` at a time.
    fn at<V: OpeningVerifier<E = E>>(&self, v: &mut V, query: &V::Query) -> E {
        let m = self.log_msg_cols;
        let normalizers = Normalizers::new(m);
        let (sks, inverses) = (normalizers.at_roots(), normalizers.inverses());
        let normalize = |v: &mut V, s: E, b: usize| v.mul_const(s, F192::from(inverses[b]));
        // `W_b(x)` for the bits of `j < k`, then `W_m(x)`, by the recurrence of `LevelCtx::basis_at`.
        let bits = self.g1.len().next_power_of_two().trailing_zeros() as usize;
        let mut s = v.query_point(query);
        let mut w = Vec::with_capacity(bits);
        for b in 0..=m {
            if b > 0 {
                let u = v.mul_const(s, F192::from(sks[b - 1]));
                s = v.mul_add(s, s, u);
            }
            if b < bits {
                w.push(normalize(v, s, b));
            }
        }
        let w_m = normalize(v, s, m);
        let w_m = v.add_const(w_m, F192::from(self.shift));
        let mut g = self.g1.clone();
        while g.len() > 1 {
            let half = g.len().next_power_of_two() >> 1;
            let w_b = w[half.trailing_zeros() as usize];
            for j in 0..g.len() - half {
                g[j] = v.mul_add(w_b, g[j + half], g[j]);
            }
            g.truncate(half);
        }
        match g.first() {
            Some(&p) => v.mul(w_m, p),
            None => v.zero(),
        }
    }
}

impl<E: Copy> ExtRows<E> {
    /// A later level's enforced sum over rows of `E`: `sum_l eq(point, l) sum_i w_i row_i[l]`.
    fn enforced_sum<V: OpeningVerifier<E = E>>(&self, v: &mut V, point: &[E], weights: &[E]) -> E {
        let rows = &self.0;
        let eq = v.eq_table_prefix(point, rows[0].len());
        let zero = v.zero();
        (eq.iter().enumerate()).fold(zero, |acc, (l, &e)| {
            let column = (rows.iter().zip(weights)).fold(zero, |s, (row, &w)| v.mul_add(w, row[l], s));
            v.mul_add(e, column, acc)
        })
    }
}
