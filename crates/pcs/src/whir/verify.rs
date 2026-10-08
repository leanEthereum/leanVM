// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The succinct verifier: it replays the transcript and checks the terminal claim through closed forms, never materializing a weight.
//!
//! It is written once over the opening verifier's operations, so the native verifier and the recursion machine's rows run the same steps.
//! Every query opens a full row whose path follows the query's bits, so the rows never depend on which rows are opened.

use crate::verifier::OpeningVerifier;
use crate::whir::config::{ConfigError, VerifierConfig};
use crate::whir::induce::eval_sk_at_vks;
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
    LaneCount { n_lanes: usize, max: usize },
    /// A level of the configuration does not fit the witness.
    #[error("level {level} of the configuration does not fit the witness")]
    InvalidShape { level: usize },
    /// The opening has no ring-switched claim.
    #[error("the opening has no ring-switched claim")]
    NoRingClaim,
    /// A ring-switched region is no aligned slice of the committed cube, or a claim on it does not span it.
    #[error("ring-switched region {index} is no aligned slice of the cube spanned by its claims")]
    Region { index: usize },
    /// A point claim is not an aligned slice of the committed cube, or its strided slot is out of range.
    #[error("point claim {index} has an invalid aligned range or strided slot")]
    PointClaim { index: usize },
    /// The final folded value does not match the claimed evaluation.
    #[error("the final sumcheck claim does not match the opening")]
    TerminalMismatch,
}

/// A round's quadratic `c + b X + a X^2`.
#[derive(Clone, Copy)]
struct Quad<E> {
    c: E,
    b: E,
    a: E,
}

/// An out-of-domain claim on a level's oracle: its point, its value, and its intro round.
struct Ood<E> {
    z: Vec<E>,
    y: E,
    intro: Quad<E>,
}

/// What a level's query batch leaves for the terminal weight.
struct LevelCtx<Q, E> {
    log_msg_cols: usize,
    queries: Vec<Q>,
    /// One power of the level's batching challenge per query.
    weights: Vec<E>,
    /// Where the level's fold challenges start among all of them.
    ris_start: usize,
    /// The level's power in the running claim.
    beta: E,
}

/// What an out-of-domain claim leaves for the terminal weight.
struct OodCtx<E> {
    z: Vec<E>,
    ris_start: usize,
    beta: E,
}

/// The oracle the next query batch opens.
struct Oracle<R> {
    root: R,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

/// One level's query batch: its grinding, its index width and its count.
#[derive(Clone, Copy)]
struct QueryPhase {
    grinding: u32,
    depth: usize,
    count: usize,
}

/// The succinct WHIR verifier's state.
struct WhirReplay<'c, V: OpeningVerifier> {
    config: &'c VerifierConfig,
    /// The running claim and its round's quadratic.
    t_r: V::E,
    quad: Quad<V::E>,
    /// Every fold challenge, in round order.
    ris: Vec<V::E>,
    levels: Vec<LevelCtx<V::Query, V::E>>,
    oods: Vec<OodCtx<V::E>>,
}

/// The level-0 rows a query batch opened, one per query, of committed words.
struct BaseRows<K>(Vec<Vec<K>>);

/// A later level's rows a query batch opened, one per query, of elements of `E`.
struct ExtRows<E>(Vec<Vec<E>>);

/// Succinct verifier for the recursive prover, against a weight `b` over the `2^log_n` committed words.
///
/// It takes no dense weight: `weight_at` evaluates b's multilinear extension once, at the final fold point indexed by witness coordinate.
/// The fold challenges arrive in round order, and the first `initial_k` rounds, the lane fold, bind the witness's top `initial_k` coordinates.
/// So the point is rotated left by `initial_k` before the closure sees it.
///
/// Per-level induced bases are never materialized: a level's enforced sum is recomputed from its opened rows, and its basis taken in closed form at the terminal point.
/// The L0 rows the proof stores are the committed lanes, `n_lanes` of them, which the caller derives from the announced layout.
///
/// # Errors
///
/// Returns a lane count a leaf cannot hold, a configuration that does not fit the witness, a malformed stream, or a terminal claim the opening does not reproduce.
pub(crate) fn recursive_verifier_with_basis_succinct<V: OpeningVerifier>(
    v: &mut V,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    target: V::E,
    root: V::Root,
    weight_at: impl FnOnce(&mut V, &[V::E]) -> V::E,
) -> Result<(), WhirError> {
    WhirReplay::run(v, config, log_n, n_lanes, target, root, weight_at)
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

    fn eval<V: OpeningVerifier<E = E>>(self, v: &mut V, x: E) -> E {
        let u = v.mul_add(self.a, x, self.b);
        v.mul_add(u, x, self.c)
    }

    /// `self + s·other`.
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
    /// The level's induced basis at `point`: `sum_i w_i prod_k (1 + p_k (1 + s_k(q_i) / s_k(v_k)))`, `q_i` the query index in `K`.
    fn basis_at<V: OpeningVerifier<E = E, Query = Q>>(&self, v: &mut V, point: &[E]) -> E {
        assert_eq!(point.len(), self.log_msg_cols, "a point of the level's cube");
        let sks = eval_sk_at_vks(self.log_msg_cols);
        // `1 + p (1 + s / sigma) = (1 + p) + (p / sigma) s`.
        let lin: Vec<(E, E)> = (point.iter().zip(&sks))
            .map(|(&p, &sigma)| {
                let inv = if sigma == F64(0) { F64(0) } else { sigma.inv() };
                (v.add_const(p, F192::ONE), v.mul_const(p, F192::from(inv)))
            })
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
    /// The succinct WHIR verifier.
    ///
    /// The caller's weight is evaluated once, at the terminal point indexed by witness coordinate.
    fn run(
        v: &mut V,
        config: &'c VerifierConfig,
        log_n: usize,
        n_lanes: usize,
        target: V::E,
        root: V::Root,
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
        let lane_fold = w.fold_rounds(v, initial_k)?;
        let root_1 = v.next_root()?;
        let oods = (0..config.ood_samples()[1])
            .map(|_| Ood::replay(v, n_current))
            .collect::<Result<_, _>>()?;
        let phase = w.phase(0, n_current + config.log_inv_rates()[0]);
        // The proof stores the committed lanes, the image's tail; the image is lane-descending.
        w.query(v, phase, oods, n_current, |v, queries, weights| {
            let mut rows = v.open_rows(&root, phase.depth, queries, n_lanes, max)?;
            for row in &mut rows {
                row.reverse();
            }
            Ok(BaseRows(rows).enforced_sum(v, &lane_fold, weights))
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
    fn oracle(&self, root: V::Root, level: usize, n_current: usize) -> Result<Oracle<V::Root>, WhirError> {
        let k = self.config.level_ks()[level];
        Ok(Oracle {
            root,
            log_num_interleaved: k,
            log_msg_cols: n_current.checked_sub(k).ok_or(WhirError::InvalidShape { level })?,
            log_inv_rate: self.config.log_inv_rates()[level + 1],
        })
    }

    /// `k` fold rounds: each draws a challenge, evaluates the running quadratic, and reads the next.
    fn fold_rounds(&mut self, v: &mut V, k: usize) -> Result<Vec<V::E>, TranscriptError> {
        let mut rs = Vec::with_capacity(k);
        for _ in 0..k {
            let ri = v.sample();
            self.t_r = self.quad.eval(v, ri);
            self.quad = Quad::recv(v, self.t_r)?;
            rs.push(ri);
        }
        self.ris.extend_from_slice(&rs);
        Ok(rs)
    }

    /// One query batch: grind, draw the queries and their batching challenge, open them, then batch the level's claims.
    ///
    /// `enforced` opens the queries and returns their weighted sum at the level's fold point.
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

        // The OOD claims, then the query batch, each at the next power of the level's challenge.
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

    /// `weight · <yr, eq(ris_tail)> = t_r`, the weight every level's basis, every OOD claim and the caller's at the full point.
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
        // `ris ++ ris_tail` is the fold challenges in ROUND order, and the first `initial_k` rounds are the lane fold,
        // which binds the committed witness's TOP `initial_k` variables (lane `l` is the stack block `q[l·H ..)`).
        // Rotating by `initial_k` re-indexes the point by witness variable, so the caller's weight is in witness coordinates.
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
    /// The level-0 enforced sum over `K` rows: `sum_i w_i <row_i, eq(v, .)>`.
    ///
    /// Each row's inner product is its own, so the first query's weight, one, costs no product in rows.
    fn enforced_sum<V: OpeningVerifier<K = K>>(&self, v: &mut V, point: &[V::E], weights: &[V::E]) -> V::E {
        let rows = &self.0;
        let eq = v.eq_table_prefix(point, rows[0].len());
        let zero = v.zero();
        (rows.iter().zip(weights)).fold(zero, |acc, (row, &w)| {
            let inner = (eq.iter().zip(row)).fold(zero, |s, (&e, &k)| v.mul_k_add(e, k, s));
            v.mul_add(w, inner, acc)
        })
    }
}

impl<E: Copy> ExtRows<E> {
    /// A later level's enforced sum over `E` rows: `sum_l eq(v, l) sum_i w_i row_i[l]`.
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
