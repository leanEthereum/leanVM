// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The succinct verifier: it replays the transcript and checks the terminal
//! claim through closed forms, never materializing a weight.

use super::sample_queries_ordered;
use super::sumcheck::{RoundQuad, recv_quad};
use crate::merkle::Hash;
use crate::whir_config::VerifierConfig;
use crate::whir_induce::{eval_sk_at_vks, induce_sumcheck_enforced_sum, induce_sumcheck_evaluate_at_residual};
use fiat_shamir::transcript::{Receiver, TranscriptError};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::{eq_eval, eq_table, inner_product};
use thiserror::Error;

/// Why a WHIR opening is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum WhirError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The announced layout stores no lanes, or more than a leaf holds.
    #[error("{n_lanes} committed lanes, and a leaf holds 1 to {max}")]
    LaneCount { n_lanes: usize, max: usize },
    /// A level of the configuration does not fit the witness.
    #[error("level {level} of the configuration does not fit the witness")]
    InvalidShape { level: usize },
    /// The final folded value does not match the claimed evaluation.
    #[error("the final sumcheck claim does not match the opening")]
    TerminalMismatch,
}

/// An `E` row from the `F64` words its Merkle leaf is hashed from. The row was
/// already checked to be `3w` words wide, which is what makes the regrouping exact.
fn ext_row_from_words(words: &[F64]) -> Vec<F192> {
    words.chunks(3).map(|c| F192::new(c[0].0, c[1].0, c[2].0)).collect()
}

/// Pull the next Merkle phase, authenticated against `root`, and decode its
/// leaf words into the rows the level committed. `row_words` announces what the
/// proof stores and `leaf_words` the image it hashes to, which pins what the
/// octopus is checked against; they differ only at a padding-free L0, whose absent
/// lanes ride the image as a zero prefix. The decoded rows are full images.
fn recv_level_rows<T>(
    vs: &mut impl Receiver,
    root: &Hash,
    block_len: usize,
    queries: &[usize],
    row_words: usize,
    leaf_words: usize,
    decode: impl Fn(Vec<F64>) -> T,
) -> Result<Vec<T>, TranscriptError> {
    let rows = vs.next_merkle_batch(root, block_len, queries, row_words, leaf_words)?;
    Ok(rows.into_iter().map(decode).collect())
}

/// Decode for an L0 leaf image: the image is lane-DESCENDING, so that a
/// padding-free commitment's absent lanes are its leading words, and reversing it
/// puts stack block `b` back at index `b`, which is what the induce folds.
fn l0_row_ascending(mut row: Vec<F64>) -> Vec<F64> {
    row.reverse();
    row
}

/// The already-committed level whose rows the next query phase opens: its root
/// plus the shape both verifiers re-derive the block length and leaf width from.
struct PrevLevel {
    root: Hash,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

impl PrevLevel {
    #[inline]
    const fn block_len(&self) -> usize {
        1usize << (self.log_msg_cols + self.log_inv_rate)
    }

    #[inline]
    const fn num_interleaved(&self) -> usize {
        1usize << self.log_num_interleaved
    }

    /// Step to the level just committed, which folds `k_next` of the
    /// `n_current` remaining variables. `None` when the announced shape cannot
    /// hold them.
    fn advance(&mut self, root: Hash, k_next: usize, n_current: usize, log_inv_rate: usize) -> Option<()> {
        self.root = root;
        self.log_num_interleaved = k_next;
        self.log_msg_cols = n_current.checked_sub(k_next)?;
        self.log_inv_rate = log_inv_rate;
        Some(())
    }
}

/// Replay each fold challenge and its following round message, in prover order.
fn replay_fold_rounds(
    vs: &mut impl Receiver,
    k: usize,
    t_r: &mut F192,
    running_quad: &mut RoundQuad,
) -> Result<Vec<F192>, TranscriptError> {
    let mut rs = Vec::with_capacity(k);
    for _ in 0..k {
        let ri = vs.sample();
        rs.push(ri);
        *t_r = running_quad.eval(ri);
        *running_quad = recv_quad(vs, *t_r)?;
    }
    Ok(rs)
}

/// One replayed OOD claim: the point `z` it was taken at, its claimed value and
/// the intro message that carries it into the running sumcheck. Both are held
/// until the level's batching challenge is drawn (the prover holds the matching
/// basis pending, see the prover's `send_ood`).
struct OodReplay {
    z: Vec<F192>,
    y: F192,
    intro_quad: RoundQuad,
}

/// Replay one OOD claim: draw its point, then read its value and intro message.
fn replay_ood(vs: &mut impl Receiver, n_vars: usize) -> Result<OodReplay, TranscriptError> {
    let z = vs.sample_vec(n_vars);
    let y = vs.next_scalar()?;
    let intro_quad = recv_quad(vs, y)?;
    Ok(OodReplay { z, y, intro_quad })
}

/// Fold the level's pending claims into the running one with powers of its
/// batching challenge, in Protocol 1 step 1 order (the OOD claims, then the
/// query batch), and return the power each was scaled by, for the terminal
/// weight. The running claim keeps `lambda^0 = 1`.
fn batch_level_claims(
    lambda: F192,
    ood: &[OodReplay],
    query_intro: &RoundQuad,
    query_sum: F192,
    t_r: &mut F192,
    running_quad: &mut RoundQuad,
) -> (Vec<F192>, F192) {
    let mut scalar = F192::ONE;
    let mut ood_scalars = Vec::with_capacity(ood.len());
    for claim in ood {
        scalar *= lambda;
        *running_quad = RoundQuad::fold(running_quad, &claim.intro_quad, scalar);
        *t_r += scalar * claim.y;
        ood_scalars.push(scalar);
    }
    scalar *= lambda;
    *running_quad = RoundQuad::fold(running_quad, query_intro, scalar);
    *t_r += scalar * query_sum;
    (ood_scalars, scalar)
}

/// Succinct verifier for the recursive prover: instead of a dense
/// `b_initial` (2^log_n E-values) it takes a closure `eval_b_at` that evaluates
/// b's multilinear extension once, at the final fold point INDEXED BY WITNESS
/// COORDINATE: the fold challenges arrive in round order and the first `initial_k`
/// rounds are the lane fold, which binds the witness's top `initial_k` coords, so
/// the point is rotated left by `initial_k` before the closure sees it.
///
/// Per-level induced bases are never materialized: intro time uses the cheap
/// enforced-sum recomputation, and the residual uses the closed-form
/// `induce_sumcheck_evaluate_at_residual`. `log_n` is the committed
/// K-witness log size (b's logical dimension).
pub(crate) fn recursive_verifier_with_basis_succinct<F>(
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    target: F192,
    expected_initial_root: &Hash,
    eval_b_at: F,
    vs: &mut impl Receiver,
) -> Result<(), WhirError>
where
    // Called once at the terminal check with the full fold point.
    F: Fn(&[F192]) -> F192,
{
    let initial_k = config.initial_k();
    let r = config.level_steps();
    // The L0 rows the proof stores: the committed lanes, the rest of the leaf image
    // being the zero prefix the absent ones contribute. Derived from the announced
    // layout by the caller, so it is not the prover's to choose.
    let max = 1usize << initial_k;
    if n_lanes == 0 || n_lanes > max {
        return Err(WhirError::LaneCount { n_lanes, max });
    }

    // The caller already bound the root and claim values through the transcript.

    let log_inv_rate_0 = config.log_inv_rates()[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;

    let mut t_r = target;
    let mut running_quad = recv_quad(vs, t_r)?;

    let ood_count = |lvl: usize| -> usize { config.ood_samples()[lvl] };
    struct OodCtx {
        z: Vec<F192>,
        ris_start: usize,
        beta: F192,
    }
    let mut ood_ctxs: Vec<OodCtx> = Vec::new();

    let r_lane_fold = replay_fold_rounds(vs, initial_k, &mut t_r, &mut running_quad)?;

    let root_1 = vs.next_root()?;

    let mut level_ood = Vec::with_capacity(ood_count(1));
    for _ in 0..ood_count(1) {
        let ood = replay_ood(vs, log_n - initial_k)?;
        level_ood.push(ood);
    }

    // PoW grinding check for L0's query phase.
    vs.grind_check(config.grinding_bits()[0] as u32)?;

    let num_queries_0 = config.queries()[0];
    let queries_0 = sample_queries_ordered(vs, block_len_0, num_queries_0);
    let lambda_0 = vs.sample();
    let weights_0 = powers(lambda_0, num_queries_0);
    let ordered_rows_0 = recv_level_rows(
        vs,
        expected_initial_root,
        block_len_0,
        &queries_0,
        n_lanes,
        num_interleaved_0,
        l0_row_ascending,
    )?;

    // Compute enforced_sum cheaply at intro time. The induced basis poly's
    // residual evaluations are deferred to the final closed-form check.
    let n1 = log_n - initial_k;
    let enforced_sum_0 = induce_sumcheck_enforced_sum(&ordered_rows_0, &r_lane_fold, &queries_0, &weights_0);

    let intro_quad_0 = recv_quad(vs, enforced_sum_0)?;
    let (ood_scalars_0, query_scalar_0) = batch_level_claims(
        lambda_0,
        &level_ood,
        &intro_quad_0,
        enforced_sum_0,
        &mut t_r,
        &mut running_quad,
    );
    for (ood, scalar) in level_ood.into_iter().zip(ood_scalars_0) {
        ood_ctxs.push(OodCtx {
            z: ood.z,
            ris_start: initial_k,
            beta: scalar,
        });
    }

    // Per-level induced-basis evaluation context: small (no dense vec).
    struct LevelCtx {
        log_msg_cols: usize,
        queries: Vec<usize>,
        weights: Vec<F192>, // one power of the level's lambda per query
        ris_start: usize,
        beta: F192,
    }
    let mut level_ctxs: Vec<LevelCtx> = vec![LevelCtx {
        log_msg_cols: n1,
        queries: queries_0,
        weights: weights_0,
        ris_start: initial_k,
        beta: query_scalar_0,
    }];
    let mut ris = r_lane_fold;

    let mut prev = PrevLevel {
        root: root_1,
        log_num_interleaved: config.level_ks()[0],
        log_msg_cols: n1 - config.level_ks()[0],
        log_inv_rate: config.log_inv_rates()[1],
    };
    let mut n_current = n1;

    for i in 0..r {
        let k_i = config.level_ks()[i];
        if n_current < k_i {
            return Err(WhirError::InvalidShape { level: i });
        }
        let level_rs = replay_fold_rounds(vs, k_i, &mut t_r, &mut running_quad)?;
        ris.extend_from_slice(&level_rs);
        n_current -= k_i;

        if i == r - 1 {
            let yr = vs.next_scalars(1 << n_current)?;
            // PoW grinding check for the last level's query phase.
            vs.grind_check(config.grinding_bits()[i + 1] as u32)?;

            let num_queries_last = config.queries()[i + 1];
            let queries_last = sample_queries_ordered(vs, prev.block_len(), num_queries_last);
            // Batching challenge for the LAST commitment, sampled after `yr`
            // was observed and the queries are fixed, as the prover does.
            let lambda_last = vs.sample();
            let weights_last = powers(lambda_last, num_queries_last);
            let leaf_words = 3 * prev.num_interleaved();
            let ordered_rows_last = recv_level_rows(
                vs,
                &prev.root,
                prev.block_len(),
                &queries_last,
                leaf_words,
                leaf_words,
                |row| ext_row_from_words(&row),
            )?;

            let enforced_sum_last =
                induce_sumcheck_enforced_sum(&ordered_rows_last, &level_rs, &queries_last, &weights_last);
            let intro_quad_last = recv_quad(vs, enforced_sum_last)?;
            // No OOD at the final level: there is no new oracle to bind.
            let (_, query_scalar_last) = batch_level_claims(
                lambda_last,
                &[],
                &intro_quad_last,
                enforced_sum_last,
                &mut t_r,
                &mut running_quad,
            );
            level_ctxs.push(LevelCtx {
                log_msg_cols: n_current,
                queries: queries_last,
                weights: weights_last,
                ris_start: ris.len(),
                beta: query_scalar_last,
            });

            // Finish the sumcheck over the residual cube. Each basis and the
            // caller's weight are then evaluated once at `ris ++ ris_tail`.
            let yr_log_n = n_current;
            let mut ris_tail = Vec::with_capacity(yr_log_n);
            for j in 0..yr_log_n {
                let ri = vs.sample();
                t_r = running_quad.eval(ri);
                ris_tail.push(ri);
                if j + 1 < yr_log_n {
                    let q = recv_quad(vs, t_r)?;
                    running_quad = q;
                }
            }

            let mut weight = F192::ZERO;
            for ctx in &level_ctxs {
                if ctx.log_msg_cols < yr_log_n || ctx.ris_start + (ctx.log_msg_cols - yr_log_n) > ris.len() {
                    return Err(WhirError::InvalidShape { level: i });
                }
                let folded = ctx.log_msg_cols - yr_log_n;
                let mut point = ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
                point.extend_from_slice(&ris_tail);
                let at = induce_sumcheck_evaluate_at_residual(
                    ctx.log_msg_cols,
                    &eval_sk_at_vks(ctx.log_msg_cols),
                    &ctx.queries,
                    &ctx.weights,
                    &point,
                    0,
                );
                if at.len() != 1 {
                    return Err(WhirError::InvalidShape { level: i });
                }
                weight += ctx.beta * at[0];
            }
            for ctx in &ood_ctxs {
                if ctx.z.len() < yr_log_n || ctx.ris_start + (ctx.z.len() - yr_log_n) > ris.len() {
                    return Err(WhirError::InvalidShape { level: i });
                }
                let folded = ctx.z.len() - yr_log_n;
                let mut scalar = ctx.beta;
                for b in 0..folded {
                    scalar *= F192::ONE + ctx.z[b] + ris[ctx.ris_start + b];
                }
                weight += scalar * eq_eval(&ctx.z[folded..], &ris_tail);
            }

            // `ris ++ ris_tail` is the fold challenges in ROUND order, and the
            // first `initial_k` rounds are the lane fold, which binds the
            // committed witness's TOP `initial_k` variables (lane `l` is the
            // stack block `q[l·H ..)`). Rotating by `initial_k` re-indexes the
            // point by witness variable, which is the only thing this whole
            // relayout changes for a verifier: `eval_b_at` and every closed form
            // under it stay exactly as they were.
            let mut full_point = ris;
            full_point.extend_from_slice(&ris_tail);
            full_point.rotate_left(initial_k);
            weight += eval_b_at(&full_point);
            return if weight * inner_product(&yr, &eq_table(&ris_tail)) == t_r {
                Ok(())
            } else {
                Err(WhirError::TerminalMismatch)
            };
        }

        let root_next = vs.next_root()?;

        let mut level_ood = Vec::with_capacity(ood_count(i + 2));
        for _ in 0..ood_count(i + 2) {
            let ood = replay_ood(vs, n_current)?;
            level_ood.push(ood);
        }
        let ood_ris_start = ris.len();

        // PoW grinding check for this iteration's query phase.
        vs.grind_check(config.grinding_bits()[i + 1] as u32)?;

        let num_queries_i = config.queries()[i + 1];
        let queries_i = sample_queries_ordered(vs, prev.block_len(), num_queries_i);
        let lambda_i = vs.sample();
        let weights_i = powers(lambda_i, num_queries_i);
        let leaf_words = 3 * prev.num_interleaved();
        let ordered_rows_i = recv_level_rows(
            vs,
            &prev.root,
            prev.block_len(),
            &queries_i,
            leaf_words,
            leaf_words,
            |row| ext_row_from_words(&row),
        )?;

        let enforced_sum_i = induce_sumcheck_enforced_sum(&ordered_rows_i, &level_rs, &queries_i, &weights_i);

        let intro_quad_i = recv_quad(vs, enforced_sum_i)?;
        let (ood_scalars_i, query_scalar_i) = batch_level_claims(
            lambda_i,
            &level_ood,
            &intro_quad_i,
            enforced_sum_i,
            &mut t_r,
            &mut running_quad,
        );
        for (ood, scalar) in level_ood.into_iter().zip(ood_scalars_i) {
            ood_ctxs.push(OodCtx {
                z: ood.z,
                ris_start: ood_ris_start,
                beta: scalar,
            });
        }
        level_ctxs.push(LevelCtx {
            log_msg_cols: n_current,
            queries: queries_i,
            weights: weights_i,
            ris_start: ris.len(),
            beta: query_scalar_i,
        });

        if prev
            .advance(
                root_next,
                config.level_ks()[i + 1],
                n_current,
                config.log_inv_rates()[i + 2],
            )
            .is_none()
        {
            return Err(WhirError::InvalidShape { level: i });
        }
    }

    unreachable!()
}
