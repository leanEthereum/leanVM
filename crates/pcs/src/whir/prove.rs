// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The WHIR prover, level by level.
//!
//! ```text
//!     lane fold   initial_k rounds over the witness's top variables
//!     L1 commit   its root, then its OOD claims
//!     L0 queries  grinding, positions, batching challenge, opened rows, consistency claim
//!     level i     k_i fold rounds, then L(i+1)'s commit and OOD claims, then level i's queries
//!     last level  k fold rounds, the residual in the clear, its queries, then the residual rounds
//! ```

use crate::whir::commit::{BaseCommitment, LevelCommitment};
use crate::whir::config::Config;
use crate::whir::query::{Padding, QueryBatch, sample_queries};
use crate::whir::sumcheck::{InitialWeight, NextRound, SumcheckProver};
use fiat_shamir::ProverState;
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;

/// One level's query batch: its positions, and the powers of its batching challenge that weigh them.
struct LevelQueries {
    /// The positions, in transcript order, repeats included.
    positions: Vec<usize>,
    /// The batching challenge, whose powers batch the level's claims.
    lambda: F192,
    /// One power of the batching challenge per query.
    weights: Vec<F192>,
}

impl LevelQueries {
    /// Grind, sample `count` positions of `depth` bits, then draw the batching challenge.
    ///
    /// The challenge comes once every claim it batches is fixed: the level's OOD claims and these positions.
    fn draw(ps: &mut ProverState, grinding: usize, depth: usize, count: usize) -> Self {
        ps.challenge_pow(u32::try_from(grinding).expect("a few grinding bits"));
        let positions = sample_queries(ps, depth, count);
        let lambda = ps.verifier_message();
        Self {
            positions,
            lambda,
            weights: F192::powers(lambda, count),
        }
    }

    /// The batch the positions and their weights make.
    fn batch(&self) -> QueryBatch<'_> {
        QueryBatch::new(&self.positions, &self.weights)
    }
}

/// Prove `sum_x witness(x) * w(x) = target` against the L0 commitment `l0`.
///
/// # Arguments
///
/// - `config`: the configuration `l0` was made under, its interleaving `2^initial_k` and its rate L0's.
/// - `log_n`: the log of the committed cube, in words.
/// - `witness`: the committed lanes' words, only read; the first fold lifts them into `E`.
/// - `weight`: the weight `w` over the whole `2^log_n` cube.
/// - `target`: the claimed sum, already bound by the caller.
/// - `l0`: the L0 codeword and Merkle tree.
/// - `ps`: the transcript, into which every scalar is bound as it is sent.
///
/// # Precondition
///
/// `witness` is a whole number of lane blocks, so it may be shorter than `2^log_n` words.
/// The weight must then vanish at every boolean point of `[witness.len(), 2^log_n)`.
///
/// - The lane rounds treat the absent blocks as zero, while the verifier evaluates the weight over the whole cube.
/// - A weight nonzero out there gives a proof that fails at the terminal check.
/// - The stacked opening meets this by keeping every claim's support inside the placed stack.
///
/// # Hiding
///
/// Under a configuration that pads, the commitment is a hiding one, and after the lane fold's last challenge:
///
/// - a transcript still hidden is revealed: the running claim is sent in the clear;
/// - the padding's lane fold is sent, and level 0's queries take its share off their rows.
///
/// # Transcript
///
/// Each level's Merkle openings travel as one hint, which is not absorbed.
/// The typed caller has already bound the complete immutable L0 record and statement, or a hiding commitment's root.
///
/// # Panics
///
/// Panics on a shape the commitment does not have, or a padding other than the configuration's.
pub(crate) fn prove(
    config: &Config,
    log_n: usize,
    witness: &[F64],
    weight: &dyn InitialWeight,
    target: F192,
    l0: &BaseCommitment,
    ps: &mut ProverState,
) {
    let initial_k = config.initial_k();
    let log_inv_rate_0 = config.log_inv_rates()[0];
    let log_msg_cols_0 = log_n - initial_k;
    let num_interleaved_0 = 1usize << initial_k;
    // Only the lanes that carry data are committed.
    // So the witness is whole lane blocks, generally fewer than `2^log_n` words.
    let lane_block = 1usize << log_msg_cols_0;
    let n_lanes = witness.len() / lane_block;
    assert_eq!(witness.len(), n_lanes * lane_block, "witness is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= num_interleaved_0,
        "at most 2^initial_k lanes"
    );
    assert_eq!(l0.n_lanes(), n_lanes, "the commitment holds the witness's lanes");
    assert_eq!(l0.num_positions(), 1 << (log_msg_cols_0 + log_inv_rate_0));
    let pad_k = config.padding();
    assert_eq!(
        l0.pads.len(),
        pad_k * n_lanes,
        "the commitment's padding is the opening's"
    );

    // The typed stack wrapper binds the whole immutable record, or a hiding commitment's root, and the public statement
    // before drawing opening challenges. This private kernel does not bind either again.
    // A plain opening's weight includes the commitment-time anchor, restricted to the occupied lanes.

    // Phase 1: the lane fold, `initial_k` rounds over the witness's top variables.
    // The first message answers `target`; each round samples its challenge, then sends the next message.
    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, weight, target, lane_block, initial_k));
    start_msg.send(ps, target);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    let mut g1 = Vec::new();
    for j in 0..initial_k {
        let last = j + 1 == initial_k;
        let next = if last { NextRound::Words } else { NextRound::Lanes };
        let r_j = ps.verifier_message();
        let msg = sumcheck_span.in_scope(|| sc.fold_lane(r_j, lane_block, next));
        r_lane_fold.push(r_j);
        if last && pad_k > 0 {
            // A hidden transcript ends here: the running claim goes in the clear, and so does every later message.
            if ps.is_hidden() {
                ps.set_hidden(false);
                ps.prover_message(&sc.claim());
            }
            // The padding folded as the lanes are: g_1[j] = sum_u eq(r, u) pad_u[j].
            let eq = eq_table(&r_lane_fold);
            g1 = (0..pad_k)
                .map(|j| (0..n_lanes).fold(F192::ZERO, |acc, u| acc + eq[u].mul_base(l0.pads[u * pad_k + j])))
                .collect();
            ps.prover_messages(&g1);
        }
        msg.send(ps, sc.claim());
    }
    drop(sumcheck_span);

    // Phase 2: commit the lane-folded witness, now over `E`, as the L1 oracle.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks()[0];
    assert!(n1 >= log_num_interleaved_1);
    let span = tracing::info_span!("Commit", level = 1).entered();
    let mut oracle = LevelCommitment::new(
        sc.shared_ext().clone(),
        n1 - log_num_interleaved_1,
        log_num_interleaved_1,
        config.log_inv_rates()[1],
    );
    drop(span);
    ps.prover_message(&oracle.root());

    // L1's OOD claims bind its Johnson list before the L0 queries are drawn.
    // Each claimed evaluation is introduced into the running sumcheck.
    sc.send_ood(ps, n1, config.ood_samples()[1]);

    // Phase 3: L0's query phase, after its proof of work.
    let depth_0 = log_msg_cols_0 + log_inv_rate_0;
    let queries_0 = LevelQueries::draw(ps, config.grinding_bits()[0], depth_0, config.queries()[0]);
    let span = tracing::info_span!("Open", level = 0).entered();
    // The induce folds each row lane-ascending against the lane eq table.
    // Reversed, block `b` sits at index `b` and the absent lanes' zeros at the end, where they add nothing.
    let opened_rows_0: Vec<Vec<F64>> = (queries_0.positions.iter())
        .map(|&q| {
            let mut row = vec![F64::ZERO; num_interleaved_0];
            for (t, &word) in l0.row(q).iter().enumerate() {
                row[n_lanes - 1 - t] = word;
            }
            row
        })
        .collect();
    l0.open(ps, &queries_0.positions);
    drop(span);

    // Induce the L0 consistency weight, and its claimed sum from the opened rows.
    let span = tracing::info_span!("Induce", level = 0).entered();
    let batch_0 = queries_0.batch();
    let mut claimed_sum_0 = batch_0.claimed_sum(&opened_rows_0, &r_lane_fold);
    let induced_0 = batch_0.induced_weight(n1, log_inv_rate_0);
    // The opened rows fold the padded codeword.
    // Taking the padding's share off each query leaves the folded data's codeword, so the weight is unchanged.
    if pad_k > 0 {
        claimed_sum_0 += batch_0.padding_correction(&Padding::new(n1, log_inv_rate_0), &g1);
    }
    drop(span);

    // Introduce the consistency claim, then batch the level's pending claims with powers of `lambda_0`.
    tracing::info_span!("Introduce", level = 0).in_scope(|| sc.join(ps, queries_0.lambda, claimed_sum_0, induced_0));

    // Phase 4: the recursive levels.
    // Each folds its `k_i` rounds, then either closes the opening or commits the next oracle and queries the last one.
    let r = config.level_steps();
    for i in 0..r {
        let k_i = config.level_ks()[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let sumcheck_span = tracing::info_span!("Sumcheck");
        for _ in 0..k_i {
            let ri = ps.verifier_message();
            let msg = sumcheck_span.in_scope(|| sc.fold(ri));
            msg.send(ps, sc.claim());
            level_rs.push(ri);
        }
        drop(sumcheck_span);
        let depth = oracle.num_positions().trailing_zeros() as usize;

        if i + 1 == r {
            // Last level: send the residual `yr` in the clear, then grind before its queries.
            ps.prover_messages(sc.f_ext());
            // The batching challenge is drawn after `yr` and the queries are bound, as the verifier draws it.
            let queries = LevelQueries::draw(ps, config.grinding_bits()[i + 1], depth, config.queries()[i + 1]);
            let span = tracing::info_span!("Final level").entered();
            // Tie the last oracle into the running claim by the same intro and batching step as every level.
            // - The consistency weight is the induced weight on the residual cube.
            // - The residual rounds then discharge the batched claim.
            let rows = oracle.open(ps, &queries.positions);
            let batch = queries.batch();
            let claimed_sum = batch.claimed_sum(&rows, &level_rs);
            let n_res = sc.f_ext().len().trailing_zeros() as usize;
            let induced = batch.induced_weight(n_res, config.log_inv_rates()[i + 1]);
            sc.join(ps, queries.lambda, claimed_sum, induced);
            for j in 0..n_res {
                let ri = ps.verifier_message();
                let msg = sc.fold(ri);
                // Why skip the last message: the verifier evaluates `yr` at the final point instead.
                if j + 1 < n_res {
                    msg.send(ps, sc.claim());
                }
            }
            drop(span);
            return;
        }

        let n_next = sc.f_ext().len().trailing_zeros() as usize;
        let log_num_interleaved_next = config.level_ks()[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let span = tracing::info_span!("Commit", level = i + 2).entered();
        let next_oracle = LevelCommitment::new(
            sc.shared_ext().clone(),
            n_next - log_num_interleaved_next,
            log_num_interleaved_next,
            config.log_inv_rates()[i + 2],
        );
        drop(span);
        ps.prover_message(&next_oracle.root());

        sc.send_ood(ps, n_next, config.ood_samples()[i + 2]);

        // This level's query phase, after its proof of work, then its batching challenge.
        let queries = LevelQueries::draw(ps, config.grinding_bits()[i + 1], depth, config.queries()[i + 1]);
        let span = tracing::info_span!("Open", level = i + 1).entered();
        let rows = oracle.open(ps, &queries.positions);
        drop(span);

        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let batch = queries.batch();
        let claimed_sum = batch.claimed_sum(&rows, &level_rs);
        let induced = batch.induced_weight(n_next, config.log_inv_rates()[i + 1]);
        drop(span);

        tracing::info_span!("Introduce", level = i + 1).in_scope(|| sc.join(ps, queries.lambda, claimed_sum, induced));

        oracle = next_oracle;
    }
    unreachable!("the configuration has at least one recursive level")
}
