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

use super::commit::{ProverData, ligero_commit_ext};
use super::sample_queries_ordered;
use super::sumcheck::{InitialWeight, SumcheckProver, send_msg};
use crate::merkle::PrunedMerklePaths;
use crate::whir::config::Config;
use crate::whir::query::QueryBatch;
use fiat_shamir::ProverState;
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_table;

/// Send `count` OOD claims on the folded witness, right after its root enters the transcript.
///
/// For each claim, in transcript order:
///
/// 1. sample the point `z` of `n_vars` coordinates,
/// 2. send the value `y` of the folded witness at `z`,
/// 3. send the claim's intro message.
///
/// The claims stay pending until the level's batching challenge is drawn, after its query positions.
/// The verifier replays the same steps in the same order.
fn send_ood(sc: &mut SumcheckProver<'_>, ps: &mut ProverState, n_vars: usize, count: usize) {
    for _ in 0..count {
        let z = ps.verifier_messages(n_vars);
        let (intro, y) = sc.introduce_new_with_eval(eq_table(&z));
        ps.prover_message(&y);
        send_msg(ps, intro, y);
    }
}

/// An `E` row as the `F64` words its Merkle leaf is hashed from.
fn ext_row_words(row: &[F192]) -> Vec<F64> {
    row.iter().flat_map(|v| [F64(v.c0), F64(v.c1), F64(v.c2)]).collect()
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
/// # Transcript
///
/// Each level's Merkle openings travel as one hint, which is not absorbed.
/// The caller has already transmitted the L0 root.
pub(crate) fn prove(
    config: &Config,
    log_n: usize,
    witness: &[F64],
    weight: &dyn InitialWeight,
    target: F192,
    l0: &ProverData,
    ps: &mut ProverState,
) {
    let (l0_codeword, l0_tree) = (&l0.codeword[..], &l0.merkle_tree[..]);
    let r = config.level_steps();
    let initial_k = config.initial_k();

    let log_inv_rate_0 = config.log_inv_rates()[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
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
    assert_eq!(l0_codeword.len(), block_len_0 * n_lanes);
    assert_eq!(l0_tree.len(), 2 * block_len_0 - 1);

    // Invariant: nothing is absorbed on entry, since the state already determines the commitment and the target.
    // - The commitment was bound when its root was transmitted.
    // - The target is `sum_i lambda^i * claim_i`, its claim values bound when read and `lambda` drawn from the state.
    // So a caller must transmit its root before opening against it: that makes the fold challenges depend on it.

    // A codeword row interleaves the committed lanes only, lane `t` being stack block `n_lanes - 1 - t`.
    // So a row is the tail of the leaf image, whose leading zeros are the absent lanes, and only it rides the proof.
    let l0_row = |q: usize| -> Vec<F64> { l0_codeword[q * n_lanes..(q + 1) * n_lanes].to_vec() };
    // The same row for the induce, which folds a lane-ascending row against the lane eq table.
    // Reversed, block `b` sits at index `b` and the absent lanes' zeros at the end, where they add nothing.
    let l0_fold_row = |q: usize| -> Vec<F64> {
        let mut row = vec![F64::ZERO; num_interleaved_0];
        for (t, &word) in l0_codeword[q * n_lanes..(q + 1) * n_lanes].iter().enumerate() {
            row[n_lanes - 1 - t] = word;
        }
        row
    };

    let ood_count = |lvl: usize| -> usize { config.ood_samples()[lvl] };

    // Phase 1: the lane fold, `initial_k` rounds over the witness's top variables.
    // The first message answers `target`; each round samples its challenge, then sends the next message.
    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc_prover, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, weight, target, lane_block, initial_k));
    send_msg(ps, start_msg, target);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        let r_j = ps.verifier_message();
        let msg = sumcheck_span.in_scope(|| sc_prover.fold_lane(r_j, lane_block, j + 1 == initial_k));
        send_msg(ps, msg, sc_prover.claim());
        r_lane_fold.push(r_j);
    }
    drop(sumcheck_span);

    // Phase 2: commit the lane-folded witness, now over `E`, as the L1 oracle.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks()[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates()[1];
    let span = tracing::info_span!("Commit", level = 1).entered();
    let wtns_1 = ligero_commit_ext(
        sc_prover.shared_ext().clone(),
        log_msg_cols_1,
        log_num_interleaved_1,
        log_inv_rate_1,
    );
    drop(span);
    ps.prover_message(&wtns_1.root());

    // L1's OOD claims bind its Johnson list before the L0 queries are drawn.
    // Each claimed evaluation is introduced into the running sumcheck.
    send_ood(&mut sc_prover, ps, n1, ood_count(1));

    // Phase 3: L0's query phase, after its proof of work.
    ps.challenge_pow(config.grinding_bits()[0] as u32);

    let num_queries_0 = config.queries()[0];
    let queries_0 = sample_queries_ordered(ps, block_len_0, num_queries_0);
    // One batching challenge for the whole level, drawn once every claim it batches is fixed.
    // Those claims are the OOD claims above and the queries at these positions.
    let lambda_0 = ps.verifier_message();
    let weights_0 = powers(lambda_0, num_queries_0);
    let span = tracing::info_span!("Open", level = 0).entered();
    // The induce takes the rows in query order, repeats included.
    let opened_rows_0: Vec<Vec<F64>> = queries_0.iter().map(|&q| l0_fold_row(q)).collect();
    // The proof stores each distinct row once, with one pruned path set over the distinct positions.
    // The verifier expands them back to query order.
    ps.prover_hint(&PrunedMerklePaths::prune(l0_tree, block_len_0, &queries_0, l0_row).to_hint());
    drop(span);

    // Induce the L0 consistency weight, and its claimed sum from the opened rows.
    let span = tracing::info_span!("Induce", level = 0).entered();
    let batch_0 = QueryBatch::new(&queries_0, &weights_0);
    let enforced_sum_0 = batch_0.claimed_sum(&opened_rows_0, &r_lane_fold);
    let basis_0_induced = batch_0.induced_weight(n1, log_inv_rate_0);
    drop(span);

    // Introduce the consistency claim, then batch the level's pending claims with powers of `lambda_0`.
    let span = tracing::info_span!("Introduce", level = 0).entered();
    let intro_msg_0 = sc_prover.introduce_new(basis_0_induced, enforced_sum_0);
    send_msg(ps, intro_msg_0, enforced_sum_0);
    sc_prover.glue_pending(lambda_0);
    drop(span);

    // Phase 4: the recursive levels.
    // Each folds its `k_i` rounds, then either closes the opening or commits the next oracle and queries the last one.
    let mut wtns_prev = wtns_1;

    for i in 0..r {
        let k_i = config.level_ks()[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let sumcheck_span = tracing::info_span!("Sumcheck");
        for _ in 0..k_i {
            let ri = ps.verifier_message();
            let msg = sumcheck_span.in_scope(|| sc_prover.fold(ri));
            send_msg(ps, msg, sc_prover.claim());
            level_rs.push(ri);
        }
        drop(sumcheck_span);

        if i == r - 1 {
            ps.prover_messages(sc_prover.f_ext());
            // Last level: send the residual `yr` in the clear, then grind before its queries.
            ps.challenge_pow(config.grinding_bits()[i + 1] as u32);
            let num_queries_last = config.queries()[i + 1];
            let queries_last = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_last);
            // The batching challenge is drawn after `yr` and the queries are bound, as the verifier draws it.
            let lambda_last = ps.verifier_message();
            let weights_last = powers(lambda_last, num_queries_last);
            let span = tracing::info_span!("Final level").entered();
            // The proof stores each distinct row once; the verifier expands them back to query order.
            let opened_last = wtns_prev.open(&queries_last);
            ps.prover_hint(
                &PrunedMerklePaths::prune(&wtns_prev.tree, wtns_prev.block_len, &queries_last, |q| {
                    ext_row_words(opened_last.row(q))
                })
                .to_hint(),
            );
            // Tie the last oracle into the running claim by the same intro and batching step as every level.
            // - The consistency weight is the induced weight on the residual cube.
            // - The residual rounds then discharge the batched claim.
            let rows_last: Vec<Vec<F192>> = queries_last.iter().map(|&q| opened_last.row(q).to_vec()).collect();
            let batch_last = QueryBatch::new(&queries_last, &weights_last);
            let enforced_sum_last = batch_last.claimed_sum(&rows_last, &level_rs);
            let n_res = sc_prover.f_ext().len().trailing_zeros() as usize;
            let basis_last = batch_last.induced_weight(n_res, config.log_inv_rates()[i + 1]);
            let intro_msg_last = sc_prover.introduce_new(basis_last, enforced_sum_last);
            send_msg(ps, intro_msg_last, enforced_sum_last);
            sc_prover.glue_pending(lambda_last);
            for j in 0..n_res {
                let ri = ps.verifier_message();
                let msg = sc_prover.fold(ri);
                // Why skip the last message: the verifier evaluates `yr` at the final point instead.
                if j + 1 < n_res {
                    send_msg(ps, msg, sc_prover.claim());
                }
            }
            drop(span);
            return;
        }

        let n_next = sc_prover.f_ext().len().trailing_zeros() as usize;
        let log_num_interleaved_next = config.level_ks()[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let log_msg_cols_next = n_next - log_num_interleaved_next;
        let log_inv_rate_next = config.log_inv_rates()[i + 2];
        let span = tracing::info_span!("Commit", level = i + 2).entered();
        let wtns_next = ligero_commit_ext(
            sc_prover.shared_ext().clone(),
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
        );
        drop(span);
        ps.prover_message(&wtns_next.root());

        send_ood(&mut sc_prover, ps, n_next, ood_count(i + 2));

        // This level's query phase, after its proof of work, then its batching challenge.
        ps.challenge_pow(config.grinding_bits()[i + 1] as u32);
        let num_queries_i = config.queries()[i + 1];
        let queries_i = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_i);
        let lambda_i = ps.verifier_message();
        let weights_i = powers(lambda_i, num_queries_i);
        let span = tracing::info_span!("Open", level = i + 1).entered();
        // Rows in query order for the induce; the proof stores each distinct row once.
        let opened_i = wtns_prev.open(&queries_i);
        let opened_rows_i: Vec<Vec<F192>> = queries_i.iter().map(|&q| opened_i.row(q).to_vec()).collect();
        ps.prover_hint(
            &PrunedMerklePaths::prune(&wtns_prev.tree, wtns_prev.block_len, &queries_i, |q| {
                ext_row_words(opened_i.row(q))
            })
            .to_hint(),
        );
        drop(span);

        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let batch_i = QueryBatch::new(&queries_i, &weights_i);
        let enforced_sum_i = batch_i.claimed_sum(&opened_rows_i, &level_rs);
        let basis_i_induced = batch_i.induced_weight(n_next, config.log_inv_rates()[i + 1]);
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
