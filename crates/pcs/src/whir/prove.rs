// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The recursive prover: the lane fold, then one commit, query phase and induce
//! per level, down to the residual sent in the clear.

use super::commit::ligero_commit_ext;
use super::sample_queries_ordered;
use super::sumcheck::{Basis, InitialRounds, SumcheckProver, send_msg};
use crate::merkle::Hash;
use crate::ntt::{AdditiveNttF64, Codeword};
use crate::whir::config::ProverConfig;
use crate::whir::induce::{
    eval_sk_at_vks, induce_sumcheck_enforced_sum, induce_sumcheck_evaluate_at_residual, induce_sumcheck_poly,
    induce_sumcheck_poly_auto_base,
};
use fiat_shamir::merkle::PrunedMerklePaths;
use fiat_shamir::transcript::Transmitter;
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_table;

/// Prover side of the OOD claims taken right after a level's root enters the
/// transcript: sample `z`, evaluate the folded witness there, send the claim
/// and its intro message. The claim stays pending: the level's batching
/// challenge is drawn only once its query positions are fixed too, and
/// `glue_pending` then folds every claim of the level in with its own power.
/// Mirror of the verifier's `replay_ood`, operation for operation.
fn send_ood(sc: &mut SumcheckProver<'_>, ps: &mut impl Transmitter, n_vars: usize, count: usize) {
    for _ in 0..count {
        let z = ps.sample_vec(n_vars);
        let (intro, y) = sc.introduce_new_with_eval(eq_table(&z));
        ps.add_scalar(y);
        send_msg(ps, intro, y);
    }
}

/// An `E` row from the `F64` words its Merkle leaf is hashed from.
fn ext_row(words: &[F64]) -> Vec<F192> {
    words
        .as_chunks::<3>()
        .0
        .iter()
        .map(|&[c0, c1, c2]| F192::new(c0.0, c1.0, c2.0))
        .collect()
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`](super::commit()) (with `log_batch_size = config.initial_k()` and
/// `log_inv_rate = config.log_inv_rates()[0]`).
///
/// `witness` is borrowed: it is only READ (round-0 message + the first lane
/// fold, which lifts it into an owned E-vector), so callers with a large
/// committed stack pass the slice directly instead of paying a full copy.
///
/// PRECONDITION, and the reason `witness` may be shorter than `2^log_n`: it is a
/// whole number of lane blocks, and `b_initial` must be the weight restricted to
/// them, with the weight VANISHING at every boolean point of
/// `[witness.len(), 2^log_n)`. The lane rounds treat the absent blocks as zero
/// while the verifier's `eval_b_at` evaluates the closed form over the whole cube,
/// so a weight that is nonzero out there produces a proof that fails only at the
/// terminal check. `stack_open` discharges this by bounding every claim's support
/// by `stack.len()`; `ood_samples[0] == 0` is what keeps a full-tensor OOD weight
/// out of these rounds.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one phase per level. The caller has already bound the initial commitment and target.
#[expect(
    clippy::too_many_arguments,
    reason = "The proof kernel keeps its independent inputs explicit."
)]
pub fn recursive_prover_with_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Vec<F192>,
    target: F192,
    l0_codeword: &Codeword,
    l0_tree: &[Hash],
    ps: &mut impl Transmitter,
) {
    recursive_prover_with_prepared_basis(
        config,
        log_n,
        witness,
        Basis::Dense(b_initial),
        target,
        l0_codeword,
        l0_tree,
        None,
        ps,
    );
}

#[expect(
    clippy::too_many_arguments,
    reason = "The proof kernel keeps its independent inputs explicit."
)]
pub(crate) fn recursive_prover_with_prepared_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Basis<'_>,
    target: F192,
    l0_codeword: &Codeword,
    l0_tree: &[Hash],
    initial: Option<InitialRounds>,
    ps: &mut impl Transmitter,
) {
    let r = config.level_steps();
    let initial_k = config.initial_k();

    let log_inv_rate_0 = config.log_inv_rates()[0];
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
    if let Basis::Dense(b) = &b_initial {
        assert_eq!(b.len(), witness.len());
    }
    assert_eq!(l0_codeword.len(), block_len_0 * n_lanes);
    assert_eq!(l0_tree.len(), 2 * block_len_0 - 1);

    // Nothing is absorbed on entry. The commitment was bound by the `add_root`/`next_root` that
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
    // The induce folds a lane-ASCENDING row against the lane eq table: reversing the
    // image puts block `b` at index `b` and the absent lanes' zeros at the end, where
    // they contribute nothing.
    let fold_row = |image: &[F64]| -> Vec<F64> {
        let mut row = vec![F64::ZERO; num_interleaved_0];
        for (t, &word) in image.iter().enumerate() {
            row[n_lanes - 1 - t] = word;
        }
        row
    };

    let ood_count = |lvl: usize| -> usize { config.ood_samples()[lvl] };

    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc_prover, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, b_initial, target, lane_block, initial_k, initial));
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
    let log_num_interleaved_1 = config.level_ks()[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates()[1];
    let span = tracing::info_span!("Commit", level = 1).entered();
    let ntt_1 = AdditiveNttF64::standard(log_msg_cols_1 + log_inv_rate_1);
    let wtns_1 = ligero_commit_ext(
        sc_prover.f_ext(),
        log_msg_cols_1,
        log_num_interleaved_1,
        log_inv_rate_1,
        ntt_1,
    );
    drop(span);
    ps.add_root(&wtns_1.root());

    // Bind the L1 Johnson list before drawing L0 queries. Each claimed random
    // MLE evaluation is introduced into the running sumcheck.
    send_ood(&mut sc_prover, ps, n1, ood_count(1));

    // PoW grinding for L0's query phase.
    ps.grind(config.grinding_bits()[0] as u32);

    // Open L0; lane-fold weights = r_lane_fold.
    let num_queries_0 = config.queries()[0];
    let queries_0 = sample_queries_ordered(ps, block_len_0, num_queries_0);
    // One batching challenge for the whole level, drawn once every claim it
    // batches is fixed: the OOD claims above and these query positions.
    let lambda_0 = ps.sample();
    let weights_0 = powers(lambda_0, num_queries_0);
    let span = tracing::info_span!("Open", level = 0).entered();
    // Ordered (dup-possible) rows for the local induce math ...
    let opened_0 = l0_codeword.open(&queries_0);
    let opened_rows_0: Vec<Vec<F64>> = queries_0.iter().map(|&q| fold_row(opened_0.row(q))).collect();
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    ps.hint_merkle(PrunedMerklePaths::prune(l0_tree, block_len_0, &queries_0, |q| {
        opened_0.row(q).to_vec()
    }));
    drop(span);

    // Induce basis_0 from the L0 opens. L0 dominates the induce phase, where
    // the sparse-prefix transposed-NTT path wins; the dispatcher auto-selects
    // it (deeper levels stay dense), mirroring the original.
    let sks_vks_n1 = eval_sk_at_vks(n1);
    let span = tracing::info_span!("Induce", level = 0).entered();
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto_base(
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
        let k_i = config.level_ks()[i];
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
            ps.grind(config.grinding_bits()[i + 1] as u32);
            let num_queries_last = config.queries()[i + 1];
            let queries_last = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_last);
            // The final level's batching challenge is drawn only after `yr`
            // and its queries are bound, matching the verifier exactly.
            let lambda_last = ps.sample();
            let weights_last = powers(lambda_last, num_queries_last);
            let span = tracing::info_span!("Final level").entered();
            // Final level: stored (sorted-unique) only, no local induce; the
            // verifier fans these to ordered for its last-level induce.
            let opened_last = wtns_prev.open(&queries_last);
            ps.hint_merkle(PrunedMerklePaths::prune(
                &wtns_prev.tree,
                wtns_prev.block_len,
                &queries_last,
                |q| opened_last.row(q).to_vec(),
            ));
            // Tie the last commitment into the running claim through the same
            // intro/glue step as every other level, then finish the remaining
            // sumcheck rounds. This closes on one weight evaluation instead of
            // a sweep over the residual cube.
            let rows_last: Vec<Vec<F192>> = queries_last.iter().map(|&q| ext_row(opened_last.row(q))).collect();
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
        let log_num_interleaved_next = config.level_ks()[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let log_msg_cols_next = n_next - log_num_interleaved_next;
        let log_inv_rate_next = config.log_inv_rates()[i + 2];
        let span = tracing::info_span!("Commit", level = i + 2).entered();
        let ntt_next = AdditiveNttF64::standard(log_msg_cols_next + log_inv_rate_next);
        let wtns_next = ligero_commit_ext(
            sc_prover.f_ext(),
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
            ntt_next,
        );
        drop(span);
        ps.add_root(&wtns_next.root());

        send_ood(&mut sc_prover, ps, n_next, ood_count(i + 2));

        // PoW grinding for this iteration's query phase.
        ps.grind(config.grinding_bits()[i + 1] as u32);
        let num_queries_i = config.queries()[i + 1];
        let queries_i = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_i);
        let lambda_i = ps.sample();
        let weights_i = powers(lambda_i, num_queries_i);
        let span = tracing::info_span!("Open", level = i + 1).entered();
        // Ordered rows for the local induce; sorted-unique rows + octopus stored.
        let opened_i = wtns_prev.open(&queries_i);
        let opened_rows_i: Vec<Vec<F192>> = queries_i.iter().map(|&q| ext_row(opened_i.row(q))).collect();
        ps.hint_merkle(PrunedMerklePaths::prune(
            &wtns_prev.tree,
            wtns_prev.block_len,
            &queries_i,
            |q| opened_i.row(q).to_vec(),
        ));
        drop(span);

        let sks_vks_i = eval_sk_at_vks(n_next);
        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let (basis_i_induced, enforced_sum_i) =
            induce_sumcheck_poly(n_next, &sks_vks_i, &opened_rows_i, &level_rs, &queries_i, &weights_i);
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
