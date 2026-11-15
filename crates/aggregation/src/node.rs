//! The entry point that proves one node of an aggregation tree.

use super::cells::count;
use super::child::gen_verify;
use super::coverage::plan_coverage;
use super::deferred::{DeferredBytecodeClaim, aggregate_deferred_claims, bytecode_sums};
use super::error::AggregateError;
use super::guest::{assembled, fs_seed, scalar_bytecode, unified_guest};
#[cfg(test)]
use super::hints::FORGE;
use super::hints::{Hints, lean_sphincs_hints, lean_xmss_hints};
use super::proof::{AggregateClaims, AggregateProof, OutputClaims, is_sorted};
use super::statement::{lean_sphincs_claim_cells, lean_xmss_claim_cells, list_split, statement_digest};
use super::{MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE};
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::{Prover, Stats};
use lean_da::CELLS_PER_ROW;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_vm_core::cpu::{from_scalar, public_input_bytes, to_scalar};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use primitives::field::F128;

/// Aggregate leanXMSS and leanSPHINCS signatures, blobs and the claims of child proofs, on the prover `P`, also
/// returning the prover's statistics (what the CLI's benchmarks report).
///
/// - `children`: at most [`MAX_RECURSIONS`], each with its claims.
/// - `raw_lean_xmss`, `raw_lean_sphincs`: `(public_key, message, signature)`, in any order.
/// - `blobs`: the encoded blobs, if any ([`lean_da::BlobMatrix`]).
/// - `output`: which covered claims the proof attests.
/// - `log_inv_rate`: the code rate's log, in [`MIN_LOG_INV_RATE`]..=[`MAX_LOG_INV_RATE`];
///   higher gives smaller proof size but slower proving time.
///
/// # WARNING
/// - Signatures and children must be valid (children checked with [`AggregateProof::verify`]):
///   otherwise proving fails.
/// - Do not run two `aggregate` calls at once in one process, and call [`P::init`](Prover::init) once before the first.
pub fn aggregate<P: Prover>(
    children: &[(AggregateClaims, AggregateProof)],
    mut raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    mut raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
    log_inv_rate: usize,
) -> Result<(AggregateClaims, AggregateProof, Stats), AggregateError> {
    let declare = match output {
        OutputClaims::All => None,
        OutputClaims::Only(claims) => Some(claims),
    };
    // Proving checks the rate too, but only after the witness is built.
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregateError::InvalidInput("log_inv_rate out of range"));
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregateError::InvalidInput("more than MAX_RECURSIONS children"));
    }
    // The published root and the guest's slot for it: a child's, or `children.len()` for the node's own, its blobs'
    // or none.
    let own = children.len();
    let (da_pick, da_root) = match (blobs, declare.map(|claims| claims.da_commitment)) {
        (Some(matrix), declared) => {
            let root = Some(matrix.top_root());
            if declared.is_some_and(|declared| declared != root) {
                return Err(AggregateError::InvalidInput("a node with blobs publishes their root"));
            }
            (own, root)
        }
        (None, None) => children
            .iter()
            .position(|(claims, _)| claims.da_commitment.is_some())
            .map_or((own, None), |i| (i, children[i].0.da_commitment)),
        (None, Some(None)) => (own, None),
        (None, Some(root)) => children
            .iter()
            .position(|(claims, _)| claims.da_commitment == root)
            .map(|i| (i, root))
            .ok_or(AggregateError::InvalidInput("the requested DA root is not a child's"))?,
    };

    // The request's checks, on the claim lists alone, before any costly work.
    if !children.iter().all(|(claims, _)| is_sorted(claims)) {
        return Err(AggregateError::InvalidChild);
    }
    let raw_lean_xmss_claims = sorted_claims(&mut raw_lean_xmss);
    let raw_lean_sphincs_claims = sorted_claims(&mut raw_lean_sphincs);
    let cover = plan_coverage(&raw_lean_xmss_claims, &raw_lean_sphincs_claims, children, declare)?;
    if cover.lean_xmss.signers.is_empty() && cover.lean_sphincs.signers.is_empty() && da_root.is_none() {
        return Err(AggregateError::InvalidInput("nothing to publish"));
    }

    // Nothing here verifies a child (see `AGENTS.md`): the replay reads out of its proof the summary `gen_verify`
    // builds the guest's witness from, and fails only on a proof it cannot walk.
    let _span = tracing::info_span!("Replay children").entered();
    let carried_points: Vec<Vec<F128>> = children.iter().map(|(_, proof)| proof.bytecode_point.clone()).collect();
    let carried_sums = bytecode_sums::<P>(&carried_points);
    let carried: Vec<DeferredBytecodeClaim> = carried_points
        .into_iter()
        .zip(&carried_sums)
        .map(|(point, sums)| DeferredBytecodeClaim::from_sums(point, sums))
        .collect();
    let public_inputs: Vec<[F128; 2]> = children
        .iter()
        .zip(&carried)
        .map(|((claims, _), defer)| statement_digest(claims, defer))
        .collect();
    // One single-threaded replay per worker: nothing inside dispatches.
    let summaries = P::map_collect(children.len(), |i| {
        let pi = public_input_bytes(&public_inputs[i]);
        verifier::replay_unchecked(scalar_bytecode(), &pi, &children[i].1.proof)
    });
    let summaries: Vec<verifier::Summary> = summaries
        .into_iter()
        .collect::<Result<_, _>>()
        .map_err(|_| AggregateError::InvalidChild)?;
    drop(_span);

    let _span = tracing::info_span!("Build witness").entered();
    let mut hints = Hints::default();
    hints.push(
        "meta",
        vec![
            count(cover.lean_xmss.signers.len()),
            count(cover.lean_xmss.dups.len()),
            count(raw_lean_xmss.len()),
            count(cover.lean_sphincs.signers.len()),
            count(cover.lean_sphincs.dups.len()),
            count(raw_lean_sphincs.len()),
            count(children.len()),
            count(usize::from(blobs.is_some())),
        ],
    );
    hints.push("fs_seed", fs_seed().to_vec());
    // Both lists in the guest's order, leanXMSS first: each one's split, its declared claims, then its duplicates.
    let lean_xmss_cells: Vec<[F128; 4]> = cover.lean_xmss.signers.iter().map(lean_xmss_claim_cells).collect();
    let lean_sphincs_cells: Vec<[F128; 4]> = cover
        .lean_sphincs
        .signers
        .iter()
        .map(lean_sphincs_claim_cells)
        .collect();
    for cells in [&lean_xmss_cells, &lean_sphincs_cells] {
        if !cells.is_empty() {
            hints.push("signers_split", list_split(cells.len()));
        }
        for claim in cells {
            hints.push("claims", claim.to_vec());
        }
    }
    let dups = cover.lean_xmss.dups.iter().map(lean_xmss_claim_cells);
    for claim in dups.chain(cover.lean_sphincs.dups.iter().map(lean_sphincs_claim_cells)) {
        hints.push("dup_claims", claim.to_vec());
    }
    // Each slot is hinted as an offset into its scheme's region, which is how one range check keeps a scheme's
    // writers off the other's claims.
    let raw = [
        (
            "raw_index",
            &cover.lean_xmss.raw,
            P::map_collect(raw_lean_xmss.len(), |i| {
                let (pk, message, sig) = &raw_lean_xmss[i];
                lean_xmss_hints(pk, sig, message)
            }),
        ),
        (
            "sp_raw_index",
            &cover.lean_sphincs.raw,
            P::map_collect(raw_lean_sphincs.len(), |i| {
                let (pk, message, sig) = &raw_lean_sphincs[i];
                lean_sphincs_hints(pk, sig, message)
            }),
        ),
    ];
    for (name, offsets, signatures) in raw {
        for (&offset, signature) in offsets.iter().zip(signatures) {
            hints.push(name, vec![count(offset)]);
            hints.extend(signature?);
        }
    }

    // Each child's fresh claim, the one its verification raises.
    let fresh_points: Vec<Vec<F128>> = summaries
        .iter()
        .map(|summary| summary.bytecode_point.iter().copied().map(from_scalar).collect())
        .collect();
    let fresh_sums = bytecode_sums::<P>(&fresh_points);
    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    // Each child's witness is its own, one child per worker: nothing inside dispatches.
    let verified = P::map_collect(children.len(), |i| gen_verify(kbc, &children[i].1.proof, &summaries[i]));
    for (i, ((claims, _), verified)) in children.iter().zip(verified).enumerate() {
        hints.push(
            "child_meta",
            vec![count(claims.lean_xmss.len()), count(claims.lean_sphincs.len())],
        );
        for offsets in [&cover.lean_xmss.children[i], &cover.lean_sphincs.children[i]] {
            if offsets.is_empty() {
                continue;
            }
            hints.push("signers_split", list_split(offsets.len()));
            // Strictly increasing slots go as gaps (`child_claim_list_mono`).
            if offsets.is_sorted_by(|a, b| a < b) {
                hints.push("child_mono", vec![count(1)]);
                let mut next = 0;
                for &offset in offsets {
                    hints.push("child_claim_gap", vec![count(offset - next)]);
                    next = offset + 1;
                }
            } else {
                hints.push("child_mono", vec![count(0)]);
                for &offset in offsets {
                    hints.push("child_claim_index", vec![count(offset)]);
                }
            }
        }
        hints.push("child_defer", carried[i].cells());
        let child_da = verifier::da::digest(claims.da_commitment);
        hints.push("child_da", hash_to_scalars(&child_da).to_vec());
        hints.extend(verified?);
    }
    drop(_span);

    let defer = if children.is_empty() {
        let leaf = DeferredBytecodeClaim::leaf();
        hints.push("leaf_defer", vec![leaf.bytecode_value]);
        leaf
    } else {
        let _span = tracing::info_span!("Batch deferred claims").entered();
        // Each child's fresh claim, then its carried one: the batch's order.
        let fresh = (fresh_points.into_iter().zip(&fresh_sums))
            .map(|(point, sums)| DeferredBytecodeClaim::from_sums(point, sums));
        let claims: Vec<_> = fresh
            .zip(carried)
            .flat_map(|(fresh, carried)| [fresh, carried])
            .collect();
        let sums = fresh_sums
            .into_iter()
            .zip(carried_sums)
            .flat_map(|(fresh, carried)| [fresh, carried]);
        let (batch_hints, reduced) = aggregate_deferred_claims::<P>(&public_inputs, &claims, sums.collect());
        hints.extend(batch_hints);
        reduced
    };

    if let Some(matrix) = blobs {
        let commitment = matrix.top_root();
        hints.push(
            "da_challenge",
            vec![from_scalar(verifier::da::membership_challenge(&commitment))],
        );
        hints.push("da_n_blobs", vec![count(matrix.n_blobs())]);
        // Padding rows are constants the guest bakes, so only the real rows' symbols ride the stream.
        for j in 0..CELLS_PER_ROW {
            for cell in matrix.column(j).expect("a column below CELLS_PER_ROW") {
                hints.push("da_symbols", cell.iter().map(|&w| F128::from(w)).collect());
            }
        }
    }
    hints.push("da_pick", vec![count(da_pick)]);

    let claims = AggregateClaims {
        lean_xmss: cover.lean_xmss.signers,
        lean_sphincs: cover.lean_sphincs.signers,
        da_commitment: da_root,
    };
    #[cfg(test)]
    if let Some(forge) = FORGE.with(|forge| forge.borrow_mut().take()) {
        forge(&mut hints);
    }
    let public_input = statement_digest(&claims, &defer).map(|x| to_scalar(&x));
    let (proof, stats) = P::prove(assembled::<P>(), &hints.witness(), public_input, log_inv_rate).map_err(|error| {
        tracing::debug!(%error, "proving failed");
        AggregateError::ProvingFailed
    })?;
    let proof = AggregateProof {
        bytecode_point: defer.bytecode_point,
        proof,
    };
    Ok((claims, proof, stats))
}

/// Sort raw signatures on their claims and drop repeats: on the whole (pubkey, message) pair, so a signer may appear
/// once per message, and one claim needs one signature, whatever leaf index a leanXMSS one carries. Returns the claims.
fn sorted_claims<K: Ord + Copy, S>(raw: &mut Vec<(K, [u8; 32], S)>) -> Vec<(K, [u8; 32])> {
    raw.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw.dedup_by_key(|(pk, message, _)| (*pk, *message));
    raw.iter().map(|(pk, message, _)| (*pk, *message)).collect()
}
