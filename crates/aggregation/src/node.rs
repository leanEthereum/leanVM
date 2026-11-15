//! The entry points that prove one node of an aggregation tree.

use super::cells::count;
use super::child::gen_verify;
use super::coverage::plan_coverage;
use super::deferred::{DeferredBytecodeClaim, aggregate_deferred_claims, bytecode_sums, bytecode_value};
use super::error::AggregateError;
use super::guest::{assembled, fs_seed, scalar_bytecode, unified_guest};
#[cfg(test)]
use super::hints::FORGE;
use super::hints::{Hints, lean_sphincs_hints, lean_xmss_hints};
use super::proof::{AggregateClaims, AggregateProof, OutputClaims, is_sorted, public_input};
use super::statement::{lean_sphincs_claim_cells, lean_xmss_claim_cells, list_split, statement_digest};
use super::{LeanSphincsClaim, LeanXmssClaim, MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE};
use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::{Prover, Stats};
use lean_da::CELLS_PER_ROW;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_vm_core::cpu::{from_scalar, public_input_bytes, to_scalar};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use primitives::field::F128;

/// Aggregate leanXMSS and leanSPHINCS signatures, blobs and the claims of child proofs, on the prover `P`.
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
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
    log_inv_rate: usize,
) -> Result<(AggregateClaims, AggregateProof), AggregateError> {
    aggregate_with_stats::<P>(children, raw_lean_xmss, raw_lean_sphincs, blobs, output, log_inv_rate)
        .map(|(claims, proof, _)| (claims, proof))
}

/// [`aggregate`], under the same contract, also returning the prover's statistics (what the CLI's benchmarks report).
pub fn aggregate_with_stats<P: Prover>(
    children: &[(AggregateClaims, AggregateProof)],
    raw_lean_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_lean_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: Option<&lean_da::BlobMatrix>,
    output: OutputClaims,
    log_inv_rate: usize,
) -> Result<(AggregateClaims, AggregateProof, Stats), AggregateError> {
    let declare = match output {
        OutputClaims::All => None,
        OutputClaims::Only(claims) => Some(claims),
    };
    let declared_root = declare.map(|claims| claims.da_commitment);
    // Proving checks the rate too, but only after the witness is built.
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregateError::InvalidInput("log_inv_rate out of range"));
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregateError::InvalidInput("more than MAX_RECURSIONS children"));
    }
    let direct_root = blobs.map(lean_da::BlobMatrix::top_root);
    if direct_root.is_some() && declared_root.is_some_and(|declared| declared != direct_root) {
        return Err(AggregateError::InvalidInput("a node with blobs publishes their root"));
    }
    // The published root and the guest's slot for it: a child's, or `children.len()` for
    // the node's own, its blobs' or none.
    let (da_pick, da_root) = match declared_root {
        _ if direct_root.is_some() => (children.len(), direct_root),
        None => children
            .iter()
            .position(|(claims, _)| claims.da_commitment.is_some())
            .map_or((children.len(), None), |i| (i, children[i].0.da_commitment)),
        Some(None) => (children.len(), None),
        Some(Some(root)) => {
            let i = children
                .iter()
                .position(|(claims, _)| claims.da_commitment == Some(root))
                .ok_or(AggregateError::InvalidInput("the requested DA root is not a child's"))?;
            (i, Some(root))
        }
    };

    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    // On the whole (pubkey, message) pair, so a signer may appear once per message. One
    // claim needs one signature, whatever leaf index a leanXMSS one carries.
    let mut raw_lean_xmss = raw_lean_xmss;
    raw_lean_xmss.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_lean_xmss.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));
    let mut raw_lean_sphincs = raw_lean_sphincs;
    raw_lean_sphincs.sort_by_key(|(pk, message, _)| (*pk, *message));
    raw_lean_sphincs.dedup_by(|(a, am, _), (b, bm, _)| (a, am) == (b, bm));

    // The request's checks, on the claim lists alone, before any costly work.
    if !children.iter().all(|(claims, _)| is_sorted(claims)) {
        return Err(AggregateError::InvalidChild);
    }
    let raw_xmss_claims: Vec<LeanXmssClaim> = raw_lean_xmss.iter().map(|(pk, message, _)| (*pk, *message)).collect();
    let raw_lean_sphincs_claims: Vec<LeanSphincsClaim> = raw_lean_sphincs
        .iter()
        .map(|(pk, message, _)| (*pk, *message))
        .collect();
    let cover = plan_coverage(&raw_xmss_claims, &raw_lean_sphincs_claims, children, declare)?;
    if cover.lean_xmss.signers.is_empty() && cover.lean_sphincs.signers.is_empty() && da_root.is_none() {
        return Err(AggregateError::InvalidInput("nothing to publish"));
    }

    // The children are assumed checked. Nothing here verifies one: the replay only reads out of its proof the
    // summary `gen_verify` derives the guest's witness from, pinning the Merkle paths it reads, and fails on a proof
    // it cannot walk. A child that does not verify fails in the guest instead, which verifies every child in the VM,
    // so `prove` below returns the error.
    let _span = tracing::info_span!("Replay children").entered();
    // Each child's carried claim, its value read off the sums the batch runs on.
    let carried_points: Vec<Vec<F128>> = children.iter().map(|(_, proof)| proof.bytecode_point.clone()).collect();
    let carried_sums = bytecode_sums::<P>(&carried_points);
    let carried: Vec<DeferredBytecodeClaim> = carried_points
        .into_iter()
        .zip(&carried_sums)
        .map(|(point, sums)| DeferredBytecodeClaim::from_sums(point, sums))
        .collect();
    let child_da: Vec<[u8; 32]> = children
        .iter()
        .map(|(claims, _)| verifier::da::digest(claims.da_commitment))
        .collect();
    let mut public_inputs = Vec::with_capacity(children.len());
    for ((claims, _), defer) in children.iter().zip(&carried) {
        public_inputs.push(public_input(claims, defer));
    }
    // One single-threaded replay per worker: nothing inside dispatches.
    let bytecode = scalar_bytecode();
    let summaries = P::map_collect(children.len(), |i| {
        let pi = public_input_bytes(&public_inputs[i]);
        verifier::replay_unchecked(bytecode, &pi, &children[i].1.proof)
    });
    let mut replayed = Vec::with_capacity(children.len());
    for (pi, summary) in public_inputs.into_iter().zip(summaries) {
        let summary = summary.map_err(|_| AggregateError::InvalidChild)?;
        replayed.push((pi, summary));
    }

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
    let fs_seed = fs_seed();
    hints.push("fs_seed", vec![fs_seed[0], fs_seed[1]]);
    // Both lists in the guest's order, leanXMSS first: each one's split, its declared
    // claims, then its duplicates.
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
    // Each slot is hinted as an offset into its scheme's region, which is how one
    // range check keeps a scheme's writers off the other's claims.
    let lean_xmss_hints = P::map_collect(raw_lean_xmss.len(), |i| {
        let (pk, message, sig) = &raw_lean_xmss[i];
        lean_xmss_hints(pk, sig, message)
    });
    for (&offset, sub) in cover.lean_xmss.raw.iter().zip(lean_xmss_hints) {
        hints.push("raw_index", vec![count(offset)]);
        for (name, entry) in sub? {
            hints.push(name, entry);
        }
    }
    let lean_sphincs_hints = P::map_collect(raw_lean_sphincs.len(), |i| {
        let (pk, message, sig) = &raw_lean_sphincs[i];
        lean_sphincs_hints(pk, sig, message)
    });
    for (&offset, sub) in cover.lean_sphincs.raw.iter().zip(lean_sphincs_hints) {
        hints.push("sp_raw_index", vec![count(offset)]);
        for (name, entry) in sub? {
            hints.push(name, entry);
        }
    }

    // Each child's fresh claim, the one its verification raises, its value read off the sums the batch runs on.
    let fresh_points: Vec<Vec<F128>> = replayed
        .iter()
        .map(|(_, summary)| summary.bytecode_point.iter().copied().map(from_scalar).collect())
        .collect();
    let fresh_sums = bytecode_sums::<P>(&fresh_points);
    // Each child's witness is its own, one child per worker: nothing inside dispatches.
    let verified = P::map_collect(children.len(), |i| {
        let (pi, summary) = &replayed[i];
        let value = bytecode_value(&fresh_sums[i], &fresh_points[i]);
        gen_verify(kbc, *pi, &children[i].1.proof, summary, value)
    });
    let mut subs = Vec::with_capacity(children.len());
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
        hints.push("child_da", hash_to_scalars(&child_da[i]).to_vec());
        let (sub_hints, defer) = verified?;
        for (name, entry) in sub_hints {
            hints.push(name, entry);
        }
        subs.push(defer);
    }

    drop(_span);

    let defer = if children.is_empty() {
        let leaf = DeferredBytecodeClaim::leaf();
        hints.push("leaf_defer", vec![leaf.bytecode_value]);
        leaf
    } else {
        let _span = tracing::info_span!("Batch deferred claims").entered();
        // Each child's fresh claim, then its carried one: the batch's order.
        let sums = fresh_sums
            .into_iter()
            .zip(carried_sums)
            .flat_map(|(fresh, carried)| [fresh, carried]);
        let (agg_hints, reduced) =
            aggregate_deferred_claims::<P>(&subs, &carried, sums.collect()).ok_or(AggregateError::ProvingFailed)?;
        for (name, entry) in agg_hints {
            hints.push(name, entry);
        }
        reduced
    };

    let mut da_digest = child_da.get(da_pick).copied().unwrap_or_default();
    if let Some(matrix) = blobs {
        let commitment = matrix.top_root();
        let n_rows = matrix.n_blobs();
        da_digest = verifier::da::digest(Some(commitment));
        hints.push(
            "da_challenge",
            vec![from_scalar(verifier::da::membership_challenge(&commitment))],
        );
        hints.push("da_n_blobs", vec![count(n_rows)]);
        // Padding rows are constants the guest bakes, so only the real rows'
        // symbols ride the stream.
        for j in 0..CELLS_PER_ROW {
            for cell in matrix.column(j).expect("a column below CELLS_PER_ROW") {
                hints.push("da_symbols", cell.iter().map(|&w| F128::from(w)).collect());
            }
        }
    }
    hints.push("da_pick", vec![count(da_pick)]);

    let public_input = statement_digest(&cover.lean_xmss.signers, &cover.lean_sphincs.signers, da_digest, &defer);
    let mut program = assembled::<P>().clone();
    #[cfg(test)]
    if let Some(forge) = FORGE.with(|forge| forge.borrow_mut().take()) {
        forge(&mut hints);
    }
    hints.install::<P>(&mut program);
    let (proof, stats) = P::prove(&program, public_input.map(|x| to_scalar(&x)), log_inv_rate).map_err(|error| {
        tracing::debug!(%error, "proving failed");
        AggregateError::ProvingFailed
    })?;
    let claims = AggregateClaims {
        lean_xmss: cover.lean_xmss.signers,
        lean_sphincs: cover.lean_sphincs.signers,
        da_commitment: da_root,
    };
    let proof = AggregateProof {
        bytecode_point: defer.bytecode_point,
        proof,
    };
    Ok((claims, proof, stats))
}
