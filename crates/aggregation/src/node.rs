//! The entry point that proves one node of an aggregation tree. The witness streams it pushes, and their order, are
//! transcribed in Lean as `formal/Statement/LeanVmGuestProver.lean`'s `honestPushes`: a change here lands there too.

use super::cells::count;
use super::child::gen_verify;
use super::coverage::{plan_coverage, sorted_firsts};
use super::deferred::{DeferredBytecodeClaim, aggregate_deferred_claims, bytecode_sums};
use super::error::AggregateError;
use super::guest::{fs_seed, unified_guest};
#[cfg(test)]
use super::hints::FORGE;
use super::hints::{Hints, lean_sphincs_hints, lean_xmss_hints};
use super::proof::{AggregateProof, is_sorted};
use super::statement::{Claim, claim_cells, claim_lists, list_split, statement_digest};
use super::{AggregateClaims, MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE, OutputClaims};
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
/// Run one call at a time: two would share the pool and hold both proofs' memory (`lean_vm::aggregate` waits).
///
/// # WARNING
/// - Signatures and children must be valid (children checked with [`AggregateProof::verify`]):
///   otherwise proving fails.
/// - Call [`P::init`](Prover::init) once before the first.
pub fn aggregate<P: Prover>(
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
            let root = Some(matrix.commitment());
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
    let child_lists: Vec<[Vec<Claim>; 2]> = children.iter().map(|(claims, _)| claim_lists(claims)).collect();
    if !child_lists.iter().all(is_sorted) {
        return Err(AggregateError::InvalidChild);
    }
    // The raw signatures sorted on their claims, repeats dropped: on the whole (pubkey, message) pair, so a signer may
    // appear once per message, and one claim needs one signature, whatever leaf index a leanXMSS one carries.
    let raw_claims: [Vec<Claim>; 2] = [
        raw_lean_xmss
            .iter()
            .map(|(pk, message, _)| [pk.to_bytes(), *message])
            .collect(),
        raw_lean_sphincs
            .iter()
            .map(|(pk, message, _)| [pk.to_bytes(), *message])
            .collect(),
    ];
    let raw_order = [sorted_firsts(&raw_claims[0]), sorted_firsts(&raw_claims[1])];
    let raw_sorted = [0, 1].map(|s| raw_order[s].iter().map(|&i| raw_claims[s][i]).collect());
    let cover = plan_coverage(&raw_sorted, &child_lists, declare)?;
    if cover.iter().all(|region| region.signers.is_empty()) && da_root.is_none() {
        return Err(AggregateError::InvalidInput("nothing to publish"));
    }

    // Nothing here verifies a child (see `AGENTS.md`): the replay reads out of its proof the summary `gen_verify`
    // builds the guest's witness from, and fails only on a proof it cannot walk.
    let _span = tracing::info_span!("Replay children").entered();
    // The batch's claims and their sums, each child's fresh one, filled in with its witness, then its carried one.
    let mut claims = Vec::with_capacity(2 * children.len());
    let mut sums = Vec::with_capacity(2 * children.len());
    let mut public_inputs = Vec::with_capacity(children.len());
    for (i, (child, proof)) in children.iter().enumerate() {
        let carried_sums = bytecode_sums::<P>(&proof.bytecode_point);
        let defer = DeferredBytecodeClaim::from_sums(proof.bytecode_point.clone(), &carried_sums);
        public_inputs.push(statement_digest(&child_lists[i], child.da_commitment, &defer));
        claims.push(DeferredBytecodeClaim {
            bytecode_point: Vec::new(),
            bytecode_value: F128::ZERO,
        });
        claims.push(defer);
        sums.push(Vec::new());
        sums.push(carried_sums);
    }
    // One child per worker, nothing inside dispatching: its replay's fresh bytecode point and its witness.
    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    let verified = P::map_collect(children.len(), |i| {
        let pi = public_input_bytes(&public_inputs[i]);
        let proof = &children[i].1.proof;
        let guest = unified_guest();
        let summary = verifier::replay_unchecked(guest.stacked_bytecode().len(), guest.fiat_shamir_iv(), &pi, proof)
            .map_err(|_| AggregateError::InvalidChild)?;
        let fresh: Vec<F128> = summary.bytecode_point.iter().copied().map(from_scalar).collect();
        Ok((fresh, gen_verify(kbc, proof, &summary)?))
    });
    for child in &verified {
        if let Err(error) = child {
            return Err(*error);
        }
    }
    drop(_span);

    let _span = tracing::info_span!("Build witness").entered();
    // Each raw signature's witness, leanXMSS first, one per worker.
    let n_lean_xmss = raw_order[0].len();
    let signatures = P::map_collect(n_lean_xmss + raw_order[1].len(), |i| {
        if i < n_lean_xmss {
            let (pk, message, sig) = &raw_lean_xmss[raw_order[0][i]];
            lean_xmss_hints(pk, sig, message)
        } else {
            let (pk, message, sig) = &raw_lean_sphincs[raw_order[1][i - n_lean_xmss]];
            lean_sphincs_hints(pk, sig, message)
        }
    });
    let mut hints = Hints::default();
    let mut meta = Vec::new();
    for (region, order) in cover.iter().zip(&raw_order) {
        meta.extend([
            count(region.signers.len()),
            count(region.dups.len()),
            count(order.len()),
        ]);
    }
    meta.extend([count(children.len()), count(usize::from(blobs.is_some()))]);
    hints.push("meta", meta);
    hints.push("fs_seed", fs_seed().to_vec());
    // Both lists in the guest's order, leanXMSS first: each one's split, its declared claims, then its duplicates.
    for region in &cover {
        if !region.signers.is_empty() {
            hints.push("signers_split", list_split(region.signers.len()));
        }
        for claim in &region.signers {
            hints.push("claims", claim_cells(claim));
        }
    }
    for region in &cover {
        for claim in &region.dups {
            hints.push("dup_claims", claim_cells(claim));
        }
    }
    // Each slot is hinted as an offset into its scheme's region, which is how one range check keeps a scheme's
    // writers off the other's claims.
    let mut signatures = signatures.into_iter();
    for (region, name) in cover.iter().zip(["raw_index", "sp_raw_index"]) {
        for (&offset, signature) in region.raw.iter().zip(&mut signatures) {
            hints.push_count(name, offset);
            hints.extend(signature?);
        }
    }

    // Each child's slots, its carried claim, its DA digest and its verification's witness.
    for (i, child) in verified.into_iter().enumerate() {
        let (fresh, verified) = child?;
        let lists = &child_lists[i];
        hints.push("child_meta", vec![count(lists[0].len()), count(lists[1].len())]);
        for region in &cover {
            let offsets = &region.children[i];
            if offsets.is_empty() {
                continue;
            }
            hints.push("signers_split", list_split(offsets.len()));
            // Strictly increasing slots go as gaps (`child_claim_list_mono`).
            let mono = offsets.is_sorted_by(|a, b| a < b);
            hints.push_count("child_mono", usize::from(mono));
            let mut next = 0;
            for &offset in offsets {
                if mono {
                    hints.push_count("child_claim_gap", offset - next);
                    next = offset + 1;
                } else {
                    hints.push_count("child_claim_index", offset);
                }
            }
        }
        hints.push("child_defer", claims[2 * i + 1].cells());
        let child_da = verifier::da::digest(children[i].0.da_commitment);
        hints.push("child_da", hash_to_scalars(&child_da).to_vec());
        hints.extend(verified);
        sums[2 * i] = bytecode_sums::<P>(&fresh);
        claims[2 * i] = DeferredBytecodeClaim::from_sums(fresh, &sums[2 * i]);
    }
    drop(_span);

    let defer = if children.is_empty() {
        let leaf = DeferredBytecodeClaim::leaf();
        hints.push("leaf_defer", vec![leaf.bytecode_value]);
        leaf
    } else {
        let _span = tracing::info_span!("Batch deferred claims").entered();
        let (batch_hints, reduced) = aggregate_deferred_claims::<P>(&public_inputs, &claims, sums);
        hints.extend(batch_hints);
        reduced
    };

    if let Some(matrix) = blobs {
        let commitment = matrix.commitment();
        hints.push(
            "da_challenge",
            vec![from_scalar(verifier::da::membership_challenge(&commitment))],
        );
        hints.push_count("da_n_blobs", matrix.n_blobs());
        // Padding rows are constants the guest bakes, so only the real rows' symbols ride the stream, blob by blob.
        for i in 0..matrix.n_blobs() {
            for j in 0..CELLS_PER_ROW {
                let cell = matrix.cell(i, j).expect("a cell of a blob below n_blobs");
                hints.push("da_symbols", cell.iter().map(|&w| F128::from(w)).collect());
            }
        }
    }
    hints.push_count("da_pick", da_pick);

    #[cfg(test)]
    if let Some(forge) = FORGE.with(|forge| forge.borrow_mut().take()) {
        forge(&mut hints);
    }
    let signers = cover.map(|region| region.signers);
    let public_input = statement_digest(&signers, da_root, &defer).map(|x| to_scalar(&x));
    let (proof, stats) = P::prove(unified_guest(), &hints.witness(), public_input, log_inv_rate).map_err(|error| {
        tracing::debug!(%error, "proving failed");
        AggregateError::ProvingFailed
    })?;
    let [lean_xmss, lean_sphincs] = signers;
    let claims = AggregateClaims {
        lean_xmss: lean_xmss
            .iter()
            .map(|[pk, message]| (LeanXmssPublicKey::from_bytes(pk), *message))
            .collect(),
        lean_sphincs: lean_sphincs
            .iter()
            .map(|[pk, message]| (LeanSphincsPublicKey::from_bytes(pk), *message))
            .collect(),
        da_commitment: da_root,
    };
    let proof = AggregateProof {
        bytecode_point: defer.bytecode_point,
        proof,
    };
    Ok((claims, proof, stats))
}
