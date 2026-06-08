use crate::error::AggregationError;
use backend::*;
use lean_prover::fiat_shamir_domain_sep;
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_vm::*;
use tracing::instrument;
use xmss::CHAIN_LENGTH;
use xmss::make_tweak;
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, PUB_KEY_FLAT_SIZE, TWEAK_TYPE_CHAIN, TWEAK_TYPE_ENCODING, TWEAK_TYPE_MERKLE,
    TWEAK_TYPE_WOTS_PK, V, WOTS_SIG_SIZE_FE, XmssPublicKey, XmssSignature,
};

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};

use crate::InnerVerified;
use crate::bytecode_claims::compute_bytecode_value_at;
use crate::bytecode_claims::flatten_bytecode_claim;
use crate::bytecode_claims::reduce_bytecode_claims;
use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, N_MERKLE_CHUNKS_FOR_SLOT,
    PREAMBLE_MEMORY_LEN, SINGLE_MESSAGE_FLAG, get_aggregation_bytecode, single_message_input_data_size_padded,
    try_get_aggregation_bytecode,
};
use crate::decompress_size_prepended_bounded;
use crate::verify_inner;

/// Number of tweaks in the table: 1 encoding + V*CHAIN_LENGTH chains + 1 wots_pk + LOG_LIFETIME merkle
pub(crate) const N_TWEAKS: usize = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME;
/// All tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0].
pub(crate) const TWEAK_SLOT_SIZE: usize = 4;
pub(crate) const TWEAK_TABLE_SIZE_FE_PADDED: usize = (N_TWEAKS * TWEAK_SLOT_SIZE).next_multiple_of(DIGEST_LEN);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleMessageInfo {
    pub message: [F; MESSAGE_LEN_FE],
    pub slot: u32,
    pub pubkeys: Vec<XmssPublicKey>,
    pub bytecode_claim: Evaluation<EF>, // value is trusted to be correct (should be recomputed when receiving a proof from an untrusted source)
}

// Aggregation of many signatures, all sharing the same (message, slot)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SingleMessageAggregateSignature {
    pub info: SingleMessageInfo,
    pub proof: ExecutionProof,
}

impl Serialize for SingleMessageInfo {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.message, &self.slot, &self.pubkeys, &self.bytecode_claim.point).serialize(s)
    }
}

impl<'de> Deserialize<'de> for SingleMessageInfo {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (message, slot, pubkeys, bytecode_claim_point) =
            <([F; MESSAGE_LEN_FE], u32, Vec<XmssPublicKey>, MultilinearPoint<EF>)>::deserialize(d)?;
        let bytecode =
            try_get_aggregation_bytecode().ok_or_else(|| serde::de::Error::custom("bytecode not initialized"))?;
        if bytecode_claim_point.len() != bytecode.cumulated_n_vars() {
            return Err(serde::de::Error::custom("invalid bytecode point"));
        }
        check_single_message_pubkeys(&pubkeys).map_err(serde::de::Error::custom)?;
        let bytecode_value = compute_bytecode_value_at(&bytecode_claim_point);
        Ok(Self {
            message,
            slot,
            pubkeys,
            bytecode_claim: Evaluation::new(bytecode_claim_point, bytecode_value),
        })
    }
}

pub(crate) fn check_single_message_pubkeys(pubkeys: &[XmssPublicKey]) -> Result<(), &'static str> {
    if pubkeys.is_empty() {
        return Err("pubkeys must be non-empty");
    }
    if pubkeys.len() > MAX_XMSS_AGGREGATED {
        return Err("too many pubkeys (exceeds MAX_XMSS_AGGREGATED)");
    }
    if !pubkeys.windows(2).all(|w| w[0] < w[1]) {
        return Err("pubkeys must be strictly sorted (no duplicates)");
    }
    Ok(())
}

impl SingleMessageAggregateSignature {
    pub fn compress(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn decompress(bytes: &[u8]) -> Option<Self> {
        let decompressed = decompress_size_prepended_bounded(bytes)?;
        let (value, rest) = postcard::take_from_bytes::<Self>(&decompressed).ok()?;
        rest.is_empty().then_some(value)
    }
}

impl SingleMessageInfo {
    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_claim)
    }

    pub(crate) fn build_input_data(&self) -> Vec<F> {
        let tweak_table = compute_tweak_table(self.slot);
        let tweaks_hash = poseidon_hash_slice(&tweak_table);
        build_single_message_input_data(
            self.pubkeys.len(),
            &hash_pubkeys(&self.pubkeys),
            &self.message,
            self.slot,
            &tweaks_hash,
            &self.bytecode_claim_flat(),
            get_aggregation_bytecode(),
        )
    }
}

pub(crate) fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> [F; DIGEST_LEN] {
    let flat: Vec<F> = pub_keys.iter().flat_map(|pk| pk.flaten().into_iter()).collect();
    poseidon_hash_slice(&flat)
}

/// Tweak slots are 4-FE [tw[0], tw[1], 0, 0]
fn compute_tweak_table(slot: u32) -> ArenaVec<F> {
    let mut table = ArenaVec::new();

    let push_padded = |table: &mut ArenaVec<F>, tweak_type: usize, sub_position: usize, index: u32| {
        table.extend(make_tweak(tweak_type, sub_position, index));
        table.extend(std::iter::repeat_n(F::ZERO, 2));
    };

    // Encoding tweak
    push_padded(&mut table, TWEAK_TYPE_ENCODING, 0, slot);

    // Chain tweaks
    for i in 0..V {
        for s in 0..CHAIN_LENGTH {
            push_padded(&mut table, TWEAK_TYPE_CHAIN, i * CHAIN_LENGTH + s, slot);
        }
    }

    // WOTS_PK tweak
    push_padded(&mut table, TWEAK_TYPE_WOTS_PK, 0, slot);

    // Merkle tweaks
    for level in 0..LOG_LIFETIME {
        let parent_index = ((slot as u64) >> (level + 1)) as u32;
        push_padded(&mut table, TWEAK_TYPE_MERKLE, level + 1, parent_index);
    }
    table.resize(TWEAK_TABLE_SIZE_FE_PADDED, F::ZERO);
    table
}

fn compute_merkle_chunks_for_slot(slot: u32) -> Vec<F> {
    (0..N_MERKLE_CHUNKS_FOR_SLOT)
        .map(|chunk_idx| {
            let nibble = (slot >> (chunk_idx * 4)) & 0xF;
            F::from_u32((!nibble) & 0xF)
        })
        .collect()
}

/// Layout: [prefix(8) | bytecode_claim_padded | initial_fiat_shamir_cap(8) | pubkeys_hash | message | merkle_chunks | tweaks_hash].
pub(crate) fn build_single_message_input_data(
    n_sigs: usize,
    pubkeys_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: &[F; DIGEST_LEN],
    bytecode_claim_flat: &[F],
    bytecode: &Bytecode,
) -> Vec<F> {
    let log_size = bytecode.log_size();
    let mut data = Vec::with_capacity(single_message_input_data_size_padded(log_size));
    data.push(F::from_usize(SINGLE_MESSAGE_FLAG));
    data.push(F::from_usize(n_sigs));
    data.resize(DIGEST_LEN, F::ZERO);
    data.extend_from_slice(bytecode_claim_flat);
    let claim_padding = bytecode_claim_flat.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_flat.len();
    data.extend(std::iter::repeat_n(F::ZERO, claim_padding));
    data.extend_from_slice(&fiat_shamir_domain_sep(bytecode));
    data.extend_from_slice(pubkeys_hash);
    data.extend_from_slice(message);
    data.extend(compute_merkle_chunks_for_slot(slot));
    data.extend_from_slice(tweaks_hash);
    data
}

fn encode_wots_signature(sig: &XmssSignature) -> ArenaVec<F> {
    let mut data = ArenaVec::with_capacity(WOTS_SIG_SIZE_FE);
    data.extend_from_slice(&sig.wots_signature.randomness);
    for digest in &sig.wots_signature.chain_tips {
        data.extend_from_slice(digest);
    }
    debug_assert_eq!(data.len(), WOTS_SIG_SIZE_FE);
    data
}

// assumes `bytecode_value` in SingleMessageAggregateSignature::proof is correct (it should not be read / deserialized from an untrusted source)
pub fn verify_single_message_aggregate(sig: &SingleMessageAggregateSignature) -> Result<InnerVerified, ProofError> {
    check_single_message_pubkeys(&sig.info.pubkeys).map_err(|_| ProofError::InvalidProof)?;
    verify_inner(sig.info.build_input_data(), sig.proof.proof.clone())
}

/// Aggregate raw XMSS signatures and previously aggregated single-message signatures.
/// Single-message = one shared (message, slot).
#[instrument(skip_all)]
pub fn aggregate_single_message_signatures(
    children: &[SingleMessageAggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: [F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
) -> Result<SingleMessageAggregateSignature, AggregationError> {
    aggregate_single_message_signatures_with_min_padding(
        children,
        raw_xmss,
        message,
        slot,
        log_inv_rate,
        BTreeMap::new(),
    )
}

pub(crate) fn aggregate_single_message_signatures_with_min_padding(
    children: &[SingleMessageAggregateSignature],
    mut raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: [F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
    min_table_log_n_rows: BTreeMap<Table, usize>,
) -> Result<SingleMessageAggregateSignature, AggregationError> {
    let _phase = enter_phase();
    if children.len() > MAX_RECURSIONS {
        return Err(AggregationError::LimitExceeded {
            what: "aggregation children",
            actual: children.len(),
            max: MAX_RECURSIONS,
        });
    }
    for child in children {
        if child.info.message != message {
            return Err(AggregationError::InconsistentChildren {
                what: "all children of a single-message aggregation must share the same message",
            });
        }
        if child.info.slot != slot {
            return Err(AggregationError::InconsistentChildren {
                what: "all children of a single-message aggregation must share the same slot",
            });
        }
    }
    let message = &message;
    let verified_children: Vec<InnerVerified> = children
        .iter()
        .map(verify_single_message_aggregate)
        .collect::<Result<_, _>>()?;
    let children: Vec<&[XmssPublicKey]> = children.iter().map(|c| c.info.pubkeys.as_slice()).collect();
    let children = children.as_slice();

    raw_xmss.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw_xmss.dedup_by(|(a, _), (b, _)| a == b);

    let n_recursions = children.len();
    let raw_count = raw_xmss.len();
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_claim_size = bytecode.bytecode_claim_size();

    // Build global_pub_keys as sorted deduplicated union
    let mut global_pub_keys: Vec<XmssPublicKey> = raw_xmss.iter().map(|(pk, _)| pk.clone()).collect();
    for child_pub_keys in children.iter() {
        global_pub_keys.extend_from_slice(child_pub_keys);
    }
    global_pub_keys.sort();
    global_pub_keys.dedup();
    let n_sigs = global_pub_keys.len();
    if n_sigs == 0 {
        return Err(AggregationError::EmptyAggregation {
            what: "aggregated public keys",
        });
    }
    if n_sigs > MAX_XMSS_AGGREGATED {
        return Err(AggregationError::LimitExceeded {
            what: "aggregated public keys",
            actual: n_sigs,
            max: MAX_XMSS_AGGREGATED,
        });
    }

    let tweak_table = compute_tweak_table(slot);
    let tweaks_hash = poseidon_hash_slice(&tweak_table);

    let reduced_claims = reduce_bytecode_claims(&verified_children);

    let pub_input_data = build_single_message_input_data(
        n_sigs,
        &hash_pubkeys(&global_pub_keys),
        message,
        slot,
        &tweaks_hash,
        &reduced_claims.final_claim_flat(),
        bytecode,
    );
    let public_input = poseidon_hash_slice(&pub_input_data);

    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();

    let wots_blobs: ArenaVec<ArenaVec<F>> = raw_xmss.iter().map(|(_, sig)| encode_wots_signature(sig)).collect();
    let xmss_merkle_node_blobs: ArenaVec<ArenaVec<F>> = raw_xmss
        .iter()
        .flat_map(|(_, sig)| sig.merkle_proof.iter().map(|d| ArenaVec::from_slice(d)))
        .collect();

    let raw_indices: ArenaVec<F> = raw_xmss
        .iter()
        .map(|(pk, _)| {
            let pos = global_pub_keys.binary_search(pk).unwrap();
            claimed.insert(pk.clone());
            F::from_usize(pos)
        })
        .collect();

    let mut sub_indices_blobs: ArenaVec<ArenaVec<F>> = ArenaVec::with_capacity(n_recursions);
    let mut bytecode_value_hint_blobs: ArenaVec<ArenaVec<F>> = ArenaVec::with_capacity(n_recursions);
    let mut inner_bytecode_claim_blobs: ArenaVec<ArenaVec<F>> = ArenaVec::with_capacity(n_recursions);
    let mut proof_transcript_blobs: ArenaVec<ArenaVec<F>> = ArenaVec::with_capacity(n_recursions);
    let mut table_sort_perm_blobs: ArenaVec<ArenaVec<F>> = ArenaVec::with_capacity(n_recursions);

    let claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);

    for (i, child_pub_keys) in children.iter().enumerate() {
        // sub_indices: [idx_0, idx_1, ...] into global_pub_keys + dup_pub_keys.
        // The length n_sub is communicated via the matching `aggregate_sizes` entry.
        let mut sub_indices = Vec::with_capacity(child_pub_keys.len());
        for pubkey in *child_pub_keys {
            if claimed.insert(pubkey.clone()) {
                let pos = global_pub_keys.binary_search(pubkey).unwrap();
                sub_indices.push(F::from_usize(pos));
            } else {
                sub_indices.push(F::from_usize(n_sigs + dup_pub_keys.len()));
                dup_pub_keys.push(pubkey.clone());
            }
        }
        sub_indices_blobs.push(ArenaVec::from_slice(&sub_indices));

        let v = &verified_children[i];
        bytecode_value_hint_blobs.push(ArenaVec::from_slice(
            v.bytecode_evaluation.value.as_basis_coefficients_slice(),
        ));
        inner_bytecode_claim_blobs.push(ArenaVec::from_slice(
            &v.input_data[BYTECODE_CLAIM_OFFSET..][..claim_size_padded],
        ));
        proof_transcript_blobs.push(ArenaVec::from_slice(&v.raw_proof.transcript));
        table_sort_perm_blobs.push(v.sorted_table_perm.iter().map(|&i| F::from_usize(i)).collect());
    }

    let n_dup = dup_pub_keys.len();
    if n_dup > MAX_XMSS_DUPLICATES {
        return Err(AggregationError::LimitExceeded {
            what: "duplicate public keys",
            actual: n_dup,
            max: MAX_XMSS_DUPLICATES,
        });
    }

    let mut pubkeys_blob: ArenaVec<F> = ArenaVec::with_capacity((n_sigs + n_dup) * PUB_KEY_FLAT_SIZE);
    for pk in &global_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }
    for pk in &dup_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }

    let (merkle_leaf_blobs, merkle_path_blobs) =
        extract_merkle_hint_blobs(verified_children.iter().map(|v| &v.raw_proof));

    let aggregate_sizes: ArenaVec<F> = sub_indices_blobs.iter().map(|b| F::from_usize(b.len())).collect();

    let mut hints = Hints::default();
    hints.insert(
        bytecode,
        "input_data_num_chunks",
        arena_vec![arena_vec![F::from_usize(pub_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert(
        bytecode,
        "input_data",
        arena_vec![ArenaVec::from_slice(&pub_input_data)],
    );
    // [n_recursions, n_dup, pubkeys_len, n_raw_xmss]
    hints.insert(
        bytecode,
        "meta",
        arena_vec![arena_vec![
            F::from_usize(n_recursions),
            F::from_usize(n_dup),
            F::from_usize(raw_count)
        ]],
    );
    hints.insert(bytecode, "pubkeys", arena_vec![pubkeys_blob]);
    hints.insert(bytecode, "raw_indices", arena_vec![raw_indices]);
    let fast_path = n_recursions == 1 && raw_count == 0 && dup_pub_keys.is_empty();
    let sub_indices_for_hints = if fast_path { ArenaVec::new() } else { sub_indices_blobs };
    hints.insert(bytecode, "sub_indices", sub_indices_for_hints);
    // Standard single-message aggregation (not a split).
    hints.insert(bytecode, "is_split", arena_vec![arena_vec![F::ZERO]]);
    hints.insert(bytecode, "bytecode_value_hint", bytecode_value_hint_blobs);
    hints.insert(bytecode, "inner_bytecode_claim", inner_bytecode_claim_blobs);
    hints.insert(
        bytecode,
        "proof_transcript_size",
        proof_transcript_blobs
            .iter()
            .map(|b| arena_vec![F::from_usize(b.len())])
            .collect(),
    );
    hints.insert(bytecode, "proof_transcript", proof_transcript_blobs);
    hints.insert(bytecode, "table_sort_perm", table_sort_perm_blobs);
    hints.insert(bytecode, "merkle_leaf", merkle_leaf_blobs);
    hints.insert(bytecode, "merkle_path", merkle_path_blobs);
    hints.insert(bytecode, "aggregate_sizes", arena_vec![aggregate_sizes]);
    hints.insert(bytecode, "tweak_table", arena_vec![tweak_table]);
    if n_recursions > 0 {
        hints.insert(
            bytecode,
            "bytecode_sumcheck_proof",
            arena_vec![ArenaVec::from_slice(&reduced_claims.sumcheck_transcript)],
        );
    }

    hints.insert(bytecode, "wots", wots_blobs);
    hints.insert(bytecode, "xmss_merkle_node", xmss_merkle_node_blobs);

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows,
    };
    let proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(SingleMessageAggregateSignature {
        info: SingleMessageInfo {
            message: *message,
            slot,
            pubkeys: global_pub_keys,
            bytecode_claim: reduced_claims.final_claim,
        },
        proof,
    })
}

/// return `([merkle_leafs], [merkle_paths])`
pub(crate) fn extract_merkle_hint_blobs<'a>(
    raw_proofs: impl IntoIterator<Item = &'a RawProof<F>>,
) -> (ArenaVec<ArenaVec<F>>, ArenaVec<ArenaVec<F>>) {
    raw_proofs
        .into_iter()
        .flat_map(|p| p.merkle_openings.iter())
        .map(|o| {
            let leaf = ArenaVec::from_slice(&o.leaf_data);
            let path: ArenaVec<F> = o.path.iter().flat_map(|d| d.iter().copied()).collect();
            (leaf, path)
        })
        .unzip()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compilation::init_aggregation_bytecode;
    use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

    /// Exercises the recursive-aggregation path when the inner proof has the
    /// extension-op table bigger than the execution table.
    #[test]
    fn test_recursive_aggregation_extension_table_bigger_than_execution() {
        init_aggregation_bytecode();

        let log_inv_rate = 2;
        let message = message_for_benchmark();
        let slot: u32 = BENCHMARK_SLOT;
        let signatures = get_benchmark_signatures();
        let raws_inner = signatures[0..10].to_vec();
        let raws_outer = signatures[10..12].to_vec();

        let extension_padding_log = 15;
        let mut min_padding: BTreeMap<Table, usize> = BTreeMap::new();
        min_padding.insert(Table::extension_op(), extension_padding_log);

        let inner = aggregate_single_message_signatures_with_min_padding(
            &[],
            raws_inner,
            message,
            slot,
            log_inv_rate,
            min_padding,
        )
        .unwrap();
        verify_single_message_aggregate(&inner).unwrap();

        let inner_metadata = inner.proof.metadata.as_ref().expect("inner metadata available");
        assert!(dbg!(inner_metadata.cycles) < 1usize << extension_padding_log,);

        let outer = aggregate_single_message_signatures(&[inner], raws_outer, message, slot, log_inv_rate).unwrap();
        verify_single_message_aggregate(&outer).unwrap();
    }
}
