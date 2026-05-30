use crate::error::AggregationError;
use backend::*;
use lean_prover::default_whir_config;
use lean_prover::fiat_shamir_domain_sep;
use lean_prover::prove_execution::ExecutionProof;
use lean_prover::prove_execution::prove_execution;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use utils::poseidon_hash_slice;

use crate::InnerVerified;
use crate::bytecode_claims::compute_bytecode_value_at;
use crate::bytecode_claims::flatten_bytecode_claim;
use crate::bytecode_claims::reduce_bytecode_claims;
use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, MULTI_MESSAGE_FLAG, PREAMBLE_MEMORY_LEN, get_aggregation_bytecode,
    try_get_aggregation_bytecode,
};
use crate::decompress_size_prepended_bounded;
use crate::single_message_aggregation::{
    SingleMessageAggregateSignature, SingleMessageInfo, check_single_message_pubkeys, extract_merkle_hint_blobs,
    verify_single_message_aggregate,
};
use crate::verify_inner;

/// A bundle of `n` single-message aggregate signatures with potentially distinct (message, slot) per component, attested by a single snark.
#[derive(Debug, Clone)]
pub struct MultiMessageAggregateSignature {
    pub info: Vec<SingleMessageInfo>,
    pub bytecode_claim: Evaluation<EF>, // value is trusted to be correct  (should be recomputed when receiving a proof from an untrusted source)
    pub proof: ExecutionProof,
}

impl Serialize for MultiMessageAggregateSignature {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.info, &self.bytecode_claim.point, &self.proof).serialize(s)
    }
}

impl<'de> Deserialize<'de> for MultiMessageAggregateSignature {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (info, bytecode_claim_point, proof) =
            <(Vec<SingleMessageInfo>, MultilinearPoint<EF>, ExecutionProof)>::deserialize(d)?;
        let bytecode =
            try_get_aggregation_bytecode().ok_or_else(|| serde::de::Error::custom("bytecode not initialized"))?;
        if bytecode_claim_point.len() != bytecode.cumulated_n_vars() {
            return Err(serde::de::Error::custom("invalid bytecode point"));
        }
        let bytecode_value = compute_bytecode_value_at(&bytecode_claim_point);
        Ok(MultiMessageAggregateSignature {
            info,
            bytecode_claim: Evaluation::new(bytecode_claim_point, bytecode_value),
            proof,
        })
    }
}

impl MultiMessageAggregateSignature {
    pub fn compress(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn decompress(bytes: &[u8]) -> Option<Self> {
        let decompressed = decompress_size_prepended_bounded(bytes)?;
        let (value, rest) = postcard::take_from_bytes::<Self>(&decompressed).ok()?;
        rest.is_empty().then_some(value)
    }

    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_claim)
    }
}

/// Layout: [prefix(8) | bytecode_claim_padded | initial_fiat_shamir_cap(8) | n × digest(8)].
fn build_multi_message_input_data(digests: &[[F; DIGEST_LEN]], bytecode_claim_flat: &[F]) -> Vec<F> {
    let n = digests.len();
    let claim_padded = bytecode_claim_flat.len().next_multiple_of(DIGEST_LEN);
    let domsep_offset = BYTECODE_CLAIM_OFFSET + claim_padded;
    let digests_offset = domsep_offset + DIGEST_LEN;
    let mut data = vec![F::ZERO; digests_offset + n * DIGEST_LEN];

    data[0] = F::from_usize(MULTI_MESSAGE_FLAG);
    data[1] = F::from_usize(n);
    // data[2..8] stays zero (prefix-chunk pad).

    data[BYTECODE_CLAIM_OFFSET..][..bytecode_claim_flat.len()].copy_from_slice(bytecode_claim_flat);
    let domsep = fiat_shamir_domain_sep(get_aggregation_bytecode());
    data[domsep_offset..][..DIGEST_LEN].copy_from_slice(&domsep);

    for (i, d) in digests.iter().enumerate() {
        data[digests_offset + i * DIGEST_LEN..][..DIGEST_LEN].copy_from_slice(d);
    }

    data
}

pub fn merge_single_message_aggregates(
    single_messages: Vec<SingleMessageAggregateSignature>,
    log_inv_rate: usize,
) -> Result<MultiMessageAggregateSignature, AggregationError> {
    let n_components = single_messages.len();
    if n_components == 0 {
        return Err(AggregationError::EmptyAggregation {
            what: "single-message components",
        });
    }
    if n_components > MAX_RECURSIONS {
        return Err(AggregationError::LimitExceeded {
            what: "single-message components",
            actual: n_components,
            max: MAX_RECURSIONS,
        });
    }
    let whir_config = default_whir_config(log_inv_rate);
    let bytecode = get_aggregation_bytecode();

    let verified_children: Vec<InnerVerified> = single_messages
        .iter()
        .map(verify_single_message_aggregate)
        .collect::<Result<_, _>>()?;

    let reduced_claims = reduce_bytecode_claims(&verified_children);

    let digests: Vec<[F; DIGEST_LEN]> = verified_children.iter().map(|v| v.input_data_hash).collect();
    let pub_input_data = build_multi_message_input_data(&digests, &reduced_claims.final_claim_flat());
    let public_input_digest = poseidon_hash_slice(&pub_input_data);

    let bytecode_value_hint_blobs: Vec<Vec<F>> = verified_children
        .iter()
        .map(|v| v.bytecode_evaluation.value.as_basis_coefficients_slice().to_vec())
        .collect();
    let component_layout_blobs: Vec<Vec<F>> = verified_children.iter().map(|v| v.input_data.clone()).collect();
    let proof_transcript_blobs: Vec<Vec<F>> = verified_children
        .iter()
        .map(|v| v.raw_proof.transcript.clone())
        .collect();
    let table_sort_perm_blobs: Vec<Vec<F>> = verified_children
        .iter()
        .map(|v| v.sorted_table_perm.iter().map(|&i| F::from_usize(i)).collect())
        .collect();
    let (merkle_leaf_blobs, merkle_path_blobs) =
        extract_merkle_hint_blobs(verified_children.iter().map(|v| &v.raw_proof));

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert(
        "input_data_num_chunks".to_string(),
        vec![vec![F::from_usize(pub_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    hints.insert("bytecode_value_hint".to_string(), bytecode_value_hint_blobs);
    hints.insert("component_layout".to_string(), component_layout_blobs);
    hints.insert(
        "proof_transcript_size".to_string(),
        proof_transcript_blobs
            .iter()
            .map(|b| vec![F::from_usize(b.len())])
            .collect(),
    );
    hints.insert("proof_transcript".to_string(), proof_transcript_blobs);
    hints.insert("table_sort_perm".to_string(), table_sort_perm_blobs);
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert(
        "bytecode_sumcheck_proof".to_string(),
        vec![reduced_claims.sumcheck_transcript],
    );

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows: Default::default(),
    };
    let execution_proof = prove_execution(bytecode, &public_input_digest, &witness, &whir_config, false)?;

    Ok(MultiMessageAggregateSignature {
        info: single_messages.into_iter().map(|sig| sig.info).collect(),
        bytecode_claim: reduced_claims.final_claim,
        proof: execution_proof,
    })
}

pub fn verify_multi_message_aggregate(sig: &MultiMessageAggregateSignature) -> Result<InnerVerified, ProofError> {
    if sig.info.is_empty() || sig.info.len() > MAX_RECURSIONS {
        return Err(ProofError::InvalidProof);
    }
    for info in &sig.info {
        check_single_message_pubkeys(&info.pubkeys).map_err(|_| ProofError::InvalidProof)?;
    }
    let digests = sig
        .info
        .iter()
        .map(|info| poseidon_hash_slice(&info.build_input_data()))
        .collect::<Vec<_>>();
    let input_data = build_multi_message_input_data(&digests, &sig.bytecode_claim_flat());
    verify_inner(input_data, sig.proof.proof.clone())
}

pub fn split_multi_message_aggregate_by_msg(
    multi_message: MultiMessageAggregateSignature,
    msg: [F; DIGEST_LEN],
    log_inv_rate: usize,
) -> Result<SingleMessageAggregateSignature, AggregationError> {
    let Some(index) = multi_message.info.iter().position(|info| info.message == msg) else {
        return Err(AggregationError::UnknownMessage);
    };
    if multi_message.info.iter().filter(|info| info.message == msg).count() > 1 {
        return Err(AggregationError::MultipleMessages);
    }
    split_multi_message_aggregate(multi_message, index, log_inv_rate)
}

/// Recover an independent single-message aggregate signature for the component at `index`
/// from a multi-message aggregate signature.
pub fn split_multi_message_aggregate(
    multi_message: MultiMessageAggregateSignature,
    index: usize,
    log_inv_rate: usize,
) -> Result<SingleMessageAggregateSignature, AggregationError> {
    let n_components = multi_message.info.len();
    if index >= n_components {
        return Err(AggregationError::InvalidSplitIndex { index, n_components });
    }
    if n_components > MAX_RECURSIONS {
        return Err(AggregationError::LimitExceeded {
            what: "multi-message components",
            actual: n_components,
            max: MAX_RECURSIONS,
        });
    }
    let whir_config = default_whir_config(log_inv_rate);
    let bytecode = get_aggregation_bytecode();

    let outer_verified = verify_multi_message_aggregate(&multi_message)?;

    let reduced_claims = reduce_bytecode_claims(std::slice::from_ref(&outer_verified));
    let bytecode_value_hint_blob = flatten_scalars_to_base(&[outer_verified.bytecode_evaluation.value]);
    let table_sort_perm_blob: Vec<F> = outer_verified
        .sorted_table_perm
        .iter()
        .map(|&i| F::from_usize(i))
        .collect();

    let mut outer_single_message = multi_message.info[index].clone();
    outer_single_message.bytecode_claim = reduced_claims.final_claim.clone();
    let ourer_input_data = outer_single_message.build_input_data();
    let outer_digest = poseidon_hash_slice(&ourer_input_data);

    let inner_input_data: Vec<F> = multi_message.info[index].build_input_data();

    let (merkle_leaf_blobs, merkle_path_blobs) =
        extract_merkle_hint_blobs(std::slice::from_ref(&outer_verified.raw_proof));
    let proof_transcript = outer_verified.raw_proof.transcript;
    let proof_transcript_size = vec![F::from_usize(proof_transcript.len())];

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert(
        "input_data_num_chunks".to_string(),
        vec![vec![F::from_usize(ourer_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert("input_data".to_string(), vec![ourer_input_data]);
    hints.insert("is_split".to_string(), vec![vec![F::ONE]]);
    hints.insert(
        "multi_message_meta".to_string(),
        vec![vec![F::from_usize(n_components), F::from_usize(index)]],
    );
    hints.insert(
        "inner_multi_message_layout".to_string(),
        vec![outer_verified.input_data],
    );
    hints.insert("kept_single_message_buff".to_string(), vec![inner_input_data]);
    hints.insert("bytecode_value_hint".to_string(), vec![bytecode_value_hint_blob]);
    hints.insert("proof_transcript_size".to_string(), vec![proof_transcript_size]);
    hints.insert("proof_transcript".to_string(), vec![proof_transcript]);
    hints.insert("table_sort_perm".to_string(), vec![table_sort_perm_blob]);
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert(
        "bytecode_sumcheck_proof".to_string(),
        vec![reduced_claims.sumcheck_transcript],
    );

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows: Default::default(),
    };
    let execution_proof = prove_execution(bytecode, &outer_digest, &witness, &whir_config, false)?;

    Ok(SingleMessageAggregateSignature {
        info: outer_single_message,
        proof: execution_proof,
    })
}
