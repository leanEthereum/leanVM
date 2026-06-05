#![cfg_attr(not(test), allow(unused_crate_dependencies))]
pub mod benchmark;
mod bytecode_claims;
mod compilation;
mod error;
mod multi_message_aggregation;
mod single_message_aggregation;

use backend::{Evaluation, Proof, ProofError, RawProof, poseidon_hash_slice};
pub use compilation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN,
    get_aggregation_bytecode, init_aggregation_bytecode,
};
pub use error::AggregationError;
pub use lean_prover::ProverError;
use lean_prover::verify_execution::verify_execution;
use lean_vm::{DIGEST_LEN, EF, F};
pub use multi_message_aggregation::{
    MultiMessageAggregateSignature, merge_single_message_aggregates, split_multi_message_aggregate,
    split_multi_message_aggregate_by_msg, verify_multi_message_aggregate,
};
pub use single_message_aggregation::{
    SingleMessageAggregateSignature, SingleMessageInfo, aggregate_single_msg_signatures,
    verify_single_message_aggregate,
};

#[allow(missing_debug_implementations)]
pub struct InnerVerified {
    pub input_data: Vec<F>,
    pub input_data_hash: [F; DIGEST_LEN],
    pub bytecode_evaluation: Evaluation<EF>,
    pub raw_proof: RawProof<F>,
    pub sorted_table_perm: Vec<usize>,
}

// The LZ4 size prefix is attacker-controlled; cap it before allocating. Real
// multisigs compress to ~1x (high-entropy proof + hashes), so 8x is ample.
const MAX_DECOMPRESS_RATIO: usize = 8;

pub(crate) fn decompress_size_prepended_bounded(bytes: &[u8]) -> Option<Vec<u8>> {
    let declared = u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?) as usize;
    if declared > bytes.len().saturating_mul(MAX_DECOMPRESS_RATIO) {
        return None;
    }
    lz4_flex::decompress_size_prepended(bytes).ok()
}

pub(crate) fn verify_inner(input_data: Vec<F>, proof: Proof<F>) -> Result<InnerVerified, ProofError> {
    let input_data_hash = poseidon_hash_slice(&input_data);
    let bytecode = get_aggregation_bytecode();
    let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, proof)?;
    Ok(InnerVerified {
        input_data,
        input_data_hash,
        bytecode_evaluation: verif.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verif.sorted_table_perm,
    })
}
