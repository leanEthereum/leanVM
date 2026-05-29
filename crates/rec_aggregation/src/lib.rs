#![cfg_attr(not(test), allow(unused_crate_dependencies))]
mod aggregation;
pub mod benchmark;
mod bytecode_claims;
mod compilation;
mod error;
pub mod signatures_cache;

pub use aggregation::{
    AggregatedXMSS, AggregatedXMSSInfo, AggregatedXMSSInfoWithoutPubkeys, xmss_aggregate, xmss_verify_aggregation,
};
use backend::{Evaluation, Proof, ProofError, RawProof};
pub use benchmark::AggregationTopology;
pub use compilation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN,
    get_aggregation_bytecode, init_aggregation_bytecode,
};
pub use error::AggregationError;
pub use lean_prover::ProverError;
use lean_prover::verify_execution::verify_execution;
use lean_vm::{DIGEST_LEN, EF, F};
use utils::poseidon_compress_slice;

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
    let input_data_hash = poseidon_compress_slice(&input_data);
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

/// postcard-encode then lz4-compress. Inverse of `lz4_postcard_decode`.
pub(crate) fn lz4_postcard_encode<T: serde::Serialize>(value: &T) -> Vec<u8> {
    let encoded = postcard::to_allocvec(value).expect("postcard serialization failed");
    lz4_flex::compress_prepend_size(&encoded)
}

/// Inverse of `lz4_postcard_encode`. Returns `None` on either lz4 or postcard failure.
pub(crate) fn lz4_postcard_decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Option<T> {
    let decompressed = lz4_flex::decompress_size_prepended(bytes).ok()?;
    postcard::from_bytes(&decompressed).ok()
}
