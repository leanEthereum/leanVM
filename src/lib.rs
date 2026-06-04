use backend::*;

pub use backend::ProofError;
pub use rec_aggregation::{
    AggregationError, MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, MultiMessageAggregateSignature,
    ProverError, SingleMessageAggregateSignature, SingleMessageInfo, aggregate_single_msg_signatures,
    merge_single_message_aggregates, split_multi_message_aggregate, verify_multi_message_aggregate,
    verify_single_message_aggregate,
};
pub use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSecretKey, XmssSignature, xmss_key_gen, xmss_sign, xmss_verify};

pub type F = KoalaBear;

/// Call once before proving.
pub fn setup_prover() {
    parallel::init();
    rec_aggregation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::init_aggregation_bytecode();
}

/// Bump-arena allocator.
///
/// To enable, set it as the `#[global_allocator]` in your binary. Then bracket each proving
/// call with [`begin_phase`] / [`end_phase`] and **clone the outputs after [`end_phase`]** so
/// the cloned copy lands in the system allocator before the next [`begin_phase`] resets the
/// arena slabs.
///
/// See `tests/test_zk_alloc.rs` for a runnable end-to-end example.
pub use zk_alloc::{ZkAllocator, begin_phase, end_phase};
