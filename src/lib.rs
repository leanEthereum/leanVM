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

/// Explicit bump-arena allocator (never a `#[global_allocator]`).
///
/// [`enable_arena`] once, then bracket each proving call with [`begin_phase`] / [`end_phase`].
/// `ArenaVec` buffers bump from the arena inside a phase and use the system allocator outside one;
/// data that must outlive a phase needs the system allocator, since [`begin_phase`] resets the arena.
pub use zk_alloc::{begin_phase, enable_arena, end_phase};
