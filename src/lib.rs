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
/// Opt in once at startup with [`enable_arena`] (until then phases are inert and everything
/// uses the system allocator), then bracket each proving call with [`begin_phase`] /
/// [`end_phase`] and **clone the outputs after [`end_phase`]** so the copy lands in the system
/// allocator before the next [`begin_phase`] resets the arena slabs. Two ways to route proof
/// data through it:
///
/// - **Global:** set [`ZkAllocator`] as the binary's `#[global_allocator]` — every allocation
///   in a phase hits the arena. Simplest, but forces the process allocator on the whole binary.
/// - **Explicit ([`ProverAlloc`]):** leave the global allocator alone and put proof data in
///   `Vec<T, ProverAlloc>` / `Box<T, ProverAlloc>`. Only those containers use the arena, so a
///   library can opt in without dictating its consumers' global allocator.
///
/// See `tests/test_zk_alloc.rs` for a runnable end-to-end example.
pub use zk_alloc::{ProverAlloc, ZkAllocator, begin_phase, enable_arena, end_phase};
