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

/// Tune the VM memory policy for the prover's churn of huge buffers.
///
/// **Disable Transparent Huge Pages for this process.** On Zen4 (and likely other x86 with
/// physically-indexed L2/L3), when the kernel promotes the allocator's large arenas to
/// 2 MB huge pages, the prover's strided multilinear/NTT array access collapses into a few
/// cache sets — measured **+217% cache-misses, IPC 0.85 → 0.51, +50% wall time** on
/// `fancy-aggregation`. It's intermittent (only fires when 2 MB-contiguous memory is free
/// for THP promotion), which is what made it so hard to pin down. `prctl(PR_SET_THP_DISABLE)`
/// is process-local and overrides even a system-wide `THP=always`. No-op off Linux (macOS
/// has no THP — Apple silicon was never affected). Applies under any allocator.
// Not `const`: the body is non-empty (and non-const) on Linux; it only looks empty elsewhere.
#[allow(clippy::missing_const_for_fn)]
pub fn tune_allocator() {
    // Keep the arena's slabs on 4 KB pages.
    #[cfg(target_os = "linux")]
    unsafe {
        libc::prctl(libc::PR_SET_THP_DISABLE, 1, 0, 0, 0);
    }
}

/// Call once before proving. Compiles the aggregation program and precomputes DFT twiddles.
pub fn setup_prover() {
    tune_allocator();
    parallel::init(); // construct the thread pool up front (was done by `zk_alloc::begin_phase`)
    rec_aggregation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::init_aggregation_bytecode();
}

/// Bump-arena allocator.
///
/// To enable, set it as the `#[global_allocator]` in your binary and call [`init_allocator`]
/// once at startup. Then bracket each proving call with [`begin_phase`] / [`end_phase`] and
/// **clone the outputs after [`end_phase`]** so the cloned copy lands in the system allocator
/// before the next [`begin_phase`] resets the arena slabs.
///
/// See `tests/test_zk_alloc.rs` for a runnable end-to-end example.
pub use zk_alloc::{ZkAllocator, begin_phase, end_phase, init as init_allocator};
