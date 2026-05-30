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

/// Tune the allocator and VM memory policy for the prover's churn of huge buffers.
///
/// Two things, both before any heavy proving allocation (idempotent):
///
/// 1. **Disable mimalloc purging** so freed large blocks are *retained* rather than returned
///    to the OS and re-faulted on the next allocation — what made the old bump arena fast
///    (page reuse); mimalloc-with-retention matches and beats it.
///
/// 2. **Disable Transparent Huge Pages for this process.** On Zen4 (and likely other x86 with
///    physically-indexed L2/L3), when the kernel promotes the allocator's large arenas to
///    2 MB huge pages, the prover's strided multilinear/NTT array access collapses into a few
///    cache sets — measured **+217% cache-misses, IPC 0.85 → 0.51, +50% wall time** on
///    `fancy-aggregation`. It's intermittent (only fires when 2 MB-contiguous memory is free
///    for THP promotion), which is what made it so hard to pin down. `prctl(PR_SET_THP_DISABLE)`
///    is process-local and overrides even a system-wide `THP=always`. No-op off Linux (macOS
///    has no THP — Apple silicon was never affected). Applies under any allocator.
pub fn tune_allocator() {
    // mimalloc v3 option index `mi_option_purge_delay` = 15; value -1 = never purge
    // (equivalent to `MIMALLOC_PURGE_DELAY=-1`). No-op under the `standard-alloc` (plain
    // system allocator) build.
    #[cfg(not(feature = "standard-alloc"))]
    unsafe {
        libmimalloc_sys::mi_option_set(15, -1);
    }
    // Keep allocator arenas on 4 KB pages (see point 2 above).
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
