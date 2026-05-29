use backend::*;

pub use backend::ProofError;
pub use rec_aggregation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, TypeOneInfo, TypeOneMultiSignature,
    TypeTwoMultiSignature, aggregate_type_1, merge_many_type_1, split_type_2, verify_type_1, verify_type_2,
};
pub use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSecretKey, XmssSignature, xmss_key_gen, xmss_sign, xmss_verify};

pub type F = KoalaBear;

/// Tune the default (mimalloc) allocator for the prover's churn of huge short-lived buffers.
///
/// Disables purging so freed large blocks are **retained** rather than returned to the OS
/// and re-faulted on the next allocation. This is what made the old bump arena fast (it
/// reused the same pages); mimalloc-with-retention matches *and beats* it here, without the
/// arena's fragility. Idempotent; call before any heavy proving allocation.
pub fn tune_allocator() {
    // mimalloc v3 option index `mi_option_purge_delay` = 15; value -1 = never purge
    // (equivalent to `MIMALLOC_PURGE_DELAY=-1`). No-op under the `standard-alloc` (plain
    // system allocator) build.
    #[cfg(not(feature = "standard-alloc"))]
    unsafe {
        libmimalloc_sys::mi_option_set(15, -1);
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
