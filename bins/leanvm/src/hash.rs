//! Keccak-f proved in a batch by the GKR the VM runs on its `KECCAK` steps, alone, as the
//! `hash_batch` bench of `keccak_gkr` does.

use bench::Plan;

/// Prove and verify `2^log_n` permutations, a state committed every [`leanvm_core::keccak::DEPTH`]
/// rounds, and print the report.
pub fn run_hash(log_n: usize, log_inv_rate: usize, plan: Plan) {
    keccak_gkr::batch_bench::run(1 << log_n, leanvm_core::keccak::DEPTH, log_inv_rate, plan).print();
}
