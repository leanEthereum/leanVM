//! The benchmarks on the stable prover.

crate::prover!(
    stable_rec_aggregation,
    stable_leanvm_core,
    stable_parallel,
    stable_lean_da,
    stable_keccak_gkr,
    stable_primitives
);

#[path = "benchmark.rs"]
pub mod benchmark;
#[path = "fibonacci.rs"]
pub mod fibonacci;
