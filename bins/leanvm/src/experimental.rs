//! The benchmarks on the experimental prover.

crate::prover!(
    experimental_rec_aggregation,
    experimental_leanvm_core,
    experimental_parallel,
    experimental_lean_compiler,
    experimental_lean_da,
    experimental_keccak_gkr,
    experimental_lean_xmss,
    experimental_lean_sphincs,
    experimental_primitives
);

#[path = "benchmark.rs"]
pub mod benchmark;
#[path = "fibonacci.rs"]
pub mod fibonacci;
