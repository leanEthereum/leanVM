//! Standalone batch Keccak proving with the GKR protocol, isolated from the VM.
//!
//! ```text
//! BENCH_REPEAT=3 BENCH_COOLDOWN=2 KECCAK_N_LOG=18 cargo bench -p keccak_gkr --bench hash_batch
//! ```
//!
//! With `-- --json` it prints, in place of the report, the proving time as Bencher Metric
//! Format, which is what CI compares. `cargo leanvm hash` runs the same benchmark.
//!
//! `KECCAK_DEPTH` sets the rounds between two committed states (a divisor of 24).
//! `BENCH_TRACING=1` prints the final pass's span tree (`RUST_LOG` adjusts it).

use bench::{Plan, env_usize};
use pcs::whir::LOG_INV_RATE_0;

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

fn main() {
    bench::init_tracing_from_env();
    let n = 1usize << env_usize("KECCAK_N_LOG", 13);
    let report = keccak_gkr::batch_bench::run(n, env_usize("KECCAK_DEPTH", 12), LOG_INV_RATE_0, Plan::from_env());
    if std::env::args().any(|arg| arg == "--json") {
        println!("{}", report.json());
    } else {
        report.print();
    }
}
