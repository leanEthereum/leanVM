//! Batched BLAKE2s throughput across the thread pool, 64-byte blocks to 32-byte digests.
//! The passes follow [`bench::Plan::from_env`] (`BENCH_REPEAT`, `BENCH_COOLDOWN`).
//!
//! ```text
//! BENCH_REPEAT=5 cargo bench -p primitives --bench hash_throughput
//! ```
//!
//! With `-- --json` it prints, in place of the report, the time per hashed block across the pool
//! (benchmark `blake2s-batch`, measure `per-op`) as Bencher Metric Format JSON, for CI.
//!
//! ```text
//! cargo bench -p primitives --bench hash_throughput -- --json
//! ```

use bench::{Metric, Plan, bencher_json};

fn main() {
    const K: usize = 1 << 10; // hashes per call: 96 KiB in+out per task, cache-resident
    const ITERS: usize = 1 << 5; // rehash rounds per task per dispatch
    const TASKS: usize = 1 << 10;
    const HASHES: usize = TASKS * K * ITERS;

    let data: Vec<u8> = (0..TASKS * K * 64).map(|i| (i & 0xff) as u8).collect();
    let mut out = vec![0u8; TASKS * K * 32];
    let (_, time) = Plan::from_env().warm_then_measure(|_| {
        parallel::chunks_mut(&mut out, K * 32, |i, sub| {
            let d = &data[i * K * 64..i * K * 64 + sub.len() * 2];
            for _ in 0..ITERS {
                primitives::hash::hash_many::<64>(d, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    if std::env::args().any(|arg| arg == "--json") {
        let report = [(
            "blake2s-batch".to_string(),
            vec![("per-op", Metric::nanoseconds_per_op(&time, HASHES))],
        )];
        println!("{}", bencher_json(&report));
        return;
    }
    println!(
        "64B -> 32B, {} threads, LANES={}: {:.0} Mhash/s{}",
        parallel::num_threads(),
        primitives::hash::LANES,
        HASHES as f64 / time.mean() / 1e6,
        time.spread(),
    );
}
