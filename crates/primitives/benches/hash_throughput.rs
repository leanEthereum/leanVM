//! Batched Keccak-256 throughput across the thread pool, to 32-byte digests: 64-byte inputs (a
//! Merkle node's two children) and 512-byte ones (a PCS leaf of 64 words, four permutations).
//! The passes follow [`bench::Plan::from_env`] (`BENCH_REPEAT`, `BENCH_COOLDOWN`).
//!
//! ```text
//! BENCH_REPEAT=5 cargo bench -p primitives --bench hash_throughput
//! ```

fn run<const LEN: usize>() {
    const BYTES: usize = 64 << 10; // input bytes per call, cache-resident
    const ITERS: usize = 1 << 5; // rehash rounds per task per dispatch
    const TASKS: usize = 1 << 10;
    let k = BYTES / LEN;

    let data: Vec<u8> = (0..TASKS * BYTES).map(|i| (i & 0xff) as u8).collect();
    let mut out = vec![0u8; TASKS * k * 32];
    let (_, time) = bench::Plan::from_env().warm_then_measure(|_| {
        parallel::chunks_mut(&mut out, k * 32, |i, sub| {
            let d = &data[i * BYTES..][..BYTES];
            for _ in 0..ITERS {
                primitives::hash::hash_many(d, LEN, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    println!(
        "{LEN}B -> 32B, {} threads, LANES={}: {:.2} Mhash/s{}",
        parallel::num_threads(),
        primitives::hash::LANES,
        (TASKS * k * ITERS) as f64 / time.mean() / 1e6,
        time.spread(),
    );
}

fn main() {
    run::<64>();
    run::<512>();
}
