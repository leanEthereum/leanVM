use std::time::Instant;

/// Median of `PASSES` timed passes, with a cooldown between them: the machine
/// this runs on is not necessarily idle, so a single pass is not a measurement.
const PASSES: usize = 5;
const COOLDOWN: std::time::Duration = std::time::Duration::from_millis(300);

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn time(reps: usize, mut f: impl FnMut()) -> f64 {
    f();
    let mut samples = Vec::with_capacity(PASSES);
    for _ in 0..PASSES {
        let t = Instant::now();
        for _ in 0..reps {
            f();
        }
        samples.push(t.elapsed().as_secs_f64() / reps as f64);
        std::thread::sleep(COOLDOWN);
    }
    median(samples)
}

/// cargo test --release -p primitives --test hash_bench multithreaded_throughput -- --ignored --nocapture
#[test]
#[ignore = "manual throughput measurement"]
fn multithreaded_throughput() {
    const K: usize = 1 << 10; // hashes per call: 96 KiB in+out per task, cache-resident
    const ITERS: usize = 1 << 5; // rehash rounds per task per dispatch
    const TASKS: usize = 1 << 10;

    let data: Vec<u8> = (0..TASKS * K * 64).map(|i| (i & 0xff) as u8).collect();
    let mut out = vec![0u8; TASKS * K * 32];
    let s = time(2, || {
        parallel::chunks_mut(&mut out, K * 32, |i, sub| {
            let d = &data[i * K * 64..i * K * 64 + sub.len() * 2];
            for _ in 0..ITERS {
                primitives::hash::hash_many::<64>(d, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    println!(
        "64B -> 32B, {} threads, LANES={}: {:.0} Mhash/s",
        parallel::num_threads(),
        primitives::hash::LANES,
        (TASKS * K * ITERS) as f64 / s / 1e6,
    );
}
