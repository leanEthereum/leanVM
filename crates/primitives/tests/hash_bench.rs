use std::time::Instant;

/// Timed passes per measurement, of which the median is kept.
///
/// The host is not necessarily idle, so a single pass is not a measurement.
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

/// Seconds per call of `f`: the median of back-to-back 20 ms windows.
///
/// A 50 ms warm-up lets the core reach its steady clock.
///
/// Nothing sleeps between passes, or a short kernel is timed while the clock ramps back up.
fn time_hot(mut f: impl FnMut()) -> f64 {
    // Mean seconds per call over one window of `secs`.
    let window = |secs: f64, f: &mut dyn FnMut()| {
        let (t, mut calls) = (Instant::now(), 0usize);
        while t.elapsed().as_secs_f64() < secs {
            f();
            calls += 1;
        }
        t.elapsed().as_secs_f64() / calls as f64
    };
    // Warm up, then keep the median window.
    window(0.05, &mut f);
    median((0..PASSES).map(|_| window(0.02, &mut f)).collect())
}

/// cargo test --release -p primitives --test hash_bench single_thread_throughput -- --ignored --nocapture
#[test]
#[ignore = "manual throughput measurement"]
fn single_thread_throughput() {
    use primitives::hash;
    use std::hint::black_box;

    // 64 KiB stays in L2: this times the kernels, not DRAM.
    const BYTES: usize = 1 << 16;
    let data: Vec<u8> = (0..BYTES).map(|i| (i * 7 + 3) as u8).collect();
    let report = |name: &str, bytes: usize, s: f64| {
        println!("{name:<30} {:>10.1} ns {:>7.2} GB/s", s * 1e9, bytes as f64 / s / 1e9);
    };

    let m: [u32; 16] = std::array::from_fn(|i| i as u32);
    let mut h = hash::PARAM_IV;
    report(
        "compress",
        64,
        time_hot(|| hash::compress(black_box(&mut h), black_box(&m), 64, true)),
    );
    for len in [64usize, 1024, BYTES] {
        report(
            &format!("hash {len} B"),
            len,
            time_hot(|| {
                black_box(hash::hash(black_box(&data[..len])));
            }),
        );
    }

    let mut out = vec![0u8; BYTES / 64 * 32];
    macro_rules! many {
        ($($len:literal),*) => {$(
            let n = BYTES / $len;
            let s = time_hot(|| hash::hash_many::<$len>(black_box(&data[..n * $len]), black_box(&mut out[..n * 32])));
            report(&format!("hash_many<{}> x{n}", $len), n * $len, s);
        )*};
    }
    many!(64, 128, 192, 512, 1024);
    let state = hash::zero_prefix_state(3);
    let s = time_hot(|| {
        hash::hash_many_dyn_from_state(
            black_box(&data),
            256,
            &state,
            192,
            black_box(&mut out[..BYTES / 256 * 32]),
        )
    });
    report("hash_many_dyn_from_state 256", BYTES, s);
}
