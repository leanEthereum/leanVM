//! Standalone batch u64 arithmetic proving, isolated from the VM.
//!
//! The operations: wrapping addition, and multiplication wrapping (a `u64` result) or widening (a `u128`).
//!
//! ```text
//! BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=20 cargo bench -p flock --features bench --bench arithmetic_batch -- mul_wrapping
//! ```
//!
//! With `--json` it prints, in place of the reports, each operation's proving time as Bencher Metric Format JSON.
//! CI reads it.
//! The time excludes the witness, as in the hash benchmark.
//! Each benchmark is named `flock-<operation>-batch-<n>`, `flock-mul-wrapping-batch-262144` say, measure `latency`.
//!
//! ```text
//! FLOCK_N_LOG=18 cargo bench -p flock --features bench --bench arithmetic_batch -- --json
//! ```

use std::time::Instant;

use bench::{Metric, Plan, Timing, bencher_json};
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use flock::Witness;
use flock::gadgets::{U64Circuit, U64Op};
use flock::reduction::{Instance, min_n_blocks_log};
use pcs::ring_switch::RingSwitch;
use pcs::stack_open;
use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0};
use pcs::whir::{commit, config_for_rate};
use primitives::{field::F64, pretty_integer, test_util::Rng};

#[global_allocator]
static ALLOCATOR: bench::Counting<bench::Jemalloc> = bench::Counting(bench::Jemalloc);

/// Every operation whose name contains one of the arguments, or all of them with none.
///
/// The flags `cargo bench` passes of its own, `--bench` say, are skipped.
fn main() {
    bench::init_tracing_from_env();
    let json = std::env::args().any(|arg| arg == "--json");
    let filters: Vec<String> = std::env::args().skip(1).filter(|a| !a.starts_with('-')).collect();
    let mut report = Vec::new();
    for (name, op) in [
        ("add_wrapping", U64Op::WrappingAdd),
        ("mul_wrapping", U64Op::WrappingMul),
        ("mul_widening", U64Op::WideningMul),
    ] {
        if filters.is_empty() || filters.iter().any(|f| name.contains(f.as_str())) {
            let (n, prove) = bench(op, json);
            let name = name.replace('_', "-");
            report.push((
                format!("flock-{name}-batch-{n}"),
                vec![("latency", Metric::nanoseconds(&prove))],
            ));
        }
    }
    if json {
        println!("{}", bencher_json(&report));
    }
}

/// Prove `op`'s batch, printing its report unless `quiet`.
///
/// Returns the batch size and the proving time, witness excluded.
fn bench(op: U64Op, quiet: bool) -> (usize, Timing) {
    let (title, unit) = match op {
        U64Op::WrappingAdd => ("Wrapping u64 addition", "sums"),
        U64Op::WrappingMul => ("Wrapping u64 multiplication", "products"),
        U64Op::WideningMul => ("Widening u64 multiplication", "products"),
    };
    let requested_n_log: usize = std::env::var("FLOCK_N_LOG")
        .ok()
        .map(|s| s.parse().expect("FLOCK_N_LOG must be an integer"))
        .unwrap_or(16);
    let n = 1usize
        .checked_shl(requested_n_log as u32)
        .expect("FLOCK_N_LOG exceeds the platform usize width");
    let n_log = min_n_blocks_log(n);

    let t = Instant::now();
    let circuit = U64Circuit::new(op);
    let setup_ms = t.elapsed().as_secs_f64() * 1e3;
    let block = circuit.block();
    let mu = circuit.k_log() + n_log - 64usize.ilog2() as usize;
    assert!(
        mu >= 15,
        "FLOCK_N_LOG too small: need a committed witness with mu >= 15"
    );

    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let pairs: Vec<(u64, u64)> = (0..n).map(|_| (rng.next_u64(), rng.next_u64())).collect();
    let config = config_for_rate(mu, LOG_INV_RATE_0).expect("WHIR configuration");
    let label = format!("flock-{op:?}-batch").into_bytes();

    // One full prove pass from the raw pairs, as in `hash_batch`.
    let prove_pass = || {
        let _span = tracing::info_span!("Flock prove", n_log).entered();
        let t_pass = Instant::now();
        let t = Instant::now();
        let witness = circuit.witness(&pairs, n_log);
        // SAFETY: `F64` is `repr(transparent)` over `u64`.
        let q_flock = |z: &[u64]| -> &[F64] { unsafe { std::slice::from_raw_parts(z.as_ptr().cast(), z.len()) } };
        let witness_s = t.elapsed().as_secs_f64();
        assert_eq!(witness.z.len(), 1 << mu);

        let mut ps = ProverState::from_label(&label);
        let t_prove = Instant::now();

        let t = Instant::now();
        let (commitment, prover_data) = commit(q_flock(&witness.z), mu, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
        ps.add_root(&commitment.root);
        let commit_s = t.elapsed().as_secs_f64();

        let instance = [Instance::of(block, n_log, &witness)];
        let t = Instant::now();
        let reduced = flock::reduction::prove(&instance, &mut ps).pop().expect("one circuit");
        let reduction_s = t.elapsed().as_secs_f64();
        let Witness { z, .. } = witness;

        let t = Instant::now();
        let ring = RingSwitch {
            offset: 0,
            qflock_vars: mu,
            claims: vec![reduced],
        };
        stack_open::open(
            &mut ps,
            mu,
            q_flock(&z),
            &prover_data,
            &config,
            &[],
            std::slice::from_ref(&ring),
        );
        let open_s = t.elapsed().as_secs_f64();
        let prove_s = t_prove.elapsed().as_secs_f64();

        let proof = ps.into_proof();
        let pass_s = t_pass.elapsed().as_secs_f64();
        (proof, [witness_s, commit_s, reduction_s, open_s, prove_s, pass_s])
    };

    let plan = Plan::from_env();
    let mut stages: [Timing; 6] = std::array::from_fn(|_| Timing::default());
    let (transcript, _) = plan.warm_then_measure(|final_pass| {
        let _quiet = (!final_pass).then(bench::suppress_tracing);
        let (out, secs) = prove_pass();
        for (timing, s) in stages.iter_mut().zip(secs) {
            timing.push(s);
        }
        out
    });
    // The warmup pass also pushed a sample; drop the leading one per stage.
    let [witness, commit_stage, reduction, open, prove, pass] = stages.map(|t| {
        let mut kept = Timing::default();
        for &s in &t.samples()[1..] {
            kept.push(s);
        }
        kept
    });

    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_final_pass| {
        let mut vs = VerifierState::from_label(&label, &transcript);
        let root = vs.next_root().expect("commitment root");
        let replay = flock::reduction::verify(&[(block.shape(), n_log)], &mut vs)
            .expect("Flock reduction verifies")
            .remove(0);
        replay.matrices.check(block.circuit).expect("the matrices settle");
        let ring = RingSwitch {
            offset: 0,
            qflock_vars: mu,
            claims: vec![replay.claim],
        };
        assert!(
            stack_open::verify(
                &mut vs,
                &config,
                mu,
                1 << INITIAL_FOLDING_FACTOR,
                root,
                &[],
                std::slice::from_ref(&ring)
            )
            .is_ok(),
            "stacked PCS opening verifies"
        );
        vs.finish().expect("transcript fully consumed");
    });
    if quiet {
        return (n, prove);
    }

    let pass_s = pass.mean();
    let share = |s: f64| format!("{:>5.1}%", 100.0 * s / pass_s);
    let ms = |t: &Timing| format!("{:>8.1} ms{:<9}{}", t.mean() * 1e3, t.spread(), share(t.mean()));
    let named = witness.mean() + commit_stage.mean() + reduction.mean() + open.mean();
    println!(
        "\nFlock {title} batch proving, {} {unit} (2^{n_log} slots)",
        pretty_integer(&n)
    );
    println!(
        "  block                           : 2^{} bits, {} constrained",
        circuit.k_log(),
        pretty_integer(&(circuit.useful_bits()))
    );
    println!("  setup (circuit, excluded)       : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {}", ms(&witness));
    println!("  commit                          : {}", ms(&commit_stage));
    println!("  reduction                       : {}", ms(&reduction));
    println!("  pcs opening                     : {}", ms(&open));
    println!(
        "  other                           : {:>8.1} ms{:<9}{}",
        (pass_s - named) * 1e3,
        "",
        share(pass_s - named)
    );
    println!("  ------------------------------------------");
    println!(
        "  prove TOTAL (witness included)  : {:>8.1} ms{}",
        pass_s * 1e3,
        pass.spread()
    );
    println!("  prove (witness excluded)        : {}", ms(&prove));
    println!(
        "  verify                          : {:>8.1} ms",
        verify_time.mean() * 1e3
    );
    println!(
        "  throughput                      : {:>14} {unit}/s{}",
        pretty_integer(&((n as f64 / pass_s).round() as u64)),
        pass.spread()
    );
    (n, prove)
}
