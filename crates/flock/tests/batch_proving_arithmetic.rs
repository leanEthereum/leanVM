//! Standalone batch u64 arithmetic proving, isolated from the VM: wrapping
//! addition, and multiplication wrapping (a `u64` result) or widening (a `u128`).
//!
//! ```text
//! BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=20 cargo test --release --package flock --test batch_proving_arithmetic -- mul_wrapping_prove_verify --exact --nocapture --include-ignored
//! ```

use std::sync::Mutex;
use std::time::Instant;

use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use flock::arith::{U64Circuit, U64Op};
use flock::reduction::{min_n_blocks_log, ring_switch_open, ring_switch_verify};
use pcs::pack::LOG_PACKING;
use pcs::stack_open::{open_batch_mixed_whir_stacked, verify_opening_batch_mixed_whir_stacked};
use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0};
use pcs::whir::{commit, config_for_rate};
use primitives::bench::{Plan, Timing};
use primitives::{field::F64, pretty_integer, test_rng::Rng};

/// Arena phases are process-global, so the benchmarks must not overlap.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

#[test]
#[ignore = "manual release benchmark; needs substantial memory"]
fn add_wrapping_prove_verify() {
    bench(U64Op::WrappingAdd);
}

#[test]
#[ignore = "manual release benchmark; needs substantial memory"]
fn mul_wrapping_prove_verify() {
    bench(U64Op::WrappingMul);
}

#[test]
#[ignore = "manual release benchmark; needs substantial memory"]
fn mul_widening_prove_verify() {
    bench(U64Op::WideningMul);
}

fn bench(op: U64Op) {
    let _serial = ONE_AT_A_TIME.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
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
    let mu = circuit.k_log() + n_log - LOG_PACKING;
    assert!(
        mu >= 15,
        "FLOCK_N_LOG too small: need a committed witness with mu >= 15"
    );

    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let pairs: Vec<(u64, u64)> = (0..n).map(|_| (rng.next_u64(), rng.next_u64())).collect();
    let config = config_for_rate(mu, LOG_INV_RATE_0).expect("WHIR configuration");
    let label = format!("flock-{op:?}-batch").into_bytes();

    // One full prove pass from the raw pairs, one arena phase, as in
    // `batch_proving_hashes`.
    zk_alloc::enable_arena();
    let prove_pass = || {
        let _phase = zk_alloc::enter_phase();
        let t_pass = Instant::now();
        let t = Instant::now();
        let (z_packed, a_packed, b_packed, z_lincheck) = circuit.generate_witness(&pairs, n_log);
        // SAFETY: `F64` is `repr(transparent)` over `u64`.
        let q_flock: &[F64] = unsafe { std::slice::from_raw_parts(z_packed.as_ptr().cast(), z_packed.len()) };
        let witness_s = t.elapsed().as_secs_f64();
        assert_eq!(q_flock.len(), 1 << mu);

        let mut ps = ProverState::from_label(&label);

        let t = Instant::now();
        let (commitment, prover_data) = commit(q_flock, mu, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
        ps.add_root(&commitment.root);
        let commit_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let stage = block.prove_zerocheck(n_log, &z_packed, &a_packed, &b_packed, &mut ps);
        let zerocheck_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let reduced = block.prove_lincheck(n_log, stage, &z_lincheck, &mut ps);
        let lincheck_s = t.elapsed().as_secs_f64();
        drop((a_packed, b_packed, z_lincheck));

        let t = Instant::now();
        let ring = ring_switch_open(mu, 0, &reduced);
        open_batch_mixed_whir_stacked(
            &mut ps,
            mu,
            q_flock,
            &prover_data,
            &config,
            &[],
            std::slice::from_ref(&ring),
        );
        let open_s = t.elapsed().as_secs_f64();

        let proof = ps.into_proof();
        let pass_s = t_pass.elapsed().as_secs_f64();
        (proof, [witness_s, commit_s, zerocheck_s, lincheck_s, open_s, pass_s])
    };

    let plan = Plan::from_env();
    let mut stages: [Timing; 6] = std::array::from_fn(|_| Timing::default());
    let (transcript, _) = plan.warm_then_measure(|_final_pass| {
        let (out, secs) = prove_pass();
        for (timing, s) in stages.iter_mut().zip(secs) {
            timing.push(s);
        }
        out
    });
    // The warmup pass also pushed a sample; drop the leading one per stage.
    let [witness, commit_stage, zerocheck, lincheck, open, pass] = stages.map(|t| {
        let mut kept = Timing::default();
        for &s in &t.samples()[1..] {
            kept.push(s);
        }
        kept
    });

    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_final_pass| {
        let mut vs = VerifierState::from_label(&label, &transcript);
        let root = vs.next_root().expect("commitment root");
        let replay = block.verify(n_log, &mut vs).expect("Flock reduction verifies");
        let ring = ring_switch_verify(mu, 0, &replay.claim);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &config,
                mu,
                1 << INITIAL_FOLDING_FACTOR,
                &root,
                &[],
                std::slice::from_ref(&ring)
            )
            .is_ok(),
            "stacked PCS opening verifies"
        );
        vs.finish().expect("transcript fully consumed");
    });

    let pass_s = pass.mean();
    let share = |s: f64| format!("{:>5.1}%", 100.0 * s / pass_s);
    let ms = |t: &Timing| format!("{:>8.1} ms{:<9}{}", t.mean() * 1e3, t.spread(), share(t.mean()));
    let named = witness.mean() + commit_stage.mean() + zerocheck.mean() + lincheck.mean() + open.mean();
    println!(
        "\nFlock {title} batch proving, {} {unit} (2^{n_log} slots)",
        pretty_integer(n)
    );
    println!(
        "  block                           : 2^{} bits, {} constrained",
        circuit.k_log(),
        pretty_integer(circuit.useful_bits())
    );
    println!("  setup (circuit, excluded)       : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {}", ms(&witness));
    println!("  commit                          : {}", ms(&commit_stage));
    println!("  zerocheck                       : {}", ms(&zerocheck));
    println!("  lincheck                        : {}", ms(&lincheck));
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
    println!(
        "  verify                          : {:>8.1} ms",
        verify_time.mean() * 1e3
    );
    println!(
        "  throughput                      : {:>14} {unit}/s{}",
        pretty_integer((n as f64 / pass_s).round() as u64),
        pass.spread()
    );
}
