//! Standalone batch Keccak proving with the GKR protocol, isolated from the VM.
//!
//! ```text
//! BENCH_REPEAT=3 BENCH_COOLDOWN=2 KECCAK_N_LOG=18 cargo bench -p keccak_gkr --bench hash_batch
//! ```
//!
//! With `-- --json` it prints, in place of the report, the proving time as Bencher Metric
//! Format, which is what CI compares.
//!
//! `KECCAK_DEPTH` sets the rounds between two committed states (a divisor of 24).
//! `BENCH_TRACING=1` prints the final pass's span tree (`RUST_LOG` adjusts it).

use std::time::Instant;

use bench::{Metric, Plan, Timing, bencher_json, env_usize};
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use keccak_gkr::{Shape, Witness};
use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, commit, config_for_rate};
use primitives::{field::F64, pretty_integer, test_rng::Rng};

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

const LABEL: &[u8] = b"keccak-gkr-batch";

fn main() {
    bench::init_tracing_from_env();
    let n = 1usize << env_usize("KECCAK_N_LOG", 13);
    let shape = Shape::new(n, env_usize("KECCAK_DEPTH", 6));
    let mu = shape.stack_log();

    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let inputs: Vec<[u64; 25]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let config = config_for_rate(mu, LOG_INV_RATE_0).expect("WHIR configuration");

    let prove_pass = || {
        let _span = tracing::info_span!("Keccak GKR prove", n).entered();
        let t_pass = Instant::now();
        let t = Instant::now();
        // SAFETY: the witness generator writes every word.
        let mut committed = unsafe { primitives::uninit_vec::<F64>(keccak_gkr::committed_len(shape)) };
        let witness = tracing::info_span!("Witness").in_scope(|| Witness::generate(shape, &inputs, &mut committed));
        let witness_s = t.elapsed().as_secs_f64();

        let mut ps = ProverState::from_label(LABEL);
        let t = Instant::now();
        let (commitment, prover_data) = commit(&committed, mu, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
        ps.add_root(&commitment.root);
        let commit_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let openings = keccak_gkr::prove(&mut ps, &witness, &committed);
        let gkr_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        keccak_gkr::open_commitment(&mut ps, shape, &committed, &prover_data, &config, openings);
        let open_s = t.elapsed().as_secs_f64();

        let proof = ps.into_proof();
        let pass_s = t_pass.elapsed().as_secs_f64();
        (proof, [witness_s, commit_s, gkr_s, open_s, pass_s])
    };

    let plan = Plan::from_env();
    let mut stages: [Timing; 5] = std::array::from_fn(|_| Timing::default());
    let (transcript, _) = plan.warm_then_measure(|final_pass| {
        let _quiet = (!final_pass).then(bench::suppress_tracing);
        let (out, secs) = prove_pass();
        for (timing, s) in stages.iter_mut().zip(secs) {
            timing.push(s);
        }
        out
    });
    // The warmup pass also pushed a sample; drop the leading one per stage.
    let [witness, commit_stage, gkr, open, pass] = stages.map(|t| {
        let mut kept = Timing::default();
        for &s in &t.samples()[1..] {
            kept.push(s);
        }
        kept
    });

    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_final_pass| {
        let mut vs = VerifierState::from_label(LABEL, &transcript);
        let root = vs.next_root().expect("commitment root");
        let openings = keccak_gkr::verify(&mut vs, shape).expect("the reduction verifies");
        keccak_gkr::verify_commitment(&mut vs, shape, &config, &root, &openings).expect("the opening verifies");
        vs.finish().expect("transcript fully consumed");
    });

    let merkle_bytes: usize = transcript
        .merkle
        .iter()
        .map(|m| 8 * m.leaf_data.iter().map(Vec::len).sum::<usize>() + 32 * m.sibling_hashes.len())
        .sum();
    let proof_bytes = 24 * transcript.stream.len() + merkle_bytes;

    if std::env::args().any(|arg| arg == "--json") {
        let report = [(
            format!("keccak-hash-batch-{n}"),
            vec![("latency", Metric::nanoseconds(&pass))],
        )];
        println!("{}", bencher_json(&report));
        return;
    }

    let pass_s = pass.mean();
    let line = |name: &str, t: &Timing| {
        println!(
            "  {name:<32}: {:>8.1} ms{} {:>6.1}%",
            t.mean() * 1e3,
            t.spread(),
            100.0 * t.mean() / pass_s
        );
    };
    println!(
        "\nKeccak GKR batch proving, {} permutations, a state committed every {} rounds",
        pretty_integer(n),
        shape.depth
    );
    line("witness", &witness);
    line("commit", &commit_stage);
    line("layers and openings", &gkr);
    line("pcs opening", &open);
    println!("  ------------------------------------------");
    println!(
        "  {:<32}: {:>8.1} ms{}",
        "prove TOTAL (witness included)",
        pass_s * 1e3,
        pass.spread()
    );
    println!("  {:<32}: {:>8.1} ms", "verify", verify_time.mean() * 1e3);
    println!(
        "  {:<32}: {:>14} permutations/s{}",
        "throughput",
        pretty_integer((n as f64 / pass_s).round() as u64),
        pass.spread()
    );
    println!(
        "  {:<32}: {:>11.1} KiB  ({} scalars, {:.1} KiB of Merkle openings)",
        "proof size",
        proof_bytes as f64 / 1024.0,
        transcript.stream.len(),
        merkle_bytes as f64 / 1024.0
    );
}
