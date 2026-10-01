//! Dedicated PCS throughput benchmark.
//!
//! Commits and opens a random witness of `2^PCS_LOG_N` GF(2^64) elements at
//! inverse-rate `1/2^PCS_LOG_INV_RATE`, times each phase, and reports GiB/s
//! over the committed data. Each pass is one arena phase, as a proof is; the
//! passes follow [`bench::Plan::from_env`] (`BENCH_REPEAT`, `BENCH_COOLDOWN`).
//!
//! ```text
//! PCS_LOG_N          number of variables = log2(witness length)   [default 22]
//! PCS_LOG_INV_RATE   log2 of the inverse RS rate (rate = 1/2^r)    [default: profile]
//! BENCH_TRACING      print the final pass's trace tree (`RUST_LOG` adjusts it)
//!
//! PCS_LOG_N=24 PCS_LOG_INV_RATE=1 BENCH_REPEAT=5 cargo bench -p pcs --bench throughput
//! ```
//!
//! Large `PCS_LOG_N` needs substantial memory: the RS codeword is `2^log_inv_rate`×
//! the witness, and the open copies the basis table each pass.

use std::hint::black_box;
use std::time::Instant;

use bench::{Plan, Timing, env_usize};
use pcs::whir::{LOG_INV_RATE_0, commit, config_for_rate, inner_product_base_ext, recursive_prover_with_basis};
use primitives::{
    field::{F64, F192},
    multilinear::eq_table,
    pretty_integer,
    test_rng::Rng,
};

fn main() {
    bench::init_tracing_from_env();

    let log_n = env_usize("PCS_LOG_N", 22);
    let log_inv_rate = env_usize("PCS_LOG_INV_RATE", LOG_INV_RATE_0);
    let pc = config_for_rate(log_n, log_inv_rate).expect("WHIR config feasible (try a larger PCS_LOG_N, e.g. >= 16)");
    let plan = Plan::from_env();
    let trace_span = tracing::info_span!("PCS throughput", log_n, log_inv_rate).entered();

    // Random F64 witness (the committed polynomial) and a random E evaluation point.
    let mut rng = Rng::new(0x0192_0000 ^ log_n as u64);
    let n = 1usize << log_n;
    let witness: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();
    let point: Vec<F192> = rng.ext_vec(log_n);
    let b_initial = eq_table(&point);
    let target = inner_product_base_ext(&witness, &b_initial);

    // Nothing a pass allocates outlives it: the commitment and the proof are
    // consumed inside, so every buffer dies with the pass's phase.
    zk_alloc::enable_arena();
    let (mut commit_t, mut open_t) = (Timing::default(), Timing::default());
    plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        let _phase = zk_alloc::enter_phase();

        let t = Instant::now();
        let (cm, pd) = tracing::info_span!("Commit").in_scope(|| commit(&witness, log_n, pc.initial_k(), log_inv_rate));
        commit_t.push(t.elapsed().as_secs_f64());

        let mut ch = fiat_shamir::transcript::ProverState::from_label(b"pcs-throughput");
        let t = Instant::now();
        tracing::info_span!("PCS open").in_scope(|| {
            recursive_prover_with_basis(
                &pc,
                log_n,
                &witness,
                zk_alloc::ArenaVec::from_slice(&b_initial),
                target,
                &pd.codeword,
                &pd.merkle_tree,
                &mut ch,
            );
        });
        open_t.push(t.elapsed().as_secs_f64());
        black_box((cm, ch.into_proof()));
    });
    // The warmup pass also pushed a sample; drop it.
    let [commit_t, open_t] = [commit_t, open_t].map(|t| {
        let mut kept = Timing::default();
        for &s in &t.samples()[1..] {
            kept.push(s);
        }
        kept
    });
    let (commit_s, open_s) = (commit_t.mean(), open_t.mean());

    // Throughput is over the committed data: 2^log_n F64 = 2^log_n * 8 bytes.
    let data_bytes = (n as f64) * 8.0;
    let mib = |bytes: f64| bytes / (1u64 << 20) as f64;
    let gibps = |secs: f64| (data_bytes / (1u64 << 30) as f64) / secs;
    let codeword_bytes = data_bytes * (1u64 << log_inv_rate) as f64;

    // tracing-forest renders the tree when its root span closes. Close it
    // before printing the throughput report so the complete trace appears first.
    drop(trace_span);

    println!(
        "\nPCS throughput: 2^{log_n} variables, rate 1/2^{log_inv_rate}, mean of {}",
        pretty_integer(plan.repeat)
    );
    println!(
        "  committed data                  : {:>8.1} MiB  ({:>13} F64)",
        mib(data_bytes),
        pretty_integer(n)
    );
    println!("  RS codeword (encoded)           : {:>8.1} MiB", mib(codeword_bytes));
    println!("  ------------------------------------------------------------");
    println!(
        "  commit                          : {:>8.1} ms   ({:>6.2} GiB/s){}",
        commit_s * 1e3,
        gibps(commit_s),
        commit_t.spread()
    );
    println!(
        "  open                            : {:>8.1} ms   ({:>6.2} GiB/s){}",
        open_s * 1e3,
        gibps(open_s),
        open_t.spread()
    );
    println!("  ------------------------------------------------------------");
    println!(
        "  commit + open                   : {:>8.1} ms   ({:>6.2} GiB/s)",
        (commit_s + open_s) * 1e3,
        gibps(commit_s + open_s),
    );
}
