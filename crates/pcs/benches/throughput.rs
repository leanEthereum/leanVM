//! Dedicated PCS throughput benchmark.
//!
//! Commits and opens a random witness of `2^PCS_LOG_N` GF(2^64) elements at
//! inverse-rate `1/2^PCS_LOG_INV_RATE`, times each phase, and reports GiB/s
//! over the committed data, using exactly 16 pool threads including the dispatcher.
//!
//! The opening is the stacked one a proof runs: one ring-switched claim over the whole witness and one point claim.
//!
//! The passes follow the environment's plan (`BENCH_REPEAT`, `BENCH_COOLDOWN`).
//!
//! It then times the commitment's additive NTT alone (the RS encode, without
//! the transpose and the Merkle tree), as passes of its own.
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
//!
//! With `-- --json` it prints, in place of the report, Bencher Metric Format JSON for CI:
//! `pcs-commit-<PCS_LOG_N>-16thread` and `pcs-open-<PCS_LOG_N>-16thread` (measure `latency`), and
//! `ntt-forward-<PCS_LOG_N>-16thread` (measure `per-op`, one encode), each with the actual `threads` count.
//!
//! ```text
//! cargo bench -p pcs --bench throughput -- --json
//! ```

use bench::{Metric, Plan, Timing, bencher_json, env_usize};
use fiat_shamir::transcript::ProverState;
use pcs::ntt::AdditiveNttF64;
use pcs::ring_switch::{RingSwitch, SliceClaim};
use pcs::stack::{CommittedStack, StackClaim, Statement};
use pcs::whir::{LOG_INV_RATE_0, config_for_rate, inner_product_base_ext};
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;
use primitives::pretty_integer;
use primitives::test_util::Rng;
use std::hint::black_box;
use std::num::NonZeroUsize;
use std::time::Instant;

#[global_allocator]
static ALLOCATOR: bench::Counting<bench::Jemalloc> = bench::Counting(bench::Jemalloc);

fn main() {
    parallel::init_with_threads(NonZeroUsize::new(16).unwrap()).expect("initialize exact 16-thread benchmark pool");
    bench::init_tracing_from_env();

    let log_n = env_usize("PCS_LOG_N", 22);
    let log_inv_rate = env_usize("PCS_LOG_INV_RATE", LOG_INV_RATE_0);
    let pc =
        config_for_rate(log_n, log_inv_rate).unwrap_or_else(|e| panic!("no WHIR config for PCS_LOG_N={log_n}: {e}"));
    let plan = Plan::from_env();
    let trace_span = tracing::info_span!("PCS throughput", log_n, log_inv_rate).entered();

    // Random F64 witness (the committed polynomial), a point claim on it, and a ring-switched claim on its bits.
    let mut rng = Rng::new(0x0192_0000 ^ log_n as u64);
    let n = 1usize << log_n;
    let witness: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();
    let point = rng.ext_vec(log_n);
    let value = inner_product_base_ext(&witness, &eq_table(&point));
    let point_claims = [StackClaim::Point {
        offset: 0,
        low_point: point,
        value,
    }];
    let suffix_point = rng.ext_vec(log_n);
    let rings = [RingSwitch {
        offset: 0,
        qflock_vars: log_n,
        claims: vec![SliceClaim {
            s_hat_v: bit_slices(&witness, &suffix_point),
            suffix_point,
        }],
    }];

    let (mut commit_t, mut open_t) = (Timing::default(), Timing::default());
    plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);

        let t = Instant::now();
        let committed = tracing::info_span!("Commit").in_scope(|| CommittedStack::new(&witness, log_n, pc.clone()));
        commit_t.push(t.elapsed().as_secs_f64());

        let mut ch = ProverState::from_label(b"pcs-throughput");
        let t = Instant::now();
        tracing::info_span!("PCS open").in_scope(|| {
            let statement = Statement {
                points: &point_claims,
                rings: &rings,
            };
            committed.open(&mut ch, &witness, statement);
        });
        open_t.push(t.elapsed().as_secs_f64());
        black_box((committed.root(), ch.into_proof()));
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

    // The commit's encode alone.
    // Its buffer holds `2^initial_k` interleaved lanes, the message in the first replica.
    const ENCODES: usize = 4;
    let log_lanes = pc.initial_k();
    let ntt = AdditiveNttF64::standard(log_n - log_lanes + log_inv_rate);
    let mut codeword = vec![F64::ZERO; n << log_inv_rate];
    codeword[..n].copy_from_slice(&witness);
    let (_, ntt_t) = plan.warm_then_measure(|_| {
        for _ in 0..ENCODES {
            ntt.encode_interleaved_in_place(black_box(&mut codeword), 1 << log_lanes, log_inv_rate);
        }
    });

    if std::env::args().any(|arg| arg == "--json") {
        let report = [
            (
                format!("pcs-commit-{log_n}-16thread"),
                vec![
                    ("latency", Metric::nanoseconds(&commit_t)),
                    ("threads", Metric::exact(parallel::num_threads())),
                ],
            ),
            (
                format!("pcs-open-{log_n}-16thread"),
                vec![
                    ("latency", Metric::nanoseconds(&open_t)),
                    ("threads", Metric::exact(parallel::num_threads())),
                ],
            ),
            (
                format!("ntt-forward-{log_n}-16thread"),
                vec![
                    ("per-op", Metric::nanoseconds_per_op(&ntt_t, ENCODES)),
                    ("threads", Metric::exact(parallel::num_threads())),
                ],
            ),
        ];
        println!("{}", bencher_json(&report));
        return;
    }

    println!(
        "\nPCS throughput: 2^{log_n} variables, rate 1/2^{log_inv_rate}, {} threads, mean of {}",
        parallel::num_threads(),
        pretty_integer(&plan.repeat)
    );
    println!(
        "  committed data                  : {:>8.1} MiB  ({:>13} F64)",
        mib(data_bytes),
        pretty_integer(&n)
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
    println!(
        "  NTT (the commit's encode alone) : {:>8.1} ms{}",
        ntt_t.mean() * 1e3 / ENCODES as f64,
        ntt_t.spread()
    );
    println!("  ------------------------------------------------------------");
    println!(
        "  commit + open                   : {:>8.1} ms   ({:>6.2} GiB/s)",
        (commit_s + open_s) * 1e3,
        gibps(commit_s + open_s),
    );
}

/// The 64 bit-slice values of the witness at `point`: slice `i` is `sum_y bit_i(witness[y]) · eq(point, y)`.
fn bit_slices(witness: &[F64], point: &[F192]) -> Vec<F192> {
    let eq = eq_table(point);
    parallel::fold_reduce(
        witness.len(),
        || vec![F192::ZERO; F64::DEGREE],
        |slices, y| {
            let mut bits = witness[y].0;
            while bits != 0 {
                slices[bits.trailing_zeros() as usize] += eq[y];
                bits &= bits - 1;
            }
        },
        |mut acc, part| {
            for (a, p) in acc.iter_mut().zip(part) {
                *a += p;
            }
            acc
        },
    )
}
