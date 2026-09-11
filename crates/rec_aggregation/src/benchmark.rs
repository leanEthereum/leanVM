//! The two benchmarks: one leaf of the aggregation tree (`aggregate`), and an
//! n→1 recursion step over leaves of that size (`recursion`). Aggregation accepts
//! signature counts and a blob count; recursion accepts these counts per leaf.

use primitives::bench::Plan;
use primitives::{pretty_f64, pretty_integer};
use rand::{Rng, SeedableRng, rngs::StdRng};
use xmss::{XmssPublicKey, XmssSignature};

use crate::aggregation::{DaInput, EthereumProof, aggregate, aggregate_with_stats};
use crate::signers_cache;

fn blobs(n: usize, seed: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..n * lean_da::BLOB_SYMBOLS).map(|_| rng.random()).collect()
}

/// Cached signers `[from, to)`, as the aggregation API takes them: each raw
/// signature carries its epoch and message, the benchmarks using one pair for
/// all.
fn signers(from: usize, to: usize) -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_signers(to)[from..to]
        .iter()
        .map(|(pk, sig)| {
            (
                pk.clone(),
                signers_cache::XMSS_EPOCH_A,
                signers_cache::message(),
                sig.clone(),
            )
        })
        .collect()
}

/// Each SPHINCS signer comes with the message it signed, as the XMSS ones do.
fn sphincs_signers(
    from: usize,
    to: usize,
) -> Vec<(sphincs::SphincsPublicKey, sphincs::Message, sphincs::SphincsSignature)> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_sphincs_signers(to)[from..to].to_vec()
}

/// Report the shape and cost of one aggregation node.
fn report(label: &str, stats: &lean_vm::cpu::Stats, sig: &EthereumProof, prove_time: &primitives::bench::Timing) {
    let base_cycles: usize = stats.base_counts.iter().sum();
    println!("{label}");
    // The program's own work, then what gets proven: the fill blocks bring each table
    // to a power of two so that none needs padding rows, so the proven total is the sum
    // of those powers.
    println!(
        "  cycles (VM steps)           : {} = {}",
        pretty_integer(base_cycles),
        crate::report::pow(base_cycles)
    );
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(sig.proof());
    // The whole `aggregate` call, not just `cpu::prove`: for a node that also
    // covers verifying each child and batching the deferred claims, which are
    // real per-node costs. `--tracing` breaks it down.
    println!(
        "  proving time                : {} s{}      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        crate::report::peak_gib()
    );
}

/// How a benchmark names a leaf of either scheme or of both.
fn describe(n_xmss: usize, n_sphincs: usize) -> String {
    match (n_xmss, n_sphincs) {
        (x, 0) => format!("{} XMSS", pretty_integer(x)),
        (0, s) => format!("{} SPHINCS", pretty_integer(s)),
        (x, s) => format!("{} XMSS and {} SPHINCS", pretty_integer(x), pretty_integer(s)),
    }
}

/// Prove signatures and `n_blobs` blobs in one leaf, then verify it.
///
/// Proving runs one discarded warmup pass followed by `plan.repeat` measured
/// passes; see [`primitives::bench`] for why the first pass is not
/// representative and why the cooldown matters.
pub fn run_aggregation(n_xmss: usize, n_sphincs: usize, n_blobs: usize, log_inv_rate: usize, plan: Plan) {
    assert!(
        n_xmss > 0 || n_sphincs > 0 || n_blobs > 0,
        "a leaf needs signatures or blobs"
    );
    assert!(n_blobs <= lean_da::DA_MAX_ROWS, "too many blobs in one commitment");
    let trace_span = tracing::info_span!("aggregation", n_xmss, n_sphincs, n_blobs, log_inv_rate).entered();
    // Spawn the worker pool before any timed work, so no kernel pays the spawn
    // cost. Opting into the arena is the calling *process's* decision (one region,
    // one proof at a time), so it stays in `main`, not here.
    lean_vm::init_prover_pool();
    let raw_xmss = signers(0, n_xmss);
    let raw_sphincs = sphincs_signers(0, n_sphincs);
    let blobs = blobs(n_blobs, 0);
    // Only the final measured pass of each stage is traced: the tree describes the
    // proof the reported timings are about, instead of repeating itself per pass.
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        aggregate_with_stats(
            &[],
            raw_xmss.clone(),
            raw_sphincs.clone(),
            None,
            DaInput {
                rows: &blobs,
                roots: None,
            },
            log_inv_rate,
        )
        .expect("leaf aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        sig.verify().expect("the leaf aggregate verifies");
    });
    drop(trace_span);

    let mut inputs = Vec::new();
    if n_xmss > 0 || n_sphincs > 0 {
        inputs.push(format!("{} signatures", describe(n_xmss, n_sphincs)));
    }
    if n_blobs > 0 {
        inputs.push(format!("{} blobs", pretty_integer(n_blobs)));
    }
    report(
        &format!("\naggregation, {}", inputs.join(", ")),
        &stats,
        &sig,
        &prove_time,
    );
    if n_xmss > 0 || n_sphincs > 0 {
        println!(
            "  per signature               : {} signatures/s",
            pretty_f64((n_xmss + n_sphincs) as f64 / prove_time.mean())
        );
    }
    if n_blobs > 0 {
        let payload_mib = (blobs.len() * size_of::<u64>()) as f64 / (1 << 20) as f64;
        println!(
            "  blob throughput             : {} blobs/s, {} MiB/s",
            pretty_f64(n_blobs as f64 / prove_time.mean()),
            pretty_f64(payload_mib / prove_time.mean())
        );
    }
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// Prove `n` leaves with signatures and distinct blob payloads, then aggregate them in one
/// recursion step and verify the result. The leaves are built once; only the
/// recursion step is measured.
pub fn run_recursion(
    n: usize,
    per_leaf: usize,
    sphincs_per_leaf: usize,
    blobs_per_leaf: usize,
    log_inv_rate: usize,
    enable_tracing: bool,
    plan: Plan,
) {
    assert!((1..=crate::MAX_RECURSIONS).contains(&n), "invalid child count");
    assert!(
        per_leaf > 0 || sphincs_per_leaf > 0 || blobs_per_leaf > 0,
        "a leaf needs signatures or blobs"
    );
    assert!(
        blobs_per_leaf <= lean_da::DA_MAX_ROWS,
        "too many blobs in one commitment"
    );
    assert!(
        blobs_per_leaf == 0 || n <= crate::MAX_DA_ROOTS,
        "too many distinct DA roots"
    );
    lean_vm::init_prover_pool();
    let all = signers(0, n * per_leaf);
    let all_sphincs = sphincs_signers(0, n * sphincs_per_leaf);
    let started = std::time::Instant::now();
    let guest_instructions: usize = crate::aggregation::unified_guest()
        .fn_ranges
        .iter()
        .map(|(_, _, len)| *len as usize)
        .sum();
    let compile_time = started.elapsed();

    let children: Vec<EthereumProof> = (0..n)
        .map(|k| {
            aggregate(
                &[],
                all[k * per_leaf..(k + 1) * per_leaf].to_vec(),
                all_sphincs[k * sphincs_per_leaf..(k + 1) * sphincs_per_leaf].to_vec(),
                &blobs(blobs_per_leaf, k as u64),
                None,
                log_inv_rate,
            )
            .expect("leaf aggregates")
        })
        .collect();

    if enable_tracing {
        primitives::init_tracing();
    }
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        aggregate_with_stats(&children, vec![], vec![], None, DaInput::default(), log_inv_rate)
            .expect("node aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        sig.verify().expect("the recursive aggregate verifies");
    });

    println!(
        "aggregation bytecode: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(guest_instructions),
        crate::aggregation::unified_guest().prog.len().trailing_zeros(),
        pretty_f64(compile_time.as_secs_f64())
    );
    let mut inputs = Vec::new();
    if per_leaf > 0 || sphincs_per_leaf > 0 {
        inputs.push(format!("{} signatures", describe(per_leaf, sphincs_per_leaf)));
    }
    if blobs_per_leaf > 0 {
        inputs.push(format!("{blobs_per_leaf} blobs"));
    }
    report(
        &format!("\nrecursion {n}\u{2192}1, over leaves of {}", inputs.join(", ")),
        &stats,
        &sig,
        &prove_time,
    );
    if blobs_per_leaf > 0 {
        assert_eq!(
            sig.da_commitments().len(),
            n,
            "every child's distinct root must survive recursion"
        );
        println!("  retained DA roots           : {n}");
    }
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
