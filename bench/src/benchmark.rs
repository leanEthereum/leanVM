//! The two benchmarks: one leaf of the aggregation tree (`aggregate`), and an
//! n→1 recursion step over leaves of that size (`recursion`). Aggregation accepts
//! signature counts and a blob count; recursion accepts these counts per leaf.

use aggregation::{AggregateClaims, AggregateProof, OutputClaims, aggregate, signers_cache};
use bench_harness::{Plan, Timing};
use isa::{Prover, Stats, pretty_f64, pretty_integer};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};

fn blobs(n: usize, seed: u64) -> Vec<lean_da::Blob> {
    let mut rng = StdRng::seed_from_u64(seed);
    let symbols: Vec<u128> = (0..n * lean_da::BLOB_SYMBOLS).map(|_| rng.random()).collect();
    symbols.as_chunks().0.to_vec()
}

/// Signatures as the aggregation API takes them, each with its key and message.
type RawLeanXmss = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
type RawLeanSphincs = (
    lean_sphincs::LeanSphincsPublicKey,
    lean_sphincs::Message,
    lean_sphincs::LeanSphincsSignature,
);

/// Cached signers `[from, to)`, as the aggregation API takes them.
fn signers<P: Prover>(from: usize, to: usize) -> Vec<RawLeanXmss> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_signers::<P>(to)[from..to].to_vec()
}

/// Each leanSPHINCS signer comes with the message it signed, as the leanXMSS ones do.
fn lean_sphincs_signers<P: Prover>(from: usize, to: usize) -> Vec<RawLeanSphincs> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_lean_sphincs_signers::<P>(to)[from..to].to_vec()
}

/// Report the shape and cost of one aggregation node.
fn report(label: &str, stats: &Stats, sig: &AggregateProof, prove_time: &Timing) {
    println!("{label}");
    println!(
        "  cycles (VM steps)           : {} = {}",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!(
        "    details                   : {}",
        crate::report::details(stats, aggregation::unified_guest().code_len())
    );
    crate::report::print_proof_size(sig.to_bytes().len());
    // The whole `aggregate` call, not just `cpu::prove`: for a node that also
    // covers replaying each child and batching the deferred claims, which are
    // real per-node costs. `--tracing` breaks it down.
    println!(
        "  proving time                : {} s{}      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        crate::report::peak_gib()
    );
}

/// The blobs' matrix, `None` for no blobs.
fn matrix(blobs: &[lean_da::Blob]) -> Option<lean_da::BlobMatrix> {
    (!blobs.is_empty()).then(|| lean_da::BlobMatrix::build(blobs).expect("at most DA_MAX_ROWS blobs"))
}

/// How a benchmark names a leaf of either scheme or of both.
fn describe(n_lean_xmss: usize, n_lean_sphincs: usize) -> String {
    match (n_lean_xmss, n_lean_sphincs) {
        (x, 0) => format!("{} leanXMSS", pretty_integer(x)),
        (0, s) => format!("{} leanSPHINCS", pretty_integer(s)),
        (x, s) => format!("{} leanXMSS and {} leanSPHINCS", pretty_integer(x), pretty_integer(s)),
    }
}

/// Prove signatures and `n_blobs` blobs in one leaf, then verify it.
///
/// Proving runs one discarded warmup pass followed by `plan.repeat` measured
/// passes; see [`bench_harness`] for why the first pass is not
/// representative and why the cooldown matters.
pub fn run_aggregation<P: Prover>(
    n_lean_xmss: usize,
    n_lean_sphincs: usize,
    n_blobs: usize,
    log_inv_rate: usize,
    plan: Plan,
) {
    assert!(
        n_lean_xmss > 0 || n_lean_sphincs > 0 || n_blobs > 0,
        "a leaf needs signatures or blobs"
    );
    let trace_span = tracing::info_span!("aggregation", n_lean_xmss, n_lean_sphincs, n_blobs, log_inv_rate).entered();
    let raw_lean_xmss = signers::<P>(0, n_lean_xmss);
    let raw_lean_sphincs = lean_sphincs_signers::<P>(0, n_lean_sphincs);
    let blobs = blobs(n_blobs, 0);
    // Only the final measured pass of each stage is traced: the tree describes the
    // proof the reported timings are about, instead of repeating itself per pass.
    let ((claims, sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        aggregate::<P>(
            &[],
            raw_lean_xmss.clone(),
            raw_lean_sphincs.clone(),
            matrix(&blobs).as_ref(),
            OutputClaims::All,
            log_inv_rate,
        )
        .expect("leaf aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        assert!(sig.verify(&claims), "the leaf aggregate verifies");
    });
    drop(trace_span);

    let mut inputs = Vec::new();
    if n_lean_xmss > 0 || n_lean_sphincs > 0 {
        inputs.push(format!("{} signatures", describe(n_lean_xmss, n_lean_sphincs)));
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
    if n_lean_xmss > 0 || n_lean_sphincs > 0 {
        println!(
            "  per signature               : {} signatures/s",
            pretty_f64((n_lean_xmss + n_lean_sphincs) as f64 / prove_time.mean())
        );
    }
    if n_blobs > 0 {
        let payload_mib = size_of_val(blobs.as_slice()) as f64 / (1 << 20) as f64;
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

/// Prove `n` leaves with signatures and distinct blob payloads at `leaf_log_inv_rate`, then
/// aggregate them in one recursion step at `log_inv_rate` and verify the result. The leaves come
/// from a cache on disk, proved once in a process of their own; only the recursion step is measured.
pub fn run_recursion<P: Prover>(
    n: usize,
    per_leaf: usize,
    lean_sphincs_per_leaf: usize,
    blobs_per_leaf: usize,
    leaf_log_inv_rate: usize,
    log_inv_rate: usize,
    enable_tracing: bool,
    plan: Plan,
) {
    assert!((1..=aggregation::MAX_RECURSIONS).contains(&n), "invalid child count");
    assert!(
        per_leaf > 0 || lean_sphincs_per_leaf > 0 || blobs_per_leaf > 0,
        "a leaf needs signatures or blobs"
    );
    let started = std::time::Instant::now();
    let guest_instructions = aggregation::unified_guest().code_len();
    let compile_time = started.elapsed();
    let shape = LeafShape {
        per_leaf,
        lean_sphincs_per_leaf,
        blobs_per_leaf,
        log_inv_rate: leaf_log_inv_rate,
    };
    if std::env::var_os(PROVE_LEAVES).is_some() {
        return shape.prove_missing::<P>(n);
    }
    let children = shape.leaves(n);

    if enable_tracing {
        bench_harness::init_tracing();
    }
    let ((claims, sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        aggregate::<P>(&children, vec![], vec![], None, OutputClaims::All, log_inv_rate).expect("node aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        assert!(sig.verify(&claims), "the recursive aggregate verifies");
    });

    println!(
        "aggregation bytecode: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(guest_instructions),
        aggregation::unified_guest().prog.len().trailing_zeros(),
        pretty_f64(compile_time.as_secs_f64())
    );
    let mut inputs = Vec::new();
    if per_leaf > 0 || lean_sphincs_per_leaf > 0 {
        inputs.push(format!("{} signatures", describe(per_leaf, lean_sphincs_per_leaf)));
    }
    if blobs_per_leaf > 0 {
        inputs.push(format!("{blobs_per_leaf} blobs"));
    }
    if leaf_log_inv_rate != log_inv_rate {
        inputs.push(format!(
            "leaf rate = 1/{}, recursion rate = 1/{}",
            2usize.pow(leaf_log_inv_rate as u32),
            2usize.pow(log_inv_rate as u32)
        ));
    }
    report(
        &format!("\nrecursion {n}\u{2192}1, over leaves of {}", inputs.join(", ")),
        &stats,
        &sig,
        &prove_time,
    );
    if blobs_per_leaf > 0 {
        assert_eq!(
            claims.da_commitment, children[0].0.da_commitment,
            "the first child's root is passed on"
        );
    }
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// What the leaves of a recursion step share: each one's signature and blob counts, and its rate.
#[derive(Clone, Copy, Hash)]
struct LeafShape {
    per_leaf: usize,
    lean_sphincs_per_leaf: usize,
    blobs_per_leaf: usize,
    log_inv_rate: usize,
}

/// Set by [`LeafShape::leaves`] on the process it starts, which proves the leaves the cache lacks.
const PROVE_LEAVES: &str = "LEANVM_PROVE_LEAVES";

impl LeafShape {
    /// Leaf `k`'s file in the cache: its claims after their length, then its proof. One file per guest, signers'
    /// version, shape and leaf, so recursion steps of every width share their leaves.
    fn path(&self, k: usize) -> PathBuf {
        let guest = aggregation::unified_guest().bytecode().fiat_shamir_iv();
        let mut hasher = DefaultHasher::new();
        (guest, signers_cache::VERSION, self, k).hash(&mut hasher);
        let name = format!("../target/leaves-cache/leaf_{:016x}.bin", hasher.finish());
        Path::new(env!("CARGO_MANIFEST_DIR")).join(name)
    }

    /// Leaf `k` from the cache, if it is there and verifies: a leaf an earlier protocol proved is proved again.
    fn cached(&self, k: usize) -> Option<(AggregateClaims, AggregateProof)> {
        let bytes = std::fs::read(self.path(k)).ok()?;
        let (len, rest) = bytes.split_first_chunk()?;
        let (claims, proof) = rest.split_at_checked(u64::from_le_bytes(*len) as usize)?;
        let (claims, proof) = (AggregateClaims::from_bytes(claims)?, AggregateProof::from_bytes(proof)?);
        proof.verify(&claims).then_some((claims, proof))
    }

    /// The first `n` leaves, from the cache, those it lacks proved first by this same command rerun with
    /// [`PROVE_LEAVES`] set. Peak memory is the process's high-water mark, which proving them here would make a
    /// leaf's.
    fn leaves(&self, n: usize) -> Vec<(AggregateClaims, AggregateProof)> {
        let cached = || (0..n).map(|k| self.cached(k)).collect::<Option<Vec<_>>>();
        cached().unwrap_or_else(|| {
            let status = std::process::Command::new(std::env::current_exe().expect("this binary's path"))
                .args(std::env::args_os().skip(1))
                .env(PROVE_LEAVES, "1")
                .status()
                .expect("the leaves' process starts");
            assert!(status.success(), "the leaves' process failed");
            cached().expect("every leaf is cached")
        })
    }

    /// Prove those of the first `n` leaves that the cache lacks, each written to its file.
    fn prove_missing<P: Prover>(&self, n: usize) {
        let missing: Vec<usize> = (0..n).filter(|&k| self.cached(k).is_none()).collect();
        let lean_xmss = signers::<P>(0, n * self.per_leaf);
        let lean_sphincs = lean_sphincs_signers::<P>(0, n * self.lean_sphincs_per_leaf);
        for (done, &k) in missing.iter().enumerate() {
            println!("  proving leaf {}/{}", done + 1, missing.len());
            let (claims, proof, _) = aggregate::<P>(
                &[],
                lean_xmss[k * self.per_leaf..][..self.per_leaf].to_vec(),
                lean_sphincs[k * self.lean_sphincs_per_leaf..][..self.lean_sphincs_per_leaf].to_vec(),
                matrix(&blobs(self.blobs_per_leaf, k as u64)).as_ref(),
                OutputClaims::All,
                self.log_inv_rate,
            )
            .expect("leaf aggregates");
            let claims = claims.to_bytes();
            let bytes = [&(claims.len() as u64).to_le_bytes()[..], &claims, &proof.to_bytes()].concat();
            // Written beside its place, then moved there: a reader never finds half a leaf.
            let path = self.path(k);
            let partial = path.with_extension(format!("{}.partial", std::process::id()));
            std::fs::create_dir_all(path.parent().expect("the cache's directory"))
                .and_then(|()| std::fs::write(&partial, bytes))
                .and_then(|()| std::fs::rename(&partial, &path))
                .expect("the leaf is cached");
        }
    }
}
