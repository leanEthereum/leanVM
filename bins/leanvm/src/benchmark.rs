//! The two benchmarks: one leaf of the aggregation tree (`aggregate`), and an
//! n→1 recursion step over leaves of that size (`recursion`). Aggregation accepts
//! signature counts and a blob count; recursion accepts these counts per leaf.

use bench::{Plan, Timing};
use primitives::{pretty_f64, pretty_integer};
use rand::{Rng, SeedableRng, rngs::StdRng};
use rec_aggregation::{EthereumClaims, EthereumProof, aggregate, aggregate_with_stats, signers_cache};
use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use signatures::{lean_sphincs, lean_xmss};

fn blobs(n: usize, seed: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..n * lean_da::BLOB_SYMBOLS).map(|_| rng.random()).collect()
}

/// Signatures as the aggregation API takes them, each with its key and message.
type RawLeanXmss = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
type RawLeanSphincs = (
    lean_sphincs::LeanSphincsPublicKey,
    lean_sphincs::Message,
    lean_sphincs::LeanSphincsSignature,
);

/// Cached signers `[from, to)`, as the aggregation API takes them: one message for
/// all, each signature at its own signer's leaf index.
fn signers(from: usize, to: usize) -> Vec<RawLeanXmss> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_signers(to)[from..to]
        .iter()
        .map(|(pk, sig)| (*pk, signers_cache::message(), sig.clone()))
        .collect()
}

/// Each leanSPHINCS signer comes with the message it signed, as the leanXMSS ones do.
fn lean_sphincs_signers(from: usize, to: usize) -> Vec<RawLeanSphincs> {
    if to == 0 {
        return Vec::new();
    }
    signers_cache::get_lean_sphincs_signers(to)[from..to].to_vec()
}

/// Report the shape and cost of one aggregation node.
fn report(label: &str, stats: &leanvm_core::cpu::Stats, sig: &EthereumProof, prove_time: &Timing) {
    println!("{label}");
    println!(
        "  cycles (VM steps)           : {} = {}",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(sig.proof_bytes().len());
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
/// passes; see [`bench`] for why the first pass is not
/// representative and why the cooldown matters.
pub fn run_aggregation(n_lean_xmss: usize, n_lean_sphincs: usize, n_blobs: usize, log_inv_rate: usize, plan: Plan) {
    assert!(
        n_lean_xmss > 0 || n_lean_sphincs > 0 || n_blobs > 0,
        "a leaf needs signatures or blobs"
    );
    let trace_span = tracing::info_span!("aggregation", n_lean_xmss, n_lean_sphincs, n_blobs, log_inv_rate).entered();
    rec_aggregation::warm_up();
    let raw_lean_xmss = signers(0, n_lean_xmss);
    let raw_lean_sphincs = lean_sphincs_signers(0, n_lean_sphincs);
    let blobs = blobs(n_blobs, 0);
    // Only the final measured pass of each stage is traced: the tree describes the
    // proof the reported timings are about, instead of repeating itself per pass.
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        aggregate_with_stats(
            &[],
            raw_lean_xmss.clone(),
            raw_lean_sphincs.clone(),
            &blobs,
            None,
            log_inv_rate,
        )
        .expect("leaf aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        sig.verify().expect("the leaf aggregate verifies");
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

/// Prove `n` leaves with signatures and distinct blob payloads at `leaf_log_inv_rate`, then
/// aggregate them in one recursion step at `log_inv_rate` and verify the result. The leaves are
/// built once, in a process of their own; only the recursion step is measured.
pub fn run_recursion(
    n: usize,
    per_leaf: usize,
    lean_sphincs_per_leaf: usize,
    blobs_per_leaf: usize,
    leaf_log_inv_rate: usize,
    log_inv_rate: usize,
    enable_tracing: bool,
    plan: Plan,
) {
    assert!(
        (1..=rec_aggregation::MAX_RECURSIONS).contains(&n),
        "invalid child count"
    );
    assert!(
        per_leaf > 0 || lean_sphincs_per_leaf > 0 || blobs_per_leaf > 0,
        "a leaf needs signatures or blobs"
    );
    let started = std::time::Instant::now();
    let guest_instructions = rec_aggregation::aggregation::unified_guest().code_len();
    let compile_time = started.elapsed();
    rec_aggregation::warm_up();
    if let Some(out) = std::env::var_os(LEAVES_OUT) {
        return write_leaves(
            n,
            per_leaf,
            lean_sphincs_per_leaf,
            blobs_per_leaf,
            leaf_log_inv_rate,
            out.as_ref(),
        );
    }
    let children = leaves_from_subprocess(n);

    if enable_tracing {
        bench::init_tracing();
    }
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        aggregate_with_stats(&children, vec![], vec![], &[], None, log_inv_rate).expect("node aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        sig.verify().expect("the recursive aggregate verifies");
    });

    println!(
        "aggregation bytecode: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(guest_instructions),
        rec_aggregation::aggregation::unified_guest()
            .prog
            .len()
            .trailing_zeros(),
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
        inputs.push(format!("proven at log-inv-rate {leaf_log_inv_rate}"));
    }
    report(
        &format!("\nrecursion {n}\u{2192}1, over leaves of {}", inputs.join(", ")),
        &stats,
        &sig,
        &prove_time,
    );
    if blobs_per_leaf > 0 {
        assert_eq!(
            sig.claims().da_commitment,
            children[0].claims().da_commitment,
            "the first child's root is passed on"
        );
    }
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// Prove a recursion step's `n` leaves and write them to `out`: each leaf's claims, then its proof's
/// bytes after their length.
fn write_leaves(
    n: usize,
    per_leaf: usize,
    lean_sphincs_per_leaf: usize,
    blobs_per_leaf: usize,
    log_inv_rate: usize,
    out: &std::path::Path,
) {
    let all = signers(0, n * per_leaf);
    let all_lean_sphincs = lean_sphincs_signers(0, n * lean_sphincs_per_leaf);
    let mut bytes = Vec::new();
    for k in 0..n {
        let leaf = aggregate(
            &[],
            all[k * per_leaf..(k + 1) * per_leaf].to_vec(),
            all_lean_sphincs[k * lean_sphincs_per_leaf..(k + 1) * lean_sphincs_per_leaf].to_vec(),
            &blobs(blobs_per_leaf, k as u64),
            None,
            log_inv_rate,
        )
        .expect("leaf aggregates");
        write_claims(&mut bytes, leaf.claims());
        let proof = leaf.proof_bytes();
        bytes.extend((proof.len() as u64).to_le_bytes());
        bytes.extend(proof);
    }
    std::fs::write(out, bytes).expect("the leaves are written");
}

/// A leaf's claims in the leaves' file: each list as its length and its `(key, message)` pairs, then
/// a 0/1 byte for whether there is a DA root and 32 root bytes, zero without one. The proof carries
/// no claims; the parent trusts its subprocess for them, standing in for a receiver that knows them.
fn write_claims(out: &mut Vec<u8>, claims: &EthereumClaims) {
    out.extend((claims.xmss.len() as u64).to_le_bytes());
    for (pk, message) in &claims.xmss {
        out.extend(pk.to_bytes());
        out.extend(message);
    }
    out.extend((claims.lean_sphincs.len() as u64).to_le_bytes());
    for (pk, message) in &claims.lean_sphincs {
        out.extend(pk.to_bytes());
        out.extend(message);
    }
    out.push(u8::from(claims.da_commitment.is_some()));
    out.extend(claims.da_commitment.unwrap_or_default());
}

/// The leaves' file, read back: the bytes not yet read.
struct LeavesFile<'a>(&'a [u8]);

impl<'a> LeavesFile<'a> {
    fn take(&mut self, n: usize) -> &'a [u8] {
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        head
    }

    fn array<const N: usize>(&mut self) -> [u8; N] {
        self.take(N).try_into().expect("N bytes")
    }

    fn count(&mut self) -> usize {
        u64::from_le_bytes(self.array()) as usize
    }

    /// The inverse of [`write_claims`].
    fn claims(&mut self) -> EthereumClaims {
        let n = self.count();
        let xmss = (0..n)
            .map(|_| (LeanXmssPublicKey::from_bytes(&self.array()), self.array()))
            .collect();
        let n = self.count();
        let lean_sphincs = (0..n)
            .map(|_| {
                (
                    lean_sphincs::LeanSphincsPublicKey::from_bytes(&self.array()),
                    self.array(),
                )
            })
            .collect();
        let [has_root] = self.array();
        let root = self.array();
        EthereumClaims {
            xmss,
            lean_sphincs,
            da_commitment: (has_root == 1).then_some(root),
        }
    }
}

/// Set by [`leaves_from_subprocess`] on the process it starts: the file that process writes the leaves to.
const LEAVES_OUT: &str = "LEANVM_LEAVES_OUT";

/// The leaves of [`run_recursion`], from this same command rerun with [`LEAVES_OUT`] set. Peak
/// memory is the process's high-water mark, which proving them here would make a leaf's.
fn leaves_from_subprocess(n: usize) -> Vec<EthereumProof> {
    let out = std::env::temp_dir().join(format!("leanvm-leaves-{}.bin", std::process::id()));
    let status = std::process::Command::new(std::env::current_exe().expect("this binary's path"))
        .args(std::env::args_os().skip(1))
        .env(LEAVES_OUT, &out)
        .status()
        .expect("the leaves' process starts");
    assert!(status.success(), "the leaves' process failed");
    let bytes = std::fs::read(&out).expect("the leaves are read");
    std::fs::remove_file(&out).expect("the leaves' file is removed");

    let mut file = LeavesFile(&bytes);
    let mut leaves = Vec::with_capacity(n);
    while !file.0.is_empty() {
        let claims = file.claims();
        let len = file.count();
        leaves.push(EthereumProof::from_proof_bytes(file.take(len), claims).expect("a leaf proof"));
    }
    assert_eq!(leaves.len(), n, "one proof per leaf");
    leaves
}
