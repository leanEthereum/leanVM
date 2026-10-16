//! The programs tracked in CI, reported as Bencher Metric Format JSON or, counted without a
//! proof, as a markdown table, or both from one pass.
//!
//! Two lists. The counts are exact and cheap, so they are taken at the README's sizes, the
//! most one proof holds, on one runner (`.github/workflows/counts.yml`), which compares a
//! PR's with its base's: they are the same on every machine. Proving on CI's GitHub-hosted
//! runners (16 GB, `.github/workflows/bench.yml`) takes the sizes that fit them (leanXMSS and
//! leanSPHINCS at a quarter, and no leanDA, whose one blob is its smallest run), and a PR's
//! base and head are proven in turns on one runner and compared there. leanXMSS at a quarter,
//! and the 2-to-1 and 4-to-1 trees over it, retain their 1, 4 and 8 performance-worker cases.
//! Other cases use exactly 16 total threads, each in a process of its own (`THREADS`).
//! A case's name is what a PR's results are matched by, so
//! renaming one or changing its input shows it as new.
//!
//! An aggregation tree is tracked the same way: each kind of node's circuit counted without a
//! proof (the leaf's run measured gives the shape its proofs announce), and one node of each
//! kind proven over copies of one leaf proof. A signer-set tree (`aggregate-signers-...`) is
//! counted the same way, its node circuit of every arity, and proven the same way, each node
//! declaring the union of its children's sets and verified by it.

use crate::refuse;
use crate::workload::{Items, Workload};
use bench::pretty_integer;
use bench::{Heap, Metric, Plan, Stage, Timing, bencher_json};
#[cfg(feature = "circuits")]
use leanvm::aggregate::Tier;
use leanvm::aggregate::{
    Aggregate, Capacity, CircuitStats, ClaimLeaf, ClaimShape, Kind, Leaf, LeafShape, Tree, TreeError, TreeProof,
    TreeShape,
};
use leanvm::{ProvenRun, Prover, Rate, Stats};
use serde_json::{Map, Value};
use std::fmt::Write as _;
use std::fs::OpenOptions;
use std::io::Write as _;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;

/// A tracked benchmark: its name, which CI matches a PR's results by, and its run.
struct Case {
    name: &'static str,
    workload: Workload,
}

impl Case {
    const fn new(name: &'static str, workload: Workload) -> Self {
        Self { name, workload }
    }

    /// How many items the run covers, and what one is called: every tracked run counts in items.
    const fn items(&self) -> Items {
        self.workload.items.expect("a tracked run counts in items")
    }
}

/// Counted without a proof: the README's sizes.
fn counted() -> Vec<Case> {
    vec![
        Case::new("fibonacci-asm-2000000", Workload::fibonacci(2_000_000)),
        Case::new("hash-50000", Workload::hash(50_000)),
        Case::new("leanxmss-400", Workload::leanxmss(400)),
        Case::new("leansphincs-104", Workload::leansphincs(104)),
        Case::new("leanda-1", Workload::leanda(1)),
        Case::new("shielded-1035", Workload::shielded(1035)),
    ]
}

/// Builds a case given its name.
type Build = fn(&'static str) -> Case;

/// Proven: the sizes that fit a GitHub-hosted runner, each built only if it is proven.
fn proven() -> [(&'static str, Build); 7] {
    [
        ("fibonacci-asm-2000000-16thread", |name| {
            Case::new(name, Workload::fibonacci(2_000_000))
        }),
        ("hash-50000-16thread", |name| Case::new(name, Workload::hash(50_000))),
        ("leanxmss-100-16thread", |name| Case::new(name, Workload::leanxmss(100))),
        ("leanxmss-100-1thread", |name| Case::new(name, Workload::leanxmss(100))),
        ("leanxmss-100-4thread", |name| Case::new(name, Workload::leanxmss(100))),
        ("leanxmss-100-8thread", |name| Case::new(name, Workload::leanxmss(100))),
        ("leansphincs-26-16thread", |name| {
            Case::new(name, Workload::leansphincs(26))
        }),
    ]
}

/// Every timed case's pool size. Legacy 1/4/8 cases select performance workers through
/// `LEANVM_NUM_THREADS`; 16-thread children initialize an exact total pool at CLI startup.
const THREADS: [(&str, usize); 17] = [
    ("fibonacci-asm-2000000-16thread", 16),
    ("hash-50000-16thread", 16),
    ("leanxmss-100-16thread", 16),
    ("leansphincs-26-16thread", 16),
    ("aggregate-leanxmss-100-2to1-16thread", 16),
    ("aggregate-leanxmss-100-4to1-16thread", 16),
    ("aggregate-signers-leanxmss-100-2to1-16thread", 16),
    ("aggregate-signers-leanxmss-100-4to1-16thread", 16),
    ("leanxmss-100-1thread", 1),
    ("leanxmss-100-4thread", 4),
    ("leanxmss-100-8thread", 8),
    ("aggregate-leanxmss-100-2to1-1thread", 1),
    ("aggregate-leanxmss-100-2to1-4thread", 4),
    ("aggregate-leanxmss-100-2to1-8thread", 8),
    ("aggregate-leanxmss-100-4to1-1thread", 1),
    ("aggregate-leanxmss-100-4to1-4thread", 4),
    ("aggregate-leanxmss-100-4to1-8thread", 8),
];

/// One of a tree's circuits: the first level's, or the node circuit of one arity.
#[derive(Clone, Copy)]
enum NodeCircuit {
    First,
    Node(usize),
}

/// An aggregation tree over copies of one case's proof: first-level nodes of `arity_0` leaves,
/// nodes of `arity` tree proofs, or with a capacity a signer-set tree, whose nodes take up to
/// `arity`. A tree's name ends `<N>to1` when both are `N`: every node combines `N` proofs into
/// 1; then `-<T>thread` when it is proven on `T` threads (`THREADS`).
struct Aggregation {
    name: &'static str,
    leaf: Workload,
    arity_0: usize,
    arity: usize,
    signers: Option<Capacity>,
}

impl Aggregation {
    const fn new(name: &'static str, leaf: Workload, arity_0: usize, arity: usize) -> Self {
        Self {
            name,
            leaf,
            arity_0,
            arity,
            signers: None,
        }
    }

    /// A signer-set tree of this capacity, over a leaf that publishes its signer set.
    const fn signers(name: &'static str, leaf: Workload, arity_0: usize, arity: usize, capacity: Capacity) -> Self {
        Self {
            name,
            leaf,
            arity_0,
            arity,
            signers: Some(capacity),
        }
    }

    /// The tree over the leaf's proofs shaped `shape`, every tree proof at `rate`.
    fn tree(&self, shape: LeafShape, rate: Rate) -> Tree<'_> {
        let shape = TreeShape {
            leaf: shape,
            arity_0: self.arity_0,
            arity: self.arity,
            rate,
            claims: self.signers.map(ClaimShape::new),
        };
        Tree::new(&self.leaf.program, shape).unwrap_or_else(|e| refuse(format_args!("{}: {e}", self.name)))
    }

    /// A circuit's benchmark name, and what the markdown table calls it: `<name>-first`, a
    /// first-level node (the RISC-V verifier in rows over `arity_0` leaf proofs), and
    /// `<name>-node`, a node of the largest arity (the recursion verifier in rows over `arity`
    /// child proofs); a signer-set tree's smaller node circuits are `<name>-node<k>`.
    fn node(&self, circuit: NodeCircuit) -> (String, String) {
        let signers = self.signers.map_or_else(String::new, |c| {
            format!(
                ", signer sets of fewer than {} claims in at most {} groups",
                pretty_integer(&c.claims),
                pretty_integer(&c.groups)
            )
        });
        match circuit {
            NodeCircuit::First => (
                format!("{}-first", self.name),
                format!("first-level node over {} x {}{signers}", self.arity_0, self.leaf.title),
            ),
            NodeCircuit::Node(arity) => (
                if arity == self.arity {
                    format!("{}-node", self.name)
                } else {
                    format!("{}-node{arity}", self.name)
                },
                format!(
                    "node over {arity} tree proofs, first level {} x {}{signers}",
                    self.arity_0, self.leaf.title
                ),
            ),
        }
    }
}

/// Aggregation trees counted without a proof: the README's leaves, 2 to 1 (`cargo leanvm
/// aggregate`'s shape) and 4 to 1, and the signer-set trees of those shapes, each sized for
/// its tree of distinct leaves.
fn counted_trees() -> Vec<Aggregation> {
    let leaf = || Workload::leanxmss(400);
    vec![
        Aggregation::new("aggregate-leanxmss-400-2to1", leaf(), 2, 2),
        Aggregation::new("aggregate-leanxmss-400-4to1", leaf(), 4, 4),
        Aggregation::signers(
            "aggregate-signers-leanxmss-400-2to1",
            leaf(),
            2,
            2,
            sixteen_groups(1601),
        ),
        Aggregation::signers(
            "aggregate-signers-leanxmss-400-4to1",
            leaf(),
            4,
            4,
            sixteen_groups(6401),
        ),
    ]
}

/// Builds an aggregation tree given its name.
type BuildTree = fn(&'static str) -> Aggregation;

/// Aggregation trees proven: the counted trees' arities over leaves of a size proven above, and
/// both trees on 16 total threads and on the legacy 1, 4 and 8 performance workers, and both
/// signer-set trees on 16, each sized for its tree of distinct leaves. Each gives two
/// benchmarks, `<name>-first` and `<name>-node`.
fn proven_trees() -> [(&'static str, BuildTree); 10] {
    [
        ("aggregate-leanxmss-100-2to1-16thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 2, 2)
        }),
        ("aggregate-leanxmss-100-4to1-16thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 4, 4)
        }),
        ("aggregate-signers-leanxmss-100-2to1-16thread", |name| {
            Aggregation::signers(name, Workload::leanxmss(100), 2, 2, sixteen_groups(401))
        }),
        ("aggregate-signers-leanxmss-100-4to1-16thread", |name| {
            Aggregation::signers(name, Workload::leanxmss(100), 4, 4, sixteen_groups(1601))
        }),
        ("aggregate-leanxmss-100-2to1-1thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 2, 2)
        }),
        ("aggregate-leanxmss-100-2to1-4thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 2, 2)
        }),
        ("aggregate-leanxmss-100-2to1-8thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 2, 2)
        }),
        ("aggregate-leanxmss-100-4to1-1thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 4, 4)
        }),
        ("aggregate-leanxmss-100-4to1-4thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 4, 4)
        }),
        ("aggregate-leanxmss-100-4to1-8thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 4, 4)
        }),
    ]
}

/// A signer-set tree's capacity of fewer than `claims` claims in at most 16 groups.
const fn sixteen_groups(claims: usize) -> Capacity {
    Capacity { claims, groups: 16 }
}

/// With `cycles_only`, count every case without a proof and print the counts as JSON, or with
/// `markdown` as a table, or as JSON with the table appended to `markdown_file`; otherwise
/// prove, verify and time the proven cases, or only the one named `only`, as JSON (one case
/// per process makes its `peak-memory` that case's alone). `leanda-1-16thread` is opt-in through
/// `only`, since it requires the website's larger runners.
pub fn run(
    cycles_only: bool,
    markdown: bool,
    markdown_file: Option<&Path>,
    only: Option<&str>,
    leaf_prover: &Prover,
    prover: &Prover,
    plan: Plan,
) {
    let report: Vec<_> = if cycles_only {
        let counted: Vec<_> = counted()
            .into_iter()
            .map(|case| {
                let stats = case.workload.measure();
                (case, stats)
            })
            .collect();
        let trees: Vec<_> = counted_trees()
            .into_iter()
            .map(|tree| {
                let circuits = circuits(&tree, leaf_prover.rate(), prover.rate());
                (tree, circuits)
            })
            .collect();
        let tables = table(&counted) + &tree_table(&trees);
        if markdown {
            return print!("{tables}");
        }
        if let Some(path) = markdown_file {
            OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .and_then(|mut file| file.write_all(tables.as_bytes()))
                .unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
        }
        let circuits = trees.iter().flat_map(|(tree, circuits)| {
            (circuits.iter()).map(|(kind, stats)| (tree.node(*kind).0, circuit_counts(stats)))
        });
        counted
            .iter()
            .map(|(case, stats)| (case.name.to_string(), counts(stats)))
            .chain(circuits)
            .collect()
    } else {
        let mut cases: Vec<_> = proven()
            .into_iter()
            .filter(|(name, _)| only.is_none_or(|only| only == *name))
            .collect();
        if only == Some("leanda-1-16thread") {
            cases.push((
                "leanda-1-16thread",
                (|name| Case::new(name, Workload::leanda(1))) as Build,
            ));
        }
        let trees: Vec<_> = proven_trees()
            .into_iter()
            .filter(|(name, _)| only.is_none_or(|only| only == *name))
            .collect();
        if cases.is_empty() && trees.is_empty() {
            refuse(format_args!("no tracked case is named {}", only.unwrap_or_default()));
        }
        bench::time_stages("Prove");
        // The thread count a case names, if this process's pool is not that size.
        let threads = |name: &str| {
            let &(_, threads) = THREADS.iter().find(|(case, _)| *case == name)?;
            let topology = parallel::topology();
            (threads != topology.perf || (threads == 16 && topology.efficiency != 0)).then_some(threads)
        };
        // Every case's benchmarks, proven here or by a child, as one JSON object.
        let mut benchmarks = Map::new();
        for (name, case) in cases {
            let json = threads(name).map_or_else(
                || bencher_json(&[(name.to_string(), proved(&case(name), prover, plan))]),
                |threads| on_threads(name, threads, only.is_none()),
            );
            benchmarks.extend(parsed(name, &json));
        }
        for (name, tree) in trees {
            let json = threads(name).map_or_else(
                || bencher_json(&proved_tree(&tree(name), leaf_prover, prover, plan)),
                |threads| on_threads(name, threads, only.is_none()),
            );
            benchmarks.extend(parsed(name, &json));
        }
        let json = serde_json::to_string_pretty(&Value::Object(benchmarks)).expect("JSON values print");
        return println!("{json}");
    };
    println!("{}", bencher_json(&report));
}

/// The case `name` proven by a child whose pool is `threads` threads: this executable run again
/// with this process's arguments, `--only name` added unless `add_only` is false (they name it
/// already), and `LEANVM_NUM_THREADS=threads`. Its JSON; its progress goes to this process's
/// stderr.
fn on_threads(name: &str, threads: usize, add_only: bool) -> String {
    let exe = std::env::current_exe().unwrap_or_else(|e| refuse(format_args!("{name}: {e}")));
    let mut child = Command::new(exe);
    child
        .args(std::env::args_os().skip(1))
        .env("LEANVM_NUM_THREADS", threads.to_string())
        .stderr(Stdio::inherit());
    if add_only {
        child.args(["--only", name]);
    }
    let output = child.output().unwrap_or_else(|e| refuse(format_args!("{name}: {e}")));
    if !output.status.success() {
        refuse(format_args!(
            "{name}: the {threads}-thread run failed: {}",
            output.status
        ));
    }
    String::from_utf8(output.stdout).unwrap_or_else(|e| refuse(format_args!("{name}: {e}")))
}

/// The benchmarks of case `name`'s Bencher Metric Format JSON.
fn parsed(name: &str, json: &str) -> Map<String, Value> {
    serde_json::from_str(json).unwrap_or_else(|e| refuse(format_args!("{name}: no benchmarks: {e}")))
}

/// `cycles` (the program's own instructions), `proven-rows` (the tables' heights once
/// padded to powers of two) and `committed` (the witness words): exact, the same on every
/// machine.
fn counts(stats: &Stats) -> Vec<(&'static str, Metric)> {
    vec![
        ("cycles", Metric::exact(stats.cycles())),
        ("proven-rows", Metric::exact(stats.proven_rows)),
        ("committed", Metric::exact(stats.committed)),
    ]
}

/// Each of the tree's circuits, without a proof: the first level's, then the nodes', a signer-set
/// tree's of every arity from 2. The leaf's run, measured, gives the shape its proofs announce at
/// `leaf_rate`; the tree's proofs are at `rate`.
fn circuits(tree: &Aggregation, leaf_rate: Rate, rate: Rate) -> Vec<(NodeCircuit, CircuitStats)> {
    let shape = LeafShape::measured(&tree.leaf.measure(), leaf_rate);
    let built = tree.tree(shape, rate);
    let first = (NodeCircuit::First, built.stats(Kind::First));
    match tree.signers {
        None => vec![first, (NodeCircuit::Node(tree.arity), built.stats(Kind::Node))],
        Some(_) => {
            let nodes = (2..=tree.arity).map(|arity| {
                let stats = built
                    .node_stats(arity)
                    .expect("a node circuit of every arity up to the largest");
                (NodeCircuit::Node(arity), stats)
            });
            std::iter::once(first).chain(nodes).collect()
        }
    }
}

/// Write every tracked output-tree and signer-set tree circuit, one over zero-knowledge leaves, and every claim-set tier position, plus native instruction table bindings and `Hash::circuit`'s rows at pseudorandom column weights.
///
/// CI's `rec-builder-model` workflow replays the recorded builders, checks the table slot and clock-port bindings against their Lean sources, and checks the hash rows against their Lean model.
#[cfg(feature = "circuits")]
pub fn dump(out: &Path, leaf_rate: Rate, rate: Rate) {
    let proven = [
        Aggregation::new("aggregate-leanxmss-100-2to1", Workload::leanxmss(100), 2, 2),
        Aggregation::new("aggregate-leanxmss-100-4to1", Workload::leanxmss(100), 4, 4),
    ];
    std::fs::create_dir_all(out).unwrap_or_else(|e| refuse(format_args!("{}: {e}", out.display())));
    let path = out.join("table-flushes.dump");
    std::fs::write(&path, leanvm::table_flushes()).unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
    let path = out.join("hash-rows.dump");
    std::fs::write(&path, leanvm::hash_rows()).unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
    // The same 2 to 1 tree over zero-knowledge leaves, whose first level verifies the zero-knowledge proofs.
    let zero_knowledge = Aggregation::new("aggregate-leanxmss-100-2to1-zk", Workload::leanxmss(100), 2, 2);
    let trees = (counted_trees().into_iter().chain(proven)).map(|tree| (tree, false));
    for (tree, zk) in trees.chain([(zero_knowledge, true)]) {
        let measured = LeafShape::measured(&tree.leaf.measure(), leaf_rate);
        let shape = if zk { measured.zero_knowledge() } else { measured };
        let built = tree.tree(shape, rate);
        // A tree's circuits in their positions' order: the first level's, then the node circuit of the largest arity, or a signer-set tree's of every arity from two up.
        let nodes = match tree.signers {
            None => tree.arity..=tree.arity,
            Some(_) => 2..=tree.arity,
        };
        let circuits: Vec<NodeCircuit> = std::iter::once(NodeCircuit::First)
            .chain(nodes.map(NodeCircuit::Node))
            .collect();
        assert_eq!(
            circuits.len(),
            built.circuit_count(),
            "{}: a circuit per position",
            tree.name
        );
        for (position, circuit) in circuits.into_iter().enumerate() {
            let path = out.join(format!("{}.txt", tree.node(circuit).0));
            std::fs::write(&path, built.circuit_dump(position))
                .unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
        }
    }
    let leaf = Workload::leanxmss(100);
    let measured = LeafShape::measured(&leaf.measure(), leaf_rate);
    let capacity = Capacity { claims: 12, groups: 4 };
    for (name, claims) in [
        ("claimset-single-tier", ClaimShape::new(capacity)),
        (
            "claimset-two-tier",
            ClaimShape {
                capacity,
                small: Some(Tier {
                    arity: 2,
                    capacity: Capacity { claims: 5, groups: 2 },
                }),
            },
        ),
    ] {
        let shape = TreeShape {
            leaf: measured,
            arity_0: 1,
            arity: 3,
            rate,
            claims: Some(claims),
        };
        let built = Tree::new(&leaf.program, shape).unwrap_or_else(|e| refuse(format_args!("{name}: {e}")));
        for position in 0..built.circuit_count() {
            let path = out.join(format!("{name}-circuit-{position}.txt"));
            std::fs::write(&path, built.circuit_dump(position))
                .unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
        }
    }
}

/// `rows` (the circuit's own), `proven-rows` (the tables' heights, powers of two) and
/// `committed` (the witness words): exact, the same on every machine.
fn circuit_counts(stats: &CircuitStats) -> Vec<(&'static str, Metric)> {
    let (rows, proven) = circuit_rows(stats);
    vec![
        ("rows", Metric::exact(rows)),
        ("proven-rows", Metric::exact(proven)),
        ("committed", Metric::exact(stats.committed)),
    ]
}

/// A circuit's rows, and its tables' heights, summed over its tables.
fn circuit_rows(stats: &CircuitStats) -> (usize, usize) {
    let rows = stats.tables.iter().map(|t| t.rows).sum();
    let proven = stats.tables.iter().map(|t| 1 << t.height_log).sum();
    (rows, proven)
}

/// A verification takes milliseconds, so one pass says little about it.
const VERIFY_PASSES: usize = 20;

/// The proving time, the proof's size and the verifying time, after checking the proof: the
/// output is the native reference's and it verifies. Then the time of each of the proof's
/// stages (the `Prove` span's direct children, `--tracing`'s top level), the process's peak
/// resident memory so far and the measured passes' heap.
fn proved(case: &Case, prover: &Prover, plan: Plan) -> Vec<(String, Metric)> {
    eprintln!("{}", case.name);
    let mut passes = Vec::new();
    let mut heaps = Vec::new();
    let workload = &case.workload;
    let (ProvenRun { proof, output, .. }, time) = plan.warm_then_measure(|| {
        let (proved, heap) = bench::measure_heap(|| workload.prove(prover));
        passes.push(bench::take_stages());
        heaps.push(heap);
        proved
    });
    let peak_memory = bench::peak_rss_bytes();
    let (verified, verify_time) =
        Plan::new(VERIFY_PASSES, Duration::ZERO).measure_quiet(|| workload.program.verify(output, &proof));
    verified.expect("an honest proof verifies");
    measures(
        &time,
        proof.to_bytes().len(),
        &verify_time,
        &passes[1..],
        peak_memory,
        &heaps[1..],
    )
}

/// A proven case's measures: its proving time, proof size and verifying time, each of its
/// stages over the measured passes, the peak memory, and the most any measured pass's heap
/// held at once (`heap-peak`) and allocated (`allocations`).
fn measures(
    time: &Timing,
    proof_size: usize,
    verify_time: &Timing,
    passes: &[Vec<Stage>],
    peak_memory: u64,
    heaps: &[Heap],
) -> Vec<(String, Metric)> {
    let mut report = vec![
        ("latency".to_string(), Metric::nanoseconds(time)),
        ("proof-size".to_string(), Metric::exact(proof_size)),
        ("verify".to_string(), Metric::nanoseconds(verify_time)),
        ("threads".to_string(), Metric::exact(parallel::num_threads())),
        (
            "performance-threads".to_string(),
            Metric::exact(parallel::topology().perf),
        ),
        (
            "efficiency-threads".to_string(),
            Metric::exact(parallel::topology().efficiency),
        ),
    ];
    report.extend(stages(passes));
    report.push(("peak-memory".to_string(), Metric::exact(peak_memory as usize)));
    let most = |measure: fn(&Heap) -> u64| Metric::exact(heaps.iter().map(measure).max().unwrap_or(0) as usize);
    report.push(("heap-peak".to_string(), most(|heap| heap.peak)));
    report.push(("allocations".to_string(), most(|heap| heap.allocations)));
    report
}

/// Prove the leaf once at `leaf_prover`'s rate, then one first-level node over copies of its
/// proof and one node over copies of that at `prover`'s, each reported as `proved` reports a case: its stages are the children of a
/// `Prove` span around it, its verifying time is as a root, and its peak memory is the
/// process's so far, the node's including the first-level node's. A signer-set tree's nodes
/// declare the union of their children's sets, and are verified by it.
fn proved_tree(
    tree: &Aggregation,
    leaf_prover: &Prover,
    prover: &Prover,
    plan: Plan,
) -> Vec<(String, Vec<(String, Metric)>)> {
    eprintln!("{}", tree.name);
    let ProvenRun { proof, output, .. } = tree.leaf.prove(leaf_prover);
    let built = tree.tree(LeafShape::of(&proof).expect("an honest announcement"), prover.rate());
    // The leaf's stages.
    bench::take_stages();
    let leaf = Leaf::new(&proof, output);
    let (first_report, node_report) = match tree.signers {
        None => {
            let leaves = vec![leaf; tree.arity_0];
            let outputs = vec![output; tree.arity_0];
            let (first, first_report) = proved_node(plan, || built.prove_first(&leaves), |p| built.verify(p, &outputs));
            let children = vec![first; tree.arity];
            let outputs = vec![output; tree.arity_0 * tree.arity];
            let (_, node_report) = proved_node(plan, || built.prove_node(&children), |p| built.verify(p, &outputs));
            (first_report, node_report)
        }
        Some(_) => {
            let set = tree
                .leaf
                .claims
                .as_ref()
                .expect("a signer-set tree's leaf publishes its claims");
            let leaves = vec![ClaimLeaf::new(leaf, set); tree.arity_0];
            let verify = |a: &Aggregate| built.verify_claims(&a.proof, &a.claims);
            let (first, first_report) = proved_node(plan, || built.aggregate_leaves(&leaves, None), verify);
            let children = vec![&first; tree.arity];
            let (_, node_report) = proved_node(plan, || built.aggregate(&children, None), verify);
            (first_report, node_report)
        }
    };
    vec![
        (tree.node(NodeCircuit::First).0, first_report),
        (tree.node(NodeCircuit::Node(tree.arity)).0, node_report),
    ]
}

/// A tree proof, alone or with the signer set it declares.
trait NodeProof {
    fn tree_proof(&self) -> &TreeProof;
}

impl NodeProof for TreeProof {
    fn tree_proof(&self) -> &TreeProof {
        self
    }
}

impl NodeProof for Aggregate {
    fn tree_proof(&self) -> &TreeProof {
        &self.proof
    }
}

/// One node's proof and its measures, verified as a root by `verify`.
fn proved_node<P: NodeProof>(
    plan: Plan,
    prove: impl Fn() -> Result<P, TreeError>,
    verify: impl Fn(&P) -> Result<(), TreeError>,
) -> (P, Vec<(String, Metric)>) {
    let mut passes = Vec::new();
    let mut heaps = Vec::new();
    let (proof, time) = plan.warm_then_measure(|| {
        let (proof, heap) = bench::measure_heap(|| tracing::info_span!("Prove").in_scope(&prove));
        passes.push(bench::take_stages());
        heaps.push(heap);
        proof.expect("honest children")
    });
    let peak_memory = bench::peak_rss_bytes();
    let (verified, verify_time) = Plan::new(VERIFY_PASSES, Duration::ZERO).measure_quiet(|| verify(&proof));
    verified.expect("an honest tree proof verifies");
    let report = measures(
        &time,
        proof.tree_proof().to_bytes().len(),
        &verify_time,
        &passes[1..],
        peak_memory,
        &heaps[1..],
    );
    (proof, report)
}

/// One `stage.<name>` measure per stage, in the order the stages ran, over the measured
/// passes: a stage's name lowercased, every character but a letter or a digit made a `-`.
fn stages(passes: &[Vec<Stage>]) -> Vec<(String, Metric)> {
    let mut names: Vec<&'static str> = Vec::new();
    for stage in passes.iter().flatten() {
        if !names.contains(&stage.name) {
            names.push(stage.name);
        }
    }
    names
        .into_iter()
        .map(|name| {
            let mut timing = Timing::default();
            for pass in passes {
                timing.push(
                    pass.iter()
                        .filter(|stage| stage.name == name)
                        .map(|stage| stage.elapsed.as_secs_f64())
                        .sum(),
                );
            }
            let measure: String = name
                .chars()
                .map(|c| {
                    if c.is_ascii_alphanumeric() {
                        c.to_ascii_lowercase()
                    } else {
                        '-'
                    }
                })
                .collect();
            (format!("stage.{measure}"), Metric::nanoseconds(&timing))
        })
        .collect()
}

/// The counts as a markdown table, with the rows per table: what CI puts in each run's summary.
fn table(counted: &[(Case, Stats)]) -> String {
    let mut table =
        String::from("| program | RISC-V cycles | per item | committed words | tables |\n|---|---:|---:|---:|---|\n");
    for (case, stats) in counted {
        let cycles = stats.cycles();
        let Items { count, name } = case.items();
        writeln!(
            table,
            "| {} | {} | {} / {name} | 2^{:.2} | {} |",
            case.workload.title,
            pretty_integer(&cycles),
            pretty_integer(&(cycles / count)),
            (stats.committed as f64).log2(),
            stats.details()
        )
        .unwrap();
    }
    table
}

/// Each tree's circuits as a markdown table, with the rows per table and their heights.
fn tree_table(trees: &[(Aggregation, Vec<(NodeCircuit, CircuitStats)>)]) -> String {
    let mut table = String::from(
        "\n| recursion circuit | rows | proven rows | committed words | tables |\n|---|---:|---:|---:|---|\n",
    );
    for (tree, circuits) in trees {
        for (circuit, stats) in circuits {
            let (rows, proven) = circuit_rows(stats);
            let tables: Vec<String> = (stats.tables.iter())
                .map(|t| format!("{} {} (2^{})", t.name, pretty_integer(&t.rows), t.height_log))
                .collect();
            writeln!(
                table,
                "| {} | {} | {} | 2^{:.2} | {} |",
                tree.node(*circuit).1,
                pretty_integer(&rows),
                pretty_integer(&proven),
                (stats.committed as f64).log2(),
                tables.join("  ")
            )
            .unwrap();
        }
    }
    table
}
