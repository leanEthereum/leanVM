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
//! kind proven over copies of one leaf proof.

use crate::refuse;
use crate::workload::{Items, Workload};
use bench::{Heap, Metric, Plan, Timing, bencher_json};
use leanvm::aggregate::{CircuitStats, Kind, Leaf, LeafShape, Leaves, Subtree, Tree, TreeError, TreeProof, TreeShape};
use leanvm::{ProvenRun, Prover, Rate, Stats};
#[cfg(feature = "circuits")]
use leanvm::{SphincsBatch, XmssBatch};
use primitives::pretty_integer;
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
const THREADS: [(&str, usize); 15] = [
    ("fibonacci-asm-2000000-16thread", 16),
    ("hash-50000-16thread", 16),
    ("leanxmss-100-16thread", 16),
    ("leansphincs-26-16thread", 16),
    ("aggregate-leanxmss-100-2to1-16thread", 16),
    ("aggregate-leanxmss-100-4to1-16thread", 16),
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

/// An aggregation tree over copies of one case's proof: first-level nodes of `arity_0` leaves,
/// nodes of `arity` tree proofs. A tree's name ends `<N>to1` when both are `N`: every node
/// combines `N` proofs into 1; then `-<T>thread` when it is proven on `T` threads (`THREADS`).
struct Aggregation {
    name: &'static str,
    leaf: Workload,
    arity_0: usize,
    arity: usize,
}

impl Aggregation {
    const fn new(name: &'static str, leaf: Workload, arity_0: usize, arity: usize) -> Self {
        Self {
            name,
            leaf,
            arity_0,
            arity,
        }
    }

    /// The tree over the leaf's proofs shaped `shape`, every tree proof at `rate`.
    fn tree(&self, shape: LeafShape, rate: Rate) -> Tree<'_> {
        let leaves = Leaves::Runs {
            program: &self.leaf.program,
            shape,
        };
        let shape = TreeShape {
            arity_0: self.arity_0,
            arity: self.arity,
            rate,
        };
        Tree::new(&[leaves], shape).unwrap_or_else(|e| refuse(format_args!("{}: {e}", self.name)))
    }

    /// A kind of node's benchmark name, and what the markdown table calls it: `<name>-first`, a
    /// first-level node (the RISC-V verifier in rows over `arity_0` leaf proofs), and
    /// `<name>-node`, a higher node (the recursion verifier in rows over `arity` child proofs).
    fn node(&self, kind: Kind) -> (String, String) {
        match kind {
            Kind::First(_) => (
                format!("{}-first", self.name),
                format!("first-level node over {} x {}", self.arity_0, self.leaf.title),
            ),
            Kind::Node => (
                format!("{}-node", self.name),
                format!(
                    "node over {} tree proofs, first level {} x {}",
                    self.arity, self.arity_0, self.leaf.title
                ),
            ),
        }
    }
}

/// Aggregation trees counted without a proof: the README's leaves, 2 to 1 (`cargo leanvm
/// aggregate`'s shape) and 4 to 1.
fn counted_trees() -> Vec<Aggregation> {
    let leaf = || Workload::leanxmss(400);
    vec![
        Aggregation::new("aggregate-leanxmss-400-2to1", leaf(), 2, 2),
        Aggregation::new("aggregate-leanxmss-400-4to1", leaf(), 4, 4),
    ]
}

/// Builds an aggregation tree given its name.
type BuildTree = fn(&'static str) -> Aggregation;

/// Aggregation trees proven: the counted trees' arities over leaves of a size proven above, and
/// both trees on 16 total threads and on the legacy 1, 4 and 8 performance workers. Each gives two benchmarks, `<name>-first` and
/// `<name>-node`.
fn proven_trees() -> [(&'static str, BuildTree); 8] {
    [
        ("aggregate-leanxmss-100-2to1-16thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 2, 2)
        }),
        ("aggregate-leanxmss-100-4to1-16thread", |name| {
            Aggregation::new(name, Workload::leanxmss(100), 4, 4)
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

/// Each kind of node's circuit, without a proof: the leaf's run, measured, gives the shape its
/// proofs announce at `leaf_rate`; the tree's proofs are at `rate`.
fn circuits(tree: &Aggregation, leaf_rate: Rate, rate: Rate) -> [(Kind, CircuitStats); 2] {
    let shape = LeafShape::measured(&tree.leaf.measure(), leaf_rate);
    let built = tree.tree(shape, rate);
    [Kind::First(0), Kind::Node].map(|kind| (kind, built.stats(kind)))
}

/// The leanXMSS batch sizes whose recursion circuits `dump` writes: the smallest, and the benchmark's.
#[cfg(feature = "circuits")]
const XMSS_DUMPS: [usize; 4] = [1, 2, 3, 400];

/// The leanSPHINCS batch sizes whose recursion circuits `dump` writes: the smallest, and the benchmark's.
#[cfg(feature = "circuits")]
const SPHINCS_DUMPS: [usize; 4] = [1, 2, 3, 104];

/// Write each tracked tree's two circuits, as `Tree::circuit_dump` gives them, to `<out>/<name>-first.txt` and `<out>/<name>-node.txt`: the counted trees and the proven trees' leaf size at both arities. Then the leanXMSS batch circuits of `XMSS_DUMPS` signatures, as `XmssBatch::circuit_dump` gives them, to `<out>/xmss-<n>.txt`, and the leanSPHINCS ones of `SPHINCS_DUMPS`, as `SphincsBatch::circuit_dump` gives them, to `<out>/sphincs-<n>.txt`.
///
/// CI's `rec-builder-model` workflow has the Lean model of the builder replay each and check it builds the same circuit, and `checkxmss` checks each leanXMSS and leanSPHINCS circuit is the one `LeanVMCircuits.Xmss.Circuit` or `LeanVMCircuits.Sphincs.Circuit` authors.
#[cfg(feature = "circuits")]
pub fn dump(out: &Path, leaf_rate: Rate, rate: Rate) {
    let proven = [
        Aggregation::new("aggregate-leanxmss-100-2to1", Workload::leanxmss(100), 2, 2),
        Aggregation::new("aggregate-leanxmss-100-4to1", Workload::leanxmss(100), 4, 4),
    ];
    std::fs::create_dir_all(out).unwrap_or_else(|e| refuse(format_args!("{}: {e}", out.display())));
    for tree in counted_trees().into_iter().chain(proven) {
        let shape = LeafShape::measured(&tree.leaf.measure(), leaf_rate);
        let built = tree.tree(shape, rate);
        for kind in built.kinds() {
            let path = out.join(format!("{}.txt", tree.node(kind).0));
            std::fs::write(&path, built.circuit_dump(kind))
                .unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
        }
    }
    for n in XMSS_DUMPS {
        let batch = XmssBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}")));
        let path = out.join(format!("xmss-{n}.txt"));
        std::fs::write(&path, batch.circuit_dump()).unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
    }
    for n in SPHINCS_DUMPS {
        let batch = SphincsBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}")));
        let path = out.join(format!("sphincs-{n}.txt"));
        std::fs::write(&path, batch.circuit_dump()).unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
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
    let (ProvenRun { proof, output, .. }, time) = plan.warm_then_measure(|_| {
        let (proved, heap) = bench::measure_heap(|| workload.prove(prover));
        passes.push(bench::take_stages());
        heaps.push(heap);
        proved
    });
    let peak_memory = bench::peak_rss_bytes();
    let (verified, verify_time) =
        Plan::new(VERIFY_PASSES, 0).measure_quiet(|_| workload.program.verify(output, &proof));
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
    passes: &[Vec<(&'static str, Duration)>],
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
/// process's so far, the node's including the first-level node's.
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
    let leaves = vec![Leaf::new(&proof, output); tree.arity_0];
    let first_level = Subtree::First(vec![output.into(); tree.arity_0]);
    let (first, first_report) = proved_node(&built, &first_level, plan, || built.prove_first(&leaves));
    let children = vec![first; tree.arity];
    let node_level = Subtree::Node(vec![first_level; tree.arity]);
    let (_, node_report) = proved_node(&built, &node_level, plan, || built.prove_node(&children));
    vec![
        (tree.node(Kind::First(0)).0, first_report),
        (tree.node(Kind::Node).0, node_report),
    ]
}

/// One node's proof and its measures.
fn proved_node(
    tree: &Tree<'_>,
    expected: &Subtree,
    plan: Plan,
    prove: impl Fn() -> Result<TreeProof, TreeError>,
) -> (TreeProof, Vec<(String, Metric)>) {
    let mut passes = Vec::new();
    let mut heaps = Vec::new();
    let (proof, time) = plan.warm_then_measure(|_| {
        let (proof, heap) = bench::measure_heap(|| tracing::info_span!("Prove").in_scope(&prove));
        passes.push(bench::take_stages());
        heaps.push(heap);
        proof.expect("honest children")
    });
    let peak_memory = bench::peak_rss_bytes();
    let (verified, verify_time) = Plan::new(VERIFY_PASSES, 0).measure_quiet(|_| tree.verify(&proof, expected));
    verified.expect("an honest tree proof verifies");
    let report = measures(
        &time,
        proof.to_bytes().len(),
        &verify_time,
        &passes[1..],
        peak_memory,
        &heaps[1..],
    );
    (proof, report)
}

/// One `stage.<name>` measure per stage, in the order the stages ran, over the measured
/// passes: a stage's name lowercased, every character but a letter or a digit made a `-`.
fn stages(passes: &[Vec<(&'static str, Duration)>]) -> Vec<(String, Metric)> {
    let mut names: Vec<&'static str> = Vec::new();
    for &(name, _) in passes.iter().flatten() {
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
        .into_iter()
        .map(|name| {
            let mut timing = Timing::default();
            for pass in passes {
                timing.push(
                    pass.iter()
                        .filter(|(n, _)| *n == name)
                        .map(|(_, d)| d.as_secs_f64())
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
fn tree_table(trees: &[(Aggregation, [(Kind, CircuitStats); 2])]) -> String {
    let mut table = String::from(
        "\n| recursion circuit | rows | proven rows | committed words | tables |\n|---|---:|---:|---:|---|\n",
    );
    for (tree, circuits) in trees {
        for (kind, stats) in circuits {
            let (rows, proven) = circuit_rows(stats);
            let tables: Vec<String> = (stats.tables.iter())
                .map(|t| format!("{} {} (2^{})", t.name, pretty_integer(&t.rows), t.height_log))
                .collect();
            writeln!(
                table,
                "| {} | {} | {} | 2^{:.2} | {} |",
                tree.node(*kind).1,
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
