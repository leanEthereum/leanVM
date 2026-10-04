//! The programs tracked in CI, reported as Bencher Metric Format JSON or, counted without a
//! proof, as a markdown table, or both from one pass.
//!
//! Two lists. The counts are exact and cheap, so they are taken at the README's sizes, the
//! most one proof holds, on one runner (`.github/workflows/counts.yml`), which compares a
//! PR's with its base's: they are the same on every machine. Proving on CI's GitHub-hosted
//! runners (16 GB, `.github/workflows/bench.yml`) takes the sizes that fit them (leanXMSS and
//! leanSPHINCS at a quarter, and no leanDA, whose one blob is its smallest run), and a PR's
//! base and head are proven in turns on one runner and compared there. A case's name is what
//! a PR's results are matched by, so renaming one or changing its input shows it as new.
//!
//! An aggregation tree is tracked the same way: each kind of node's circuit counted without a
//! proof (the leaf's run measured gives the shape its proofs announce), and one node of each
//! kind proven over copies of one leaf proof.

use crate::fibonacci::fibonacci_program;
use crate::guest::refuse;
use crate::workload;
use crate::workload::Workload;
use bench::{Metric, Plan, Timing, bencher_json};
use leanvm::aggregate::{CircuitStats, Kind, Leaf, LeafShape, Tree, TreeError, TreeProof, TreeShape};
use leanvm::{Output, Program, ProvenRun, Prover, Rate, Stats};
use leanvm_guest::PublicValues;
use primitives::pretty_integer;
use std::fmt::Write as _;
use std::fs::OpenOptions;
use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

struct Case {
    name: &'static str,
    /// What the markdown table calls it.
    title: String,
    program: Program,
    advice: Vec<u64>,
    /// The output the native reference computed.
    expected: [u64; 4],
    items: usize,
    item: &'static str,
}

impl Case {
    fn workload(name: &'static str, workload: Workload) -> Self {
        Self {
            name,
            program: workload.program(),
            title: workload.title,
            advice: workload.advice,
            expected: workload.expected,
            items: workload.items,
            item: workload.item,
        }
    }

    /// Fibonacci modulo 2^64 in hand-written RISC-V, `n` steps.
    fn fibonacci(name: &'static str, n: usize) -> Self {
        let (program, expected) = fibonacci_program(n);
        Self {
            name,
            title: format!("Fibonacci modulo 2^64, {} steps", pretty_integer(&n)),
            program,
            advice: vec![],
            expected,
            items: n,
            item: "step",
        }
    }

    /// The `hash` guest: BLAKE2s of the bytes `0, 1, 2, ...` (mod 251) through the precompile.
    fn hash(name: &'static str, length: usize) -> Self {
        let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
        let digest = primitives::hash::hash(&message);
        let digest: [u64; 4] =
            std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
        // What the guest commits: the length, then the digest.
        let mut public = PublicValues::new();
        public.commit(&(length as u64)).commit(&digest);
        Self::workload(
            name,
            Workload {
                title: format!("BLAKE2s of {} bytes", pretty_integer(&length)),
                elf: include_bytes!("../../../programs/hash/hash.elf"),
                advice: vec![length as u64],
                expected: public.digest(),
                items: length,
                item: "byte",
            },
        )
    }

    /// The run's exact counts, without a proof.
    fn measure(&self) -> Stats {
        self.program
            .measure(&self.advice)
            .unwrap_or_else(|e| refuse(format_args!("{}: {e}", self.name)))
    }
}

/// Counted without a proof: the README's sizes.
fn counted() -> Vec<Case> {
    vec![
        Case::fibonacci("fibonacci-asm-2000000", 2_000_000),
        Case::hash("hash-50000", 50_000),
        Case::workload("leanxmss-400", workload::leanxmss(400)),
        Case::workload("leansphincs-104", workload::leansphincs(104)),
        Case::workload("leanda-1", workload::leanda(1)),
    ]
}

/// Builds a case given its name.
type Build = fn(&'static str) -> Case;

/// Proven: the sizes that fit a GitHub-hosted runner, each built only if it is proven.
fn proven() -> [(&'static str, Build); 4] {
    [
        ("fibonacci-asm-2000000", |name| Case::fibonacci(name, 2_000_000)),
        ("hash-50000", |name| Case::hash(name, 50_000)),
        ("leanxmss-100", |name| Case::workload(name, workload::leanxmss(100))),
        ("leansphincs-26", |name| Case::workload(name, workload::leansphincs(26))),
    ]
}

/// An aggregation tree over copies of one case's proof: first-level nodes of `arity_0` leaves,
/// nodes of `arity` tree proofs. A tree's name ends `<N>to1` when both are `N`: every node
/// combines `N` proofs into 1.
struct Aggregation {
    name: &'static str,
    leaf: Case,
    arity_0: usize,
    arity: usize,
}

impl Aggregation {
    const fn new(name: &'static str, leaf: Case, arity_0: usize, arity: usize) -> Self {
        Self {
            name,
            leaf,
            arity_0,
            arity,
        }
    }

    /// The tree over the leaf's proofs shaped `shape`, every tree proof at `rate`.
    fn tree(&self, shape: LeafShape, rate: Rate) -> Tree<'_> {
        let shape = TreeShape {
            leaf: shape,
            arity_0: self.arity_0,
            arity: self.arity,
            rate,
        };
        Tree::new(&self.leaf.program, shape).unwrap_or_else(|e| refuse(format_args!("{}: {e}", self.name)))
    }

    /// A kind of node's benchmark name, and what the markdown table calls it: `<name>-first`, a
    /// first-level node (the RISC-V verifier in rows over `arity_0` leaf proofs), and
    /// `<name>-node`, a higher node (the recursion verifier in rows over `arity` child proofs).
    fn node(&self, kind: Kind) -> (String, String) {
        match kind {
            Kind::First => (
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
    let leaf = || Case::workload("leanxmss-400", workload::leanxmss(400));
    vec![
        Aggregation::new("aggregate-leanxmss-400-2to1", leaf(), 2, 2),
        Aggregation::new("aggregate-leanxmss-400-4to1", leaf(), 4, 4),
    ]
}

/// Builds an aggregation tree given its name.
type BuildTree = fn(&'static str) -> Aggregation;

/// Aggregation trees proven: the counted trees' arities over leaves of a size proven above.
/// Each gives two benchmarks, `<name>-first` and `<name>-node`.
fn proven_trees() -> [(&'static str, BuildTree); 2] {
    [
        ("aggregate-leanxmss-100-2to1", |name| {
            Aggregation::new(name, Case::workload("leanxmss-100", workload::leanxmss(100)), 2, 2)
        }),
        ("aggregate-leanxmss-100-4to1", |name| {
            Aggregation::new(name, Case::workload("leanxmss-100", workload::leanxmss(100)), 4, 4)
        }),
    ]
}

/// With `cycles_only`, count every case without a proof and print the counts as JSON, or with
/// `markdown` as a table, or as JSON with the table appended to `markdown_file`; otherwise
/// prove, verify and time the proven cases, or only the one named `only`, as JSON (one case
/// per process makes its `peak-memory` that case's alone).
pub fn run(
    cycles_only: bool,
    markdown: bool,
    markdown_file: Option<&Path>,
    only: Option<&str>,
    prover: &Prover,
    plan: Plan,
) {
    let report: Vec<_> = if cycles_only {
        let counted: Vec<_> = counted()
            .into_iter()
            .map(|case| {
                let stats = case.measure();
                (case, stats)
            })
            .collect();
        let trees: Vec<_> = counted_trees()
            .into_iter()
            .map(|tree| {
                let circuits = circuits(&tree, prover.rate());
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
        let cases: Vec<_> = proven()
            .into_iter()
            .filter(|(name, _)| only.is_none_or(|only| only == *name))
            .collect();
        let trees: Vec<_> = proven_trees()
            .into_iter()
            .filter(|(name, _)| only.is_none_or(|only| only == *name))
            .collect();
        if cases.is_empty() && trees.is_empty() {
            refuse(format_args!("no tracked case is named {}", only.unwrap_or_default()));
        }
        bench::time_stages("Prove");
        let mut report: Vec<_> = cases
            .into_iter()
            .map(|(name, case)| (name.to_string(), proved(&case(name), prover, plan)))
            .collect();
        for (name, tree) in trees {
            report.extend(proved_tree(&tree(name), prover, plan));
        }
        return println!("{}", bencher_json(&report));
    };
    println!("{}", bencher_json(&report));
}

/// `cycles` (the program's own instructions), `proven-rows` (the tables' heights once
/// padded to powers of two) and `committed` (the witness words): exact, the same on every
/// machine.
fn counts(stats: &Stats) -> Vec<(&'static str, Metric)> {
    vec![
        ("cycles", Metric::exact(stats.base_counts.iter().sum())),
        ("proven-rows", Metric::exact(stats.cycles)),
        ("committed", Metric::exact(stats.committed)),
    ]
}

/// Each kind of node's circuit, without a proof: the leaf's run, measured, gives the shape its
/// proofs announce.
fn circuits(tree: &Aggregation, rate: Rate) -> [(Kind, CircuitStats); 2] {
    let shape = LeafShape::measured(&tree.leaf.measure(), rate);
    let built = tree.tree(shape, rate);
    Kind::ALL.map(|kind| (kind, built.stats(kind)))
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
/// stages (the `Prove` span's direct children, `--tracing`'s top level) and the process's peak
/// resident memory so far.
fn proved(case: &Case, prover: &Prover, plan: Plan) -> Vec<(String, Metric)> {
    eprintln!("{}", case.name);
    let mut passes = Vec::new();
    let (ProvenRun { proof, output, .. }, time) = plan.warm_then_measure(|_| {
        let proved = prover
            .prove(&case.program, &case.advice)
            .unwrap_or_else(|e| refuse(format_args!("{}: {e}", case.name)));
        passes.push(bench::take_stages());
        proved
    });
    let peak_memory = bench::peak_rss_bytes();
    assert_eq!(
        output, case.expected,
        "{}: the output is the native reference's",
        case.name
    );
    let (verified, verify_time) = Plan::new(VERIFY_PASSES, 0).measure_quiet(|_| case.program.verify(output, &proof));
    verified.expect("an honest proof verifies");
    measures(&time, proof.to_bytes().len(), &verify_time, &passes[1..], peak_memory)
}

/// A proven case's measures: its proving time, proof size and verifying time, each of its
/// stages over the measured passes, and the peak memory.
fn measures(
    time: &Timing,
    proof_size: usize,
    verify_time: &Timing,
    passes: &[Vec<(&'static str, Duration)>],
    peak_memory: u64,
) -> Vec<(String, Metric)> {
    let mut report = vec![
        ("latency".to_string(), Metric::nanoseconds(time)),
        ("proof-size".to_string(), Metric::exact(proof_size)),
        ("verify".to_string(), Metric::nanoseconds(verify_time)),
    ];
    report.extend(stages(passes));
    report.push(("peak-memory".to_string(), Metric::exact(peak_memory as usize)));
    report
}

/// Prove the leaf once, then one first-level node over copies of its proof and one node over
/// copies of that, each reported as `proved` reports a case: its stages are the children of a
/// `Prove` span around it, its verifying time is as a root, and its peak memory is the
/// process's so far, the node's including the first-level node's.
fn proved_tree(tree: &Aggregation, prover: &Prover, plan: Plan) -> Vec<(String, Vec<(String, Metric)>)> {
    eprintln!("{}", tree.name);
    let leaf = &tree.leaf;
    let ProvenRun { proof, output, .. } = prover
        .prove(&leaf.program, &leaf.advice)
        .unwrap_or_else(|e| refuse(format_args!("{}: {e}", leaf.name)));
    assert_eq!(
        output, leaf.expected,
        "{}: the output is the native reference's",
        leaf.name
    );
    let built = tree.tree(LeafShape::of(&proof).expect("an honest announcement"), prover.rate());
    // The leaf's stages.
    bench::take_stages();
    let leaves = vec![Leaf::new(&proof, output); tree.arity_0];
    let outputs = vec![output; tree.arity_0];
    let (first, first_report) = proved_node(&built, &outputs, plan, || built.prove_first(&leaves));
    let children = vec![first; tree.arity];
    let outputs = vec![output; tree.arity_0 * tree.arity];
    let (_, node_report) = proved_node(&built, &outputs, plan, || built.prove_node(&children));
    vec![
        (tree.node(Kind::First).0, first_report),
        (tree.node(Kind::Node).0, node_report),
    ]
}

/// One node's proof and its measures.
fn proved_node(
    tree: &Tree<'_>,
    outputs: &[Output],
    plan: Plan,
    prove: impl Fn() -> Result<TreeProof, TreeError>,
) -> (TreeProof, Vec<(String, Metric)>) {
    let mut passes = Vec::new();
    let (proof, time) = plan.warm_then_measure(|_| {
        let proof = (tracing::info_span!("Prove").in_scope(&prove)).expect("honest children");
        passes.push(bench::take_stages());
        proof
    });
    let peak_memory = bench::peak_rss_bytes();
    let (verified, verify_time) = Plan::new(VERIFY_PASSES, 0).measure_quiet(|_| tree.verify(&proof, outputs));
    verified.expect("an honest tree proof verifies");
    let report = measures(&time, proof.to_bytes().len(), &verify_time, &passes[1..], peak_memory);
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
        let cycles: usize = stats.base_counts.iter().sum();
        writeln!(
            table,
            "| {} | {} | {} / {} | 2^{:.2} | {} |",
            case.title,
            pretty_integer(&cycles),
            pretty_integer(&(cycles / case.items)),
            case.item,
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
