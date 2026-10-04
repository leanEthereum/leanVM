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

use crate::fibonacci::fibonacci_program;
use crate::guest::refuse;
use crate::workload;
use crate::workload::Workload;
use bench::{Metric, Plan, Timing, bencher_json};
use leanvm::{Program, Proved, Prover, Rate, Stats, verify};
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
        leanvm::measure(&self.program, &self.advice).unwrap_or_else(|e| refuse(format_args!("{}: {e}", self.name)))
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
    rate: Rate,
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
        if markdown {
            return print!("{}", table(&counted));
        }
        if let Some(path) = markdown_file {
            OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .and_then(|mut file| file.write_all(table(&counted).as_bytes()))
                .unwrap_or_else(|e| refuse(format_args!("{}: {e}", path.display())));
        }
        counted
            .iter()
            .map(|(case, stats)| (case.name.to_string(), counts(stats)))
            .collect()
    } else {
        let cases: Vec<_> = proven()
            .into_iter()
            .filter(|(name, _)| only.is_none_or(|only| only == *name))
            .collect();
        if cases.is_empty() {
            refuse(format_args!("no tracked case is named {}", only.unwrap_or_default()));
        }
        bench::time_stages("Prove");
        let report: Vec<_> = cases
            .into_iter()
            .map(|(name, case)| (name.to_string(), proved(&case(name), prover, rate, plan)))
            .collect();
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

/// A verification takes milliseconds, so one pass says little about it.
const VERIFY_PASSES: usize = 20;

/// The proving time, the proof's size and the verifying time, after checking the proof: the
/// output is the native reference's and it verifies. Then the time of each of the proof's
/// stages (the `Prove` span's direct children, `--tracing`'s top level) and the process's peak
/// resident memory so far.
fn proved(case: &Case, prover: &Prover, rate: Rate, plan: Plan) -> Vec<(String, Metric)> {
    eprintln!("{}", case.name);
    let mut passes = Vec::new();
    let (Proved { proof, output, .. }, time) = plan.warm_then_measure(|_| {
        let proved = prover
            .prove(&case.program, &case.advice, rate)
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
    let (verified, verify_time) = Plan::new(VERIFY_PASSES, 0).measure_quiet(|_| verify(&case.program, &output, &proof));
    verified.expect("an honest proof verifies");
    let mut report = vec![
        ("latency".to_string(), Metric::nanoseconds(&time)),
        ("proof-size".to_string(), Metric::exact(proof.to_bytes().len())),
        ("verify".to_string(), Metric::nanoseconds(&verify_time)),
    ];
    report.extend(stages(&passes[1..]));
    report.push(("peak-memory".to_string(), Metric::exact(peak_memory as usize)));
    report
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
