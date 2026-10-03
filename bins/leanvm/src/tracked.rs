//! The programs tracked in CI (`.github/workflows/bench.yml`), reported as Bencher Metric
//! Format JSON or, counted without a proof, as a markdown table.
//!
//! Two lists. The counts are exact and cheap, so they are taken at the README's sizes, on
//! one testbed: they are the same on every machine. Proving on CI's GitHub-hosted runners
//! (16 GB) takes the sizes that fit them (leanXMSS and leanSPHINCS at a quarter, and no
//! leanDA, whose one blob is its smallest run) and reports only the proving time, the one
//! measure that differs between machines. A case's name is its Bencher history, so renaming
//! one or changing its input starts a new one.

use bench::{Metric, Plan, bencher_json};
use leanvm::{Program, Proved, Prover, Rate, Stats, verify};
use primitives::pretty_integer;

use crate::fibonacci::fibonacci_program;
use crate::guest::refuse;
use crate::workload::{self, Workload};

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
        let mut public = leanvm_guest::PublicValues::new();
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
        Case::workload("leanxmss-451", workload::leanxmss(451)),
        Case::workload("leansphincs-104", workload::leansphincs(104)),
        Case::workload("leanda-1", workload::leanda(1)),
    ]
}

/// Proven: the sizes that fit a GitHub-hosted runner.
fn proven() -> Vec<Case> {
    vec![
        Case::fibonacci("fibonacci-asm-2000000", 2_000_000),
        Case::hash("hash-50000", 50_000),
        Case::workload("leanxmss-112", workload::leanxmss(112)),
        Case::workload("leansphincs-26", workload::leansphincs(26)),
    ]
}

/// With `cycles_only`, count every case without a proof, as JSON or with `markdown` as a
/// table; otherwise prove, verify and time the proven cases, as JSON.
pub fn run(cycles_only: bool, markdown: bool, prover: &Prover, rate: Rate, plan: Plan) {
    if markdown {
        return table(&counted());
    }
    let report: Vec<_> = if cycles_only {
        counted()
            .iter()
            .map(|case| (case.name.to_string(), counts(&case.measure())))
            .collect()
    } else {
        proven()
            .iter()
            .map(|case| (case.name.to_string(), proved(case, prover, rate, plan)))
            .collect()
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

/// The proving time, after checking the proof: the output is the native reference's and it
/// verifies.
fn proved(case: &Case, prover: &Prover, rate: Rate, plan: Plan) -> Vec<(&'static str, Metric)> {
    eprintln!("{}", case.name);
    let (Proved { proof, output, .. }, time) = plan.warm_then_measure(|_| {
        prover
            .prove(&case.program, &case.advice, rate)
            .unwrap_or_else(|e| refuse(format_args!("{}: {e}", case.name)))
    });
    assert_eq!(
        output, case.expected,
        "{}: the output is the native reference's",
        case.name
    );
    verify(&case.program, &output, &proof).expect("an honest proof verifies");
    vec![("latency", Metric::nanoseconds(&time))]
}

/// The counts as a markdown table, with the rows per table: what CI puts in each run's summary.
fn table(cases: &[Case]) {
    println!("| program | RISC-V cycles | per item | committed words | tables |");
    println!("|---|---:|---:|---:|---|");
    for case in cases {
        let stats = case.measure();
        let cycles: usize = stats.base_counts.iter().sum();
        println!(
            "| {} | {} | {} / {} | 2^{:.2} | {} |",
            case.title,
            pretty_integer(&cycles),
            pretty_integer(&(cycles / case.items)),
            case.item,
            (stats.committed as f64).log2(),
            stats.details()
        );
    }
}
