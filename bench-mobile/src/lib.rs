//! Fixed mobile workloads, timed by mobench without a nested benchmark harness.

use leanvm::aggregate::{Leaf, LeafShape, Leaves, Subtree, Tree, TreeShape};
use leanvm::{Output, Program, ProvenRun, Prover, Rate};
use mobench_sdk::registry::BenchFunction;
use mobench_sdk::timing::{BenchReport, BenchSpec, TimingError};
use std::cell::RefCell;
use std::fmt::Display;
use std::hint::black_box;
use std::num::NonZeroUsize;
use std::sync::OnceLock;

pub const SPENDS_PER_LEAF: usize = 2;
pub const LEAF_LOG_INV_RATE: u8 = 2;
pub const AGGREGATION_LEAVES: usize = 2;
pub const AGGREGATION_LOG_INV_RATE: u8 = 1;
pub const DEFAULT_WARMUP: u32 = 1;
pub const DEFAULT_ITERATIONS: u32 = 3;
pub const PROVE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_prove";
pub const AGGREGATE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_aggregate";
pub const FALCON_BENCHMARK: &str = "leanvm_mobile_bench::falcon_prove";
pub const STATEPROOF_BENCHMARK: &str = "leanvm_mobile_bench::stateproof_prove";
pub const SIGNATURES: usize = 1;
pub const ACCOUNTS: usize = 1;
pub const STORAGE_SLOTS: usize = 1;
pub const STANDALONE_LOG_INV_RATE: u8 = 2;

static AVAILABLE_THREADS: OnceLock<std::io::Result<NonZeroUsize>> = OnceLock::new();

inventory::submit! {
    BenchFunction { name: PROVE_BENCHMARK, runner: shielded_prove }
}

inventory::submit! {
    BenchFunction { name: AGGREGATE_BENCHMARK, runner: shielded_aggregate }
}

inventory::submit! {
    BenchFunction { name: FALCON_BENCHMARK, runner: falcon_prove }
}

inventory::submit! {
    BenchFunction { name: STATEPROOF_BENCHMARK, runner: stateproof_prove }
}

mobench_sdk::export_native_c_abi!();

struct Standalone {
    name: &'static str,
    program: Program,
    advice: Vec<u64>,
    expected: Output,
    prover: Prover,
}

impl Standalone {
    fn new(
        name: &'static str,
        elf: &[u8],
        advice: Vec<u64>,
        expected: Output,
        log_inv_rate: u8,
    ) -> Result<Self, TimingError> {
        Ok(Self {
            name,
            program: Program::from_elf(elf).map_err(execution_error)?,
            advice,
            expected,
            prover: Prover::new(Rate::new(log_inv_rate).map_err(execution_error)?),
        })
    }

    fn prove(&self) -> Result<ProvenRun, TimingError> {
        self.prover.prove(&self.program, &self.advice).map_err(execution_error)
    }

    fn verify(&self, run: &ProvenRun) -> Result<(), TimingError> {
        if run.output != self.expected {
            return Err(TimingError::Execution(format!(
                "{} output {} differs from native reference {}",
                self.name, run.output, self.expected
            )));
        }
        self.program.verify(self.expected, &run.proof).map_err(execution_error)
    }

    fn run(&self, spec: BenchSpec) -> Result<BenchReport, TimingError> {
        let count = spec.warmup as usize + spec.iterations as usize;
        let mut verified: Result<(), TimingError> = Ok(());
        let report = mobench_sdk::timing::run_closure_with_setup_teardown(
            spec,
            || RefCell::new(Vec::with_capacity(count)),
            |proofs| {
                let run = self.prove()?;
                proofs.borrow_mut().push(black_box(run));
                Ok(())
            },
            |proofs| {
                verified = (|| {
                    let proofs = proofs.into_inner();
                    let produced = proofs.len();
                    for run in proofs {
                        self.verify(&run)?;
                        black_box(run);
                    }
                    mobench_sdk::record_run_u64("verified_proofs", produced as u64);
                    Ok(())
                })();
            },
        );
        verified?;
        report
    }
}

fn execution_error(error: impl Display) -> TimingError {
    TimingError::Execution(error.to_string())
}

fn initialize_threads() -> Result<(), TimingError> {
    let available = AVAILABLE_THREADS
        .get_or_init(std::thread::available_parallelism)
        .as_ref()
        .map_err(execution_error)?;
    parallel::init_with_threads(*available).map_err(|topology| {
        TimingError::Execution(format!(
            "benchmark requires {available} available threads, got {topology:?}"
        ))
    })?;
    mobench_sdk::record_run_u64("available_parallelism", available.get() as u64);
    mobench_sdk::record_run_u64("threads", parallel::num_threads() as u64);
    Ok(())
}

fn shielded_fixture() -> Result<Standalone, TimingError> {
    initialize_threads()?;
    let run = shielded_host::spends(SPENDS_PER_LEAF);
    Standalone::new(
        "shielded",
        shielded_host::ELF,
        run.advice,
        Output::new(run.expected),
        LEAF_LOG_INV_RATE,
    )
}

fn record_workload() {
    mobench_sdk::record_run_u64("spends_per_leaf", SPENDS_PER_LEAF as u64);
    mobench_sdk::record_run_u64("leaf_log_inv_rate", u64::from(LEAF_LOG_INV_RATE));
}

/// Time one shielded proof per invocation; verify and drop every retained result in teardown.
pub fn shielded_prove(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = shielded_fixture()?;
    record_workload();
    fixture.run(spec)
}

/// Time one Falcon-512 signature proof; verify every retained result in teardown.
pub fn falcon_prove(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    initialize_threads()?;
    let run = falcon_host::batch(SIGNATURES);
    let fixture = Standalone::new(
        "Falcon-512",
        falcon_host::ELF,
        run.advice,
        Output::new(run.expected),
        STANDALONE_LOG_INV_RATE,
    )?;
    mobench_sdk::record_run_u64("signatures", SIGNATURES as u64);
    mobench_sdk::record_run_u64("log_inv_rate", u64::from(STANDALONE_LOG_INV_RATE));
    fixture.run(spec)
}

/// Time one L1 account and its storage-slot proof; verify every retained result in teardown.
pub fn stateproof_prove(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    initialize_threads()?;
    let run = stateproof_host::reads(ACCOUNTS);
    let fixture = Standalone::new(
        "L1 state",
        stateproof_host::ELF,
        run.advice,
        Output::new(run.expected),
        STANDALONE_LOG_INV_RATE,
    )?;
    mobench_sdk::record_run_u64("accounts", ACCOUNTS as u64);
    mobench_sdk::record_run_u64("storage_slots", STORAGE_SLOTS as u64);
    mobench_sdk::record_run_u64("log_inv_rate", u64::from(STANDALONE_LOG_INV_RATE));
    fixture.run(spec)
}

/// Time 2-to-1 aggregation of two 2-spend leaves; prepare leaves once and verify roots in teardown.
pub fn shielded_aggregate(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = shielded_fixture()?;
    let stats = fixture.program.measure(&fixture.advice).map_err(execution_error)?;
    let runs = [fixture.prove()?, fixture.prove()?];
    for run in &runs {
        fixture.verify(run)?;
    }
    mobench_sdk::record_run_u64("verified_leaves", runs.len() as u64);
    let family = Leaves::Runs {
        program: &fixture.program,
        shape: LeafShape::measured(&stats, fixture.prover.rate()),
    };
    let tree = Tree::new(
        &[family],
        TreeShape {
            arity_0: AGGREGATION_LEAVES,
            arity: AGGREGATION_LEAVES,
            rate: Rate::new(AGGREGATION_LOG_INV_RATE).map_err(execution_error)?,
        },
    )
    .map_err(execution_error)?;
    let leaves = runs.each_ref().map(|run| Leaf::new(&run.proof, run.output));
    let expected = Subtree::First(vec![fixture.expected.into(); AGGREGATION_LEAVES]);
    let count = spec.warmup as usize + spec.iterations as usize;
    record_workload();
    mobench_sdk::record_run_u64("aggregation_leaves", leaves.len() as u64);
    mobench_sdk::record_run_u64("aggregation_log_inv_rate", u64::from(AGGREGATION_LOG_INV_RATE));
    let mut verified: Result<(), TimingError> = Ok(());
    let report = mobench_sdk::timing::run_closure_with_setup_teardown(
        spec,
        || RefCell::new(Vec::with_capacity(count)),
        |proofs| {
            let root = tree.prove_first(&leaves).map_err(execution_error)?;
            proofs.borrow_mut().push(black_box(root));
            Ok(())
        },
        |proofs| {
            verified = (|| {
                let proofs = proofs.into_inner();
                let produced = proofs.len();
                for root in proofs {
                    tree.verify(&root, &expected).map_err(execution_error)?;
                    black_box(root);
                }
                mobench_sdk::record_run_u64("verified_proofs", produced as u64);
                Ok(())
            })();
        },
    );
    verified?;
    report
}
