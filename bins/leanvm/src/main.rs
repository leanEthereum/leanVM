//! Benchmark CLI.

use aggregate::{Declare, LeafProgram, Signers};
use bench::Plan;
use clap::builder::RangedU64ValueParser;
use clap::{Parser, Subcommand};
use leanvm::aggregate::Capacity;
use leanvm::{Prover, Randomness, Rate};
use std::error::Error;
use std::fmt::Arguments;
use std::num::{NonZeroUsize, ParseIntError};
use std::path::PathBuf;
use std::time::Duration;
use workload::Workload;

/// jemalloc, or under `system-alloc` the system allocator for a heap profiler that hooks `malloc` (AGENTS.md, Profiling); counted either way.
#[cfg(not(feature = "system-alloc"))]
#[global_allocator]
static ALLOCATOR: bench::Counting<bench::Jemalloc> = bench::Counting(bench::Jemalloc);
#[cfg(feature = "system-alloc")]
#[global_allocator]
static ALLOCATOR: bench::Counting<std::alloc::System> = bench::Counting(std::alloc::System);

mod aggregate;
mod tracked;
mod workload;

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm (1 through 4).
    #[arg(long = "log-inv-rate", value_name = "LOG_INV_RATE", global = true, default_value = "1", value_parser = parse_rate)]
    rate: Rate,

    /// WHIR inverse-rate logarithm of an aggregation tree's leaf proofs (1 through 4); the tree's own proofs take `--log-inv-rate`.
    #[arg(long = "leaf-log-inv-rate", value_name = "LOG_INV_RATE", global = true, default_value = "2", value_parser = parse_rate)]
    leaf_rate: Rate,

    /// Enable hierarchical timing traces. Use RUST_LOG to adjust verbosity.
    #[arg(long, global = true)]
    tracing: bool,

    /// Make zero-knowledge proofs, each from fresh randomness of the operating system: a single run's, or an aggregation tree's leaves.
    #[arg(long, global = true)]
    zk: bool,

    /// Measured proving passes after warmup.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = RangedU64ValueParser::<usize>::new().range(1..)
    )]
    repeat: usize,

    /// Idle seconds before each measured pass.
    #[arg(long, global = true, default_value_t = 2)]
    cooldown: u64,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Prove and verify Fibonacci modulo 2^64.
    Fibonacci {
        /// Number of recurrence steps.
        #[arg(long, default_value = "2000000")]
        n: usize,
    },
    /// Prove and verify a run of a RISC-V guest (see `programs/`).
    Guest {
        /// The guest's ELF executable.
        elf: PathBuf,
        /// The advice: the words the guest reads, decimal or 0x-prefixed. The statement does not cover it.
        #[arg(long, value_delimiter = ',', value_parser = parse_word)]
        advice: Vec<u64>,
    },
    /// Prove and verify a guest checking leanXMSS signatures, one key each.
    Leanxmss {
        /// Signatures to verify.
        #[arg(long, default_value_t = 64, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking leanSPHINCS signatures, one key each.
    Leansphincs {
        /// Signatures to verify.
        #[arg(long, default_value_t = 16, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking Falcon-512 signatures, one key each.
    Falcon {
        /// Signatures to verify.
        #[arg(long, default_value_t = 4, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking L1 state proofs: mainnet accounts and storage slots at one block.
    Stateproof {
        /// Reads to verify, each an account and one of its slots.
        #[arg(long, default_value_t = 4, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking shielded transfers: privacy-pool spends, two notes in and two out.
    Shielded {
        /// Spends to check.
        #[arg(long, default_value_t = 16, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking leanDA blobs and computing their commitment.
    Leanda {
        /// Blobs of 128 KiB to check.
        #[arg(long, default_value_t = 1, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        blobs: usize,
    },
    /// Prove a leaf program once, then an aggregation tree over copies of its proof; or, with `--signers`, a
    /// signer-set tree over distinct leaves, each publishing the signer set it verifies.
    Aggregate {
        /// The leaf program.
        #[arg(long, value_enum, default_value = "leanxmss")]
        program: LeafProgram,
        /// The leaf program's size: Fibonacci's steps, or the signatures it verifies.
        #[arg(long, default_value_t = 400, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
        /// The leaves: the first level's arity times a power of the nodes' arity; with `--signers`, any multiple of
        /// the first level's arity.
        #[arg(long, default_value_t = 4)]
        leaves: usize,
        /// The leaves each first-level node verifies.
        #[arg(long, default_value_t = 2)]
        arity0: usize,
        /// The children each node verifies; with `--signers`, the most, the last node of a level taking fewer.
        #[arg(long, default_value_t = 2)]
        arity: usize,
        /// A signer-set tree (leanxmss and leansphincs): each leaf a distinct run publishing its signer set, the
        /// tree proven bottom-up, every node declaring the union of its children's sets, and the root verified by
        /// its set alone. Each node's proving time is reported under its circuit; `--repeat` proves the tree again.
        #[arg(long)]
        signers: bool,
        /// The signer-set tree's bound on claims: every node's children's sets together hold fewer. Required with
        /// `--signers`: the capacity sets every circuit's heights, so it has no default.
        #[arg(long, requires = "signers", required_if_eq("signers", "true"))]
        max_claims: Option<usize>,
        /// The signer-set tree's bound on groups: every node's children's sets together have at most as many.
        /// Required with `--signers`.
        #[arg(long, requires = "signers", required_if_eq("signers", "true"))]
        max_groups: Option<usize>,
        /// The groups each leaf's signatures are split across, group `j` signing message `j`.
        #[arg(long, default_value_t = 1, requires = "signers")]
        groups: usize,
        /// The percentage of each leaf's signers, group by group, that are the previous leaf's, so the union is
        /// smaller than the sum of the leaves' sets.
        #[arg(long, default_value_t = 0, requires = "signers", value_parser = RangedU64ValueParser::<usize>::new().range(0..=100))]
        overlap: usize,
        /// What the root declares: the union of its children's sets, or the first half of its claims.
        #[arg(long, value_enum, default_value = "all", requires = "signers")]
        declare: Declare,
    },
    /// Prove the benchmarks CI tracks and print them as Bencher Metric Format JSON.
    ///
    /// A proven case reports `latency`, `proof-size`, `verify`, one `stage.<name>` per
    /// top-level span of the proof (`--tracing`'s first level under `Prove`), `peak-memory`,
    /// and the proving passes' `heap-peak` and `allocations`, as the global allocator counts
    /// them; an aggregation tree's case reports them for its first-level node and its node.
    ///
    /// The lists are `bins/leanvm/src/tracked.rs`.
    Bench {
        /// Count every program, and two aggregation trees' circuits, at the README's sizes
        /// without proving: the exact counts only.
        #[arg(long)]
        cycles_only: bool,
        /// Print the counts as a markdown table rather than JSON.
        #[arg(long, requires = "cycles_only")]
        markdown: bool,
        /// Print the counts as JSON and append the markdown table to this file, from the same pass.
        #[arg(long, requires = "cycles_only", conflicts_with = "markdown")]
        markdown_file: Option<PathBuf>,
        /// Prove only the case of this name, as each of CI's proving jobs does.
        #[arg(long, conflicts_with = "cycles_only")]
        only: Option<String>,
    },
    /// Write the tracked aggregation circuits and instruction table bindings (with `--features circuits`) for the Lean checkers.
    Circuits {
        /// The directory to write them to.
        out: PathBuf,
    },
}

fn parse_rate(log_inv_rate: &str) -> Result<Rate, Box<dyn Error + Send + Sync>> {
    Ok(Rate::new(log_inv_rate.parse()?)?)
}

/// A word, decimal or 0x-prefixed.
fn parse_word(word: &str) -> Result<u64, ParseIntError> {
    word.strip_prefix("0x")
        .map_or_else(|| word.parse(), |hex| u64::from_str_radix(hex, 16))
}

/// An error and its causes, outermost first.
fn chain(error: &dyn Error) -> String {
    let mut text = error.to_string();
    let mut source = error.source();
    while let Some(cause) = source {
        text = format!("{text}: {cause}");
        source = cause.source();
    }
    text
}

/// What the user got wrong, said once and plainly: none of these is a bug here.
fn refuse(what: Arguments) -> ! {
    eprintln!("{what}");
    std::process::exit(1)
}

fn main() {
    let cli = Cli::parse();
    let fixed_threads = match &cli.command {
        Command::Bench { cycles_only: true, .. } | Command::Circuits { .. } => false,
        Command::Bench { only, .. } => only.as_deref().is_some_and(|name| name.ends_with("-16thread")),
        _ => std::env::var_os("LEANVM_NUM_THREADS").is_none(),
    };
    if fixed_threads {
        parallel::init_with_threads(NonZeroUsize::new(16).unwrap())
            .unwrap_or_else(|error| refuse(format_args!("cannot configure 16 benchmark threads: {error}")));
    }
    if !matches!(cli.command, Command::Bench { .. } | Command::Circuits { .. }) || fixed_threads {
        let topology = parallel::topology();
        eprintln!(
            "Benchmark pool: {} threads ({} performance, {} efficiency)",
            topology.total(),
            topology.perf,
            topology.efficiency
        );
    }
    if cli.zk && matches!(cli.command, Command::Bench { .. }) {
        refuse(format_args!(
            "--zk is not for the tracked benchmarks, which are plain proofs"
        ));
    }
    let prover = Prover::new(cli.rate);
    let prover = if cli.zk {
        prover.zero_knowledge(Randomness::Os)
    } else {
        prover
    };
    let leaf_prover = Prover::new(cli.leaf_rate);
    // An aggregation tree's leaves are zero knowledge with --zk; its own proofs need not be, as they hold only those leaves.
    let leaf_prover = if cli.zk {
        leaf_prover.zero_knowledge(Randomness::Os)
    } else {
        leaf_prover
    };
    let plan = Plan::new(cli.repeat, Duration::from_secs(cli.cooldown));
    if cli.tracing {
        bench::init_tracing();
    }
    match cli.command {
        Command::Fibonacci { n } => Workload::fibonacci(n).run(&prover, plan),
        Command::Guest { elf, advice } => Workload::guest(&elf, advice).run(&prover, plan),
        Command::Leanxmss { n } => Workload::leanxmss(n).run(&prover, plan),
        Command::Leansphincs { n } => Workload::leansphincs(n).run(&prover, plan),
        Command::Falcon { n } => Workload::falcon(n).run(&prover, plan),
        Command::Stateproof { n } => Workload::stateproof(n).run(&prover, plan),
        Command::Shielded { n } => Workload::shielded(n).run(&prover, plan),
        Command::Leanda { blobs } => Workload::leanda(blobs).run(&prover, plan),
        Command::Aggregate {
            program,
            n,
            leaves,
            arity0,
            arity,
            signers,
            max_claims,
            max_groups,
            groups,
            overlap,
            declare,
        } => {
            if signers {
                let signers = Signers {
                    capacity: Capacity {
                        claims: max_claims.expect("--signers requires --max-claims"),
                        groups: max_groups.expect("--signers requires --max-groups"),
                    },
                    groups,
                    overlap,
                    declare,
                };
                aggregate::run_signers(program, n, leaves, arity0, arity, signers, &leaf_prover, &prover, plan);
            } else {
                aggregate::run(&program.workload(n), leaves, arity0, arity, &leaf_prover, &prover, plan);
            }
        }
        Command::Bench {
            cycles_only,
            markdown,
            markdown_file,
            only,
        } => tracked::run(
            cycles_only,
            markdown,
            markdown_file.as_deref(),
            only.as_deref(),
            &leaf_prover,
            &prover,
            plan,
        ),
        #[cfg(feature = "circuits")]
        Command::Circuits { out } => tracked::dump(&out, leaf_prover.rate(), prover.rate()),
        #[cfg(not(feature = "circuits"))]
        Command::Circuits { .. } => refuse(format_args!("`circuits` needs `--features circuits`")),
    }
}
