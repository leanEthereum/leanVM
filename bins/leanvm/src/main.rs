//! Benchmark CLI.

use aggregate::{LeafProgram, Shape};
use bench::Plan;
use clap::builder::RangedU64ValueParser;
use clap::{Parser, Subcommand};
use leanvm::{Prover, Rate};
use std::error::Error as StdError;
use std::path::PathBuf;

mod aggregate;
mod fibonacci;
mod guest;
mod tracked;
mod workload;

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm (1 through 4).
    #[arg(long = "log-inv-rate", value_name = "LOG_INV_RATE", global = true, default_value = "1", value_parser = parse_rate)]
    rate: Rate,

    /// Enable hierarchical timing traces. Use RUST_LOG to adjust verbosity.
    #[arg(long, global = true)]
    tracing: bool,

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
        #[arg(long, value_delimiter = ',', value_parser = guest::parse_word)]
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
    /// Prove and verify a guest checking leanDA blobs and computing their commitment.
    Leanda {
        /// Blobs of 128 KiB to check.
        #[arg(long, default_value_t = 1, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        blobs: usize,
    },
    /// Prove a leaf program once, then an aggregation tree over copies of its proof.
    Aggregate {
        /// The leaf program.
        #[arg(long, value_enum, default_value = "leanxmss")]
        program: LeafProgram,
        /// The leaf program's size: Fibonacci's steps, or the signatures it verifies.
        #[arg(long, default_value_t = 400, value_parser = RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
        /// The leaves: the first level's arity times a power of the nodes' arity.
        #[arg(long, default_value_t = 4)]
        leaves: usize,
        /// The leaves each first-level node verifies.
        #[arg(long, default_value_t = 2)]
        arity0: usize,
        /// The children each node verifies.
        #[arg(long, default_value_t = 2)]
        arity: usize,
    },
    /// Prove the benchmarks CI tracks and print them as Bencher Metric Format JSON.
    ///
    /// A proven case reports `latency`, `proof-size`, `verify`, one `stage.<name>` per
    /// top-level span of the proof (`--tracing`'s first level under `Prove`) and `peak-memory`.
    ///
    /// The lists are `bins/leanvm/src/tracked.rs`.
    Bench {
        /// Count every program at the README's sizes without proving: the exact counts only.
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
}

fn parse_rate(log_inv_rate: &str) -> Result<Rate, Box<dyn StdError + Send + Sync>> {
    Ok(Rate::new(log_inv_rate.parse()?)?)
}

fn main() {
    let cli = Cli::parse();
    let prover = Prover::new();
    let plan = Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing {
        bench::init_tracing();
    }
    match cli.command {
        Command::Fibonacci { n } => fibonacci::run_fibonacci(n, &prover, cli.rate, plan),
        Command::Guest { elf, advice } => guest::run_guest(&elf, &advice, &prover, cli.rate, plan),
        Command::Leanxmss { n } => workload::run(&workload::leanxmss(n), &prover, cli.rate, plan),
        Command::Leansphincs { n } => workload::run(&workload::leansphincs(n), &prover, cli.rate, plan),
        Command::Leanda { blobs } => workload::run(&workload::leanda(blobs), &prover, cli.rate, plan),
        Command::Aggregate {
            program,
            n,
            leaves,
            arity0,
            arity,
        } => {
            let shape = Shape {
                leaves,
                arity_0: arity0,
                arity,
            };
            aggregate::run(program, n, shape, &prover, cli.rate, plan);
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
            &prover,
            cli.rate,
            plan,
        ),
    }
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
