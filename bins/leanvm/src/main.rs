//! Benchmark CLI.

use clap::{Parser, Subcommand};
use leanvm::{Prover, Rate};

mod aggregate;
mod fibonacci;
mod guest;
mod recursion;
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
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..)
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
        elf: std::path::PathBuf,
        /// The advice: the words the guest reads, decimal or 0x-prefixed. The statement does not cover it.
        #[arg(long, value_delimiter = ',', value_parser = guest::parse_word)]
        advice: Vec<u64>,
    },
    /// Prove and verify a guest checking leanXMSS signatures, one key each.
    Leanxmss {
        /// Signatures to verify.
        #[arg(long, default_value_t = 64, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking leanSPHINCS signatures, one key each.
    Leansphincs {
        /// Signatures to verify.
        #[arg(long, default_value_t = 16, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        n: usize,
    },
    /// Prove and verify a guest checking leanDA blobs and computing their commitment.
    Leanda {
        /// Blobs of 128 KiB to check.
        #[arg(long, default_value_t = 1, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        blobs: usize,
    },
    /// Prove an inner program, then one recursion proof that `arity` copies of its proof verify.
    Recursion {
        /// The inner program: `fibonacci` or `leanxmss`.
        #[arg(long, default_value = "fibonacci")]
        program: String,
        /// Fibonacci steps, or leanXMSS signatures.
        #[arg(long, default_value_t = 1000)]
        n: usize,
        /// Inner proofs per outer proof.
        #[arg(long, default_value_t = 1, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        arity: usize,
        /// The inner proof's WHIR inverse-rate logarithm; `--log-inv-rate` is the outer proof's.
        #[arg(long, default_value = "1", value_parser = parse_rate)]
        inner_log_inv_rate: Rate,
    },
    /// Prove a leaf program, then an aggregation tree over `leaves` copies of its proof: a lift node per leaf and
    /// nodes of `arity` children up to the root.
    Aggregate {
        /// The leaf program: `fibonacci` or `leanxmss`.
        #[arg(long, default_value = "leanxmss")]
        program: String,
        /// Fibonacci steps, or leanXMSS signatures.
        #[arg(long, default_value_t = 400)]
        n: usize,
        /// Leaf proofs, a power of the arity.
        #[arg(long, default_value_t = 4, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        leaves: usize,
        /// Children per node.
        #[arg(long, default_value_t = 2, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(2..))]
        arity: usize,
    },
    /// Prove the benchmarks CI tracks and print them as Bencher Metric Format JSON.
    ///
    /// The lists are `bins/leanvm/src/tracked.rs`.
    Bench {
        /// Count every program at the README's sizes without proving: the exact counts only.
        #[arg(long)]
        cycles_only: bool,
        /// Print the counts as a markdown table rather than JSON.
        #[arg(long, requires = "cycles_only")]
        markdown: bool,
    },
}

fn parse_rate(log_inv_rate: &str) -> Result<Rate, Box<dyn std::error::Error + Send + Sync>> {
    Ok(Rate::new(log_inv_rate.parse()?)?)
}

fn main() {
    let cli = Cli::parse();
    let prover = Prover::new();
    let plan = bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing {
        bench::init_tracing();
    }
    match cli.command {
        Command::Fibonacci { n } => fibonacci::run_fibonacci(n, &prover, cli.rate, plan),
        Command::Guest { elf, advice } => guest::run_guest(&elf, &advice, &prover, cli.rate, plan),
        Command::Leanxmss { n } => workload::run(&workload::leanxmss(n), &prover, cli.rate, plan),
        Command::Leansphincs { n } => workload::run(&workload::leansphincs(n), &prover, cli.rate, plan),
        Command::Leanda { blobs } => workload::run(&workload::leanda(blobs), &prover, cli.rate, plan),
        Command::Recursion {
            program,
            n,
            arity,
            inner_log_inv_rate,
        } => recursion::run(&program, n, arity, inner_log_inv_rate, &prover, cli.rate, plan),
        Command::Aggregate {
            program,
            n,
            leaves,
            arity,
        } => aggregate::run(&program, n, leaves, arity, &prover, cli.rate, plan),
        Command::Bench { cycles_only, markdown } => tracked::run(cycles_only, markdown, &prover, cli.rate, plan),
    }
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
