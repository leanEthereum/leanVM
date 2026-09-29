//! Benchmark CLI.

use clap::{Parser, Subcommand};

mod da;
mod fibonacci;
mod guest;
mod signatures;
mod workload;

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm (1 through 4).
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..=4)
    )]
    log_inv_rate: usize,

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
    /// Prove and verify a run of a RISC-V guest (see `guests/`).
    Guest {
        /// The guest's ELF executable.
        elf: std::path::PathBuf,
        /// The public input: up to four 64-bit words, decimal or 0x-prefixed.
        #[arg(long, value_delimiter = ',', value_parser = guest::parse_word)]
        input: Vec<u64>,
        /// The advice: words the guest reads at `ADVICE_BASE`, which the statement does not cover.
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
    /// Measure every workload guest, the most one proof holds, without proving: a markdown table.
    Cycles,
    /// Prove and verify a guest checking leanDA blobs and computing their commitment.
    Leanda {
        /// Blobs of 128 KiB to check.
        #[arg(long, default_value_t = 1, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        blobs: usize,
    },
}

fn main() {
    let cli = Cli::parse();
    lean_vm::init_prover();
    let plan = primitives::bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing {
        primitives::init_tracing();
    }
    match cli.command {
        Command::Fibonacci { n } => fibonacci::run_fibonacci(n, cli.log_inv_rate, plan),
        Command::Guest { elf, input, advice } => guest::run_guest(&elf, &input, &advice, cli.log_inv_rate, plan),
        Command::Leanxmss { n } => workload::run(&signatures::leanxmss(n), cli.log_inv_rate, plan),
        Command::Leansphincs { n } => workload::run(&signatures::leansphincs(n), cli.log_inv_rate, plan),
        Command::Cycles => workload::cycles(&[signatures::leanxmss(400), signatures::leansphincs(104), da::leanda(1)]),
        Command::Leanda { blobs } => workload::run(&da::leanda(blobs), cli.log_inv_rate, plan),
    }
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
