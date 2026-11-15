//! Benchmark CLI for signature and blob proofs, recursion, and the Fibonacci demo.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use clap::{Parser, Subcommand};
use experimental_lean_vm_core::ExperimentalProver;
use stable_lean_vm_core::StableProver;

mod benchmark;
mod fibonacci;
mod report;

/// Run the CLI's command on prover `P`.
fn run<P: isa::Prover>(cli: Cli) {
    P::init();
    let plan = bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing && !matches!(&cli.command, Command::Recursion { .. }) {
        bench::init_tracing();
    }
    match cli.command {
        Command::Aggregate { xmss, sphincs, blobs } => {
            benchmark::run_aggregation::<P>(xmss, sphincs, blobs, cli.log_inv_rate, plan);
        }
        Command::Recursion {
            n,
            xmss_per_leaf,
            sphincs_per_leaf,
            blobs_per_leaf,
            leaf_log_inv_rate,
        } => {
            benchmark::run_recursion::<P>(
                n,
                xmss_per_leaf,
                sphincs_per_leaf,
                blobs_per_leaf,
                leaf_log_inv_rate.unwrap_or(cli.log_inv_rate),
                cli.log_inv_rate,
                cli.tracing,
                plan,
            );
        }
        Command::Fibonacci { n } => fibonacci::run_fibonacci::<P>(n, cli.log_inv_rate, plan),
    }
}

/// Which of the two provers runs.
#[derive(Clone, Copy, clap::ValueEnum)]
enum Prover {
    /// The stable prover.
    Stable,
    /// The experimental prover.
    Experimental,
}

#[derive(Parser)]
#[command(name = "leanvm")]
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

    /// The prover to run, before the subcommand.
    #[arg(long, value_enum)]
    prover: Prover,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Prove signatures and blobs, then verify the proof. At least one count must be nonzero.
    Aggregate {
        /// leanXMSS signatures to aggregate.
        #[arg(long, default_value = "0")]
        xmss: usize,
        /// leanSPHINCS signatures to aggregate.
        #[arg(long, default_value = "0")]
        sphincs: usize,
        /// Blobs in one LeanDA commitment (128 KiB each).
        #[arg(
            long,
            default_value_t = 0,
            value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(0..=lean_da::DA_MAX_ROWS as u64)
        )]
        blobs: usize,
    },
    /// Aggregate n child proofs into one proof.
    Recursion {
        /// Number of child aggregates.
        #[arg(long, default_value = "2")]
        n: usize,
        /// leanXMSS signatures in each child. Sets the child proof's committed size,
        /// which is what the recursion cost should be quoted against.
        #[arg(long, default_value = "900")]
        xmss_per_leaf: usize,
        /// leanSPHINCS signatures in each child, on top of the leanXMSS ones.
        #[arg(long, default_value = "0")]
        sphincs_per_leaf: usize,
        /// Blobs in each child's LeanDA commitment. Use --xmss-per-leaf 0 for blobs alone.
        #[arg(
            long,
            default_value_t = 0,
            value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(0..=lean_da::DA_MAX_ROWS as u64)
        )]
        blobs_per_leaf: usize,
        /// WHIR inverse-rate logarithm of the leaves (1 through 4)
        #[arg(
            long,
            value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..=4)
        )]
        leaf_log_inv_rate: Option<usize>,
    },
    /// Prove and verify Fibonacci in the exponent (demo).
    Fibonacci {
        /// Number of recurrence steps.
        #[arg(long, default_value = "2000000")]
        n: usize,
    },
}

fn main() {
    let cli = Cli::parse();
    match cli.prover {
        Prover::Stable => run::<StableProver>(cli),
        Prover::Experimental => run::<ExperimentalProver>(cli),
    }
}
