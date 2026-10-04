//! Benchmark CLI for signature and blob proofs, recursion, and the Fibonacci demo.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use clap::{Parser, Subcommand};

mod benchmark;
mod fibonacci;
mod report;

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
    /// Prove signatures and blobs, then verify the proof. At least one count must be nonzero.
    Aggregate {
        /// XMSS signatures to aggregate.
        #[arg(long, default_value = "0")]
        xmss: usize,
        /// SPHINCS signatures to aggregate.
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
        /// XMSS signatures in each child. Sets the child proof's committed size,
        /// which is what the recursion cost should be quoted against.
        #[arg(long, default_value = "900")]
        xmss_per_leaf: usize,
        /// SPHINCS signatures in each child, on top of the XMSS ones.
        #[arg(long, default_value = "0")]
        sphincs_per_leaf: usize,
        /// Blobs in each child's LeanDA commitment. Use --xmss-per-leaf 0 for blobs alone.
        #[arg(
            long,
            default_value_t = 0,
            value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(0..=lean_da::DA_MAX_ROWS as u64)
        )]
        blobs_per_leaf: usize,
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
    leanvm_core::init_prover();
    let plan = bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing && !matches!(&cli.command, Command::Recursion { .. }) {
        bench::init_tracing();
    }
    match cli.command {
        Command::Aggregate { xmss, sphincs, blobs } => {
            benchmark::run_aggregation(xmss, sphincs, blobs, cli.log_inv_rate, plan);
        }
        Command::Recursion {
            n,
            xmss_per_leaf,
            sphincs_per_leaf,
            blobs_per_leaf,
        } => {
            benchmark::run_recursion(
                n,
                xmss_per_leaf,
                sphincs_per_leaf,
                blobs_per_leaf,
                cli.log_inv_rate,
                cli.tracing,
                plan,
            );
        }
        Command::Fibonacci { n } => {
            fibonacci::run_fibonacci(n, cli.log_inv_rate, plan);
        }
    }
}
