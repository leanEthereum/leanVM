//! Benchmark CLI for signature and blob proofs, recursion, batched Keccak, and the Fibonacci demo.
#![expect(clippy::duplicate_mod, reason = "each prover gets its own instance of the benchmarks")]

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use clap::{Parser, Subcommand};

mod report;

/// The aliases one prover module gives the benchmarks, which name its crates as `rec_aggregation`, `leanvm_core`, ...
macro_rules! prover {
    ($agg:ident, $core:ident, $par:ident, $comp:ident, $da:ident, $gkr:ident, $xmss:ident, $sphincs:ident, $prim:ident) => {
        pub use ::$agg as rec_aggregation;
        pub use ::$comp as lean_compiler;
        pub use ::$core as leanvm_core;
        pub use ::$da as lean_da;
        pub use ::$gkr as keccak_gkr;
        pub use ::$par as parallel;
        pub use ::$prim as primitives;
        pub use ::$sphincs as lean_sphincs;
        pub use ::$xmss as lean_xmss;

        /// The `hash` subcommand: the Keccak GKR alone, on `2^log_n` permutations.
        pub fn hash(log_n: usize, log_inv_rate: usize, plan: bench::Plan) {
            use leanvm_core::{keccak, pcs};
            let least = (pcs::MIN_STACKED_LOG - keccak::SLOT_LOG).max(keccak::MIN_STEPS.ilog2() as usize);
            let most = pcs::MAX_STACKED_LOG - keccak::SLOT_LOG;
            assert!(
                (least..=most).contains(&log_n),
                "--log-n must be in {least}..={most}"
            );
            keccak_gkr::batch_bench::run(1 << log_n, keccak::DEPTH, log_inv_rate, plan).print();
        }

        /// Run the CLI's command on this prover, whose thread pool is the only one started.
        pub fn run(cli: crate::Cli) {
            use crate::Command;
            parallel::init();
            let plan = bench::Plan::new(cli.repeat, cli.cooldown);
            if cli.tracing && !matches!(&cli.command, Command::Recursion { .. }) {
                bench::init_tracing();
            }
            if let Command::Aggregate { blobs, .. }
            | Command::Recursion {
                blobs_per_leaf: blobs,
                ..
            } = cli.command
            {
                assert!(
                    blobs <= lean_da::DA_MAX_ROWS,
                    "at most {} blobs",
                    lean_da::DA_MAX_ROWS
                );
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
                    leaf_log_inv_rate,
                } => {
                    benchmark::run_recursion(
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
                Command::Hash { log_n } => hash(log_n, cli.log_inv_rate, plan),
                Command::Fibonacci { n } => fibonacci::run_fibonacci(n, cli.log_inv_rate, plan),
            }
        }
    };
}
pub(crate) use prover;
mod experimental;
mod stable;

/// Which of the two provers runs.
#[derive(Clone, Copy, clap::ValueEnum)]
enum Prover {
    /// The plain, portable prover.
    Stable,
    /// The optimized prover.
    Experimental,
}

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

    /// The prover to run.
    #[arg(long, global = true, value_enum, default_value_t = Prover::Experimental)]
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
        #[arg(long, default_value_t = 0)]
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
        #[arg(long, default_value_t = 0)]
        blobs_per_leaf: usize,
        /// WHIR inverse-rate logarithm of the leaves (1 through 4)
        #[arg(
            long,
            value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..=4)
        )]
        leaf_log_inv_rate: Option<usize>,
    },
    /// Prove and verify a batch of Keccak-f permutations with the VM's GKR, outside the VM.
    Hash {
        /// Log2 of the number of permutations: a committed block the verifiers accept, from the
        /// least stack (or the reduction's fewest steps, if more) to the largest.
        #[arg(long, default_value_t = 17)]
        log_n: usize,
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
        Prover::Stable => stable::run(cli),
        Prover::Experimental => experimental::run(cli),
    }
}
