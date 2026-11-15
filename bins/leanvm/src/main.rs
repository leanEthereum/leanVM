//! Benchmark CLI for signature and blob proofs, recursion, batched Keccak, and the Fibonacci demo.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use clap::{Parser, Subcommand};
use experimental_lean_vm_core::ExperimentalProver;
use stable_lean_vm_core::StableProver;

mod benchmark;
mod fibonacci;
mod report;

/// A prover as the CLI runs it: the shared crates' [`isa::Prover`], and the Keccak GKR alone, which only its tree has.
trait CliProver: isa::Prover {
    /// The `hash` subcommand: the Keccak GKR alone, on `2^log_n` permutations.
    fn hash(log_n: usize, log_inv_rate: usize, plan: bench::Plan);
}

impl CliProver for StableProver {
    fn hash(log_n: usize, log_inv_rate: usize, plan: bench::Plan) {
        use stable_lean_vm_core::{keccak, pcs};
        let least = (pcs::MIN_STACKED_LOG - keccak::SLOT_LOG).max(keccak::MIN_STEPS.ilog2() as usize);
        check_log_n(log_n, least, pcs::MAX_STACKED_LOG - keccak::SLOT_LOG);
        stable_keccak_gkr::batch_bench::run(1 << log_n, keccak::DEPTH, log_inv_rate, plan).print();
    }
}

impl CliProver for ExperimentalProver {
    fn hash(log_n: usize, log_inv_rate: usize, plan: bench::Plan) {
        use experimental_lean_vm_core::{keccak, pcs};
        let least = (pcs::MIN_STACKED_LOG - keccak::SLOT_LOG).max(keccak::MIN_STEPS.ilog2() as usize);
        check_log_n(log_n, least, pcs::MAX_STACKED_LOG - keccak::SLOT_LOG);
        experimental_keccak_gkr::batch_bench::run(1 << log_n, keccak::DEPTH, log_inv_rate, plan).print();
    }
}

fn check_log_n(log_n: usize, least: usize, most: usize) {
    if !(least..=most).contains(&log_n) {
        invalid(format!("--log-n must be in {least}..={most}"));
    }
}

/// Run the CLI's command on prover `P`, whose thread pool is the only one started.
fn run<P: CliProver>(cli: Cli) {
    if let Command::Aggregate { blobs, .. }
    | Command::Recursion {
        blobs_per_leaf: blobs, ..
    } = cli.command
        && blobs > lean_da::DA_MAX_ROWS
    {
        invalid(format!("at most {} blobs", lean_da::DA_MAX_ROWS));
    }
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
        Command::Hash { log_n } => P::hash(log_n, cli.log_inv_rate, plan),
        Command::Fibonacci { n } => fibonacci::run_fibonacci::<P>(n, cli.log_inv_rate, plan),
    }
}

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

/// Exit with a usage error, as clap reports an argument out of range.
fn invalid(message: String) -> ! {
    use clap::CommandFactory;
    Cli::command()
        .error(clap::error::ErrorKind::ValueValidation, message)
        .exit()
}

fn main() {
    let cli = Cli::parse();
    match cli.prover {
        Prover::Stable => run::<StableProver>(cli),
        Prover::Experimental => run::<ExperimentalProver>(cli),
    }
}
