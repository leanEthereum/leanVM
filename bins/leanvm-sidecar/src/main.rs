//! The leanVM sidecar: proves for one machine's clients over a Unix socket. `README.md` says how to run it and
//! specifies the protocol.

#[global_allocator]
static ALLOCATOR: bench_harness::Jemalloc = bench_harness::Jemalloc;

use clap::Parser;
use experimental_lean_vm_core::ExperimentalProver;
use stable_lean_vm_core::StableProver;
use std::path::PathBuf;
use std::process::ExitCode;

/// Which of the two provers runs.
#[derive(Clone, Copy, clap::ValueEnum)]
enum Prover {
    /// The stable prover.
    Stable,
    /// The experimental prover.
    Experimental,
}

#[derive(Parser)]
#[command(name = "leanvm-sidecar")]
struct Cli {
    /// The prover to run.
    #[arg(long, value_enum)]
    prover: Prover,

    /// The Unix socket to listen on. It appears once the sidecar is ready.
    #[arg(long)]
    socket: PathBuf,

    /// The longest request taken, in MiB.
    #[arg(
        long,
        default_value_t = 1024,
        value_parser = clap::builder::RangedU64ValueParser::<u64>::new().range(1..=1 << 20)
    )]
    max_request_mib: u64,

    /// Thread count (0: one per core). With the experimental prover, the performance cores' workers, beside which
    /// it adds the efficiency cores'.
    #[arg(long, default_value_t = 0)]
    threads: usize,

    /// Print each proof's timing tree. Use RUST_LOG to adjust verbosity.
    #[arg(long)]
    tracing: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if cli.tracing {
        bench_harness::init_tracing();
    }
    let config = sidecar::Config {
        socket: cli.socket,
        max_request: cli.max_request_mib << 20,
        threads: cli.threads,
    };
    let Err(e) = match cli.prover {
        Prover::Stable => sidecar::serve::<StableProver>(&config),
        Prover::Experimental => sidecar::serve::<ExperimentalProver>(&config),
    };
    eprintln!("leanvm-sidecar: {}: {e}", config.socket.display());
    ExitCode::FAILURE
}
