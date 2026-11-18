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

    /// Thread count (0: one per core).
    #[arg(long, default_value_t = 0)]
    threads: usize,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let config = sidecar::Config {
        socket: cli.socket,
        threads: cli.threads,
    };
    let Err(e) = match cli.prover {
        Prover::Stable => sidecar::serve::<StableProver>(&config),
        Prover::Experimental => sidecar::serve::<ExperimentalProver>(&config),
    };
    eprintln!("leanvm-sidecar: {}: {e}", config.socket.display());
    ExitCode::FAILURE
}
