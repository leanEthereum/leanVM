//! The leanVM sidecar: proves for one machine's clients over a Unix socket. `README.md` says how to run it and
//! specifies the protocol.

#[global_allocator]
static ALLOCATOR: allocator::Jemalloc = allocator::Jemalloc;

use clap::Parser;
use std::path::PathBuf;
use std::process::ExitCode;

#[cfg(feature = "experimental_prover")]
type P = experimental_lean_vm_core::ExperimentalProver;
#[cfg(not(feature = "experimental_prover"))]
type P = stable_lean_vm_core::StableProver;

#[derive(Parser)]
#[command(name = "leanvm-sidecar")]
struct Cli {
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
    let Err(e) = sidecar::serve::<P>(&config);
    eprintln!("leanvm-sidecar: {}: {e}", config.socket.display());
    ExitCode::FAILURE
}
