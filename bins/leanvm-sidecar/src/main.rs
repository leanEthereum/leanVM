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
#[command(name = "leanvm-sidecar", version = env!("LEANVM_SIDECAR_VERSION"))]
struct Cli {
    /// The Unix socket to listen on. It appears once the sidecar is ready.
    #[arg(long)]
    socket: PathBuf,

    /// Thread count (0: one per core).
    #[arg(long, default_value_t = 0)]
    threads: usize,

    /// Exit when standard input closes: a program that launches the sidecar through a pipe stops it
    /// by exiting, however it exits.
    #[arg(long)]
    exit_with_stdin: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if cli.exit_with_stdin {
        std::thread::spawn(|| {
            let _ = std::io::copy(&mut std::io::stdin(), &mut std::io::sink());
            std::process::exit(0);
        });
    }
    let Err(e) = sidecar::serve::<P>(&cli.socket, cli.threads);
    eprintln!("leanvm-sidecar: {}: {e}", cli.socket.display());
    ExitCode::FAILURE
}
