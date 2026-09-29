//! The runtime of a leanVM guest: where a run starts, how it ends, its public input
//! and output. A guest is a `no_std`, `no_main` binary defining
//!
//! ```ignore
//! #[unsafe(no_mangle)]
//! extern "C" fn main() { leanvm_guest::output([..]) }
//! ```
//!
//! The environment has no traps to handle: an illegal instruction, a misaligned or
//! unmapped access, or an `ecall` that is not `exit` leave a run with no proof. So a
//! panic is one illegal instruction, and nothing else is needed.
//!
//! Off the VM only the hasher remains, computed in portable Rust.
//!
//! So a guest's library code also runs natively, as its own reference.
#![no_std]

mod blake2s;
pub use blake2s::Blake2s;

// The entry point, the input, the output and the advice exist on the VM only.
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
mod vm;
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub use vm::{advice, input, output};
