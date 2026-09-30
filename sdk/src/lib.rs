//! The SDK of a leanVM guest: where a run starts, what it reads and what it proves. A
//! guest is a `no_std`, `no_main` binary defining
//!
//! ```ignore
//! #[unsafe(no_mangle)]
//! extern "C" fn main() {
//!     let n = *leanvm_guest::read::<u64>();
//!     leanvm_guest::commit(&work(n));
//! }
//! ```
//!
//! `read` takes values from the advice, which the prover fills and the guest has to check;
//! `commit` makes values public, and the run's output is their digest.
//!
//! The environment has no traps to handle: an illegal instruction, a misaligned or
//! unmapped access, or an `ecall` that is not `exit` leave a run with no proof. So a
//! panic is one illegal instruction, and nothing else is needed.
//!
//! Off the VM the hasher, [`Words`] and [`PublicValues`] remain, in portable Rust.
//!
//! So a guest's library code also runs natively, as its own reference, and a host computes
//! the output a guest must give.
#![no_std]

mod blake2s;
mod io;
pub use blake2s::Blake2s;
pub use io::{PublicValues, Words, as_words_unchecked};

// Reading, committing, the entry point and the precompiles exist on the VM only.
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub use io::{commit, read, read_slice, read_unchecked};
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub mod precompile;
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
mod vm;
