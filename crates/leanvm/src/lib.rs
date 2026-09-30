//! leanVM: a minimal zkVM for RISC-V (rv64im). A [`Program`] is a guest's ELF executable
//! ([`Program::from_elf`], see `programs/`) or a text written by hand ([`Program::new`],
//! with [`asm`]), [`prove`] runs it and
//! proves the run, [`verify`] checks the proof against the program and the output the
//! run claims: `a0..a3` when it called `exit`.
//!
//! [`prove`] also takes the run's ADVICE, the words the program finds at
//! [`ADVICE_BASE`]. The statement says nothing about them beyond how many the program's
//! region holds. What a program reads there it has to check itself.
//! No knowledge-extraction theorem is claimed. Passing more words than the region holds is a
//! programming error, and panics.
//!
//! End to end in [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

pub use leanvm_core::security;

pub use leanvm_core::{
    cpu::{CpuError, Program, Proof, Stats, prove, verify},
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
    rv::ElfError,
    rv::{ADVICE_BASE, RAM_BASE, TEXT_BASE, Trap, asm},
};

/// Call once before [`verify`]. Idempotent, and [`setup_prover`] does it for you.
pub fn setup_verifier() {
    leanvm_core::init_prover_pool();
}

/// Call once before [`prove`].
///
/// There is one arena per process, so only one [`prove`] call may run at a
/// time in a process: to prove in parallel, use separate processes.
pub fn setup_prover() {
    zk_alloc::enable_arena();
    setup_verifier();
}

/// [`setup_prover`] for a machine with small memory.
pub fn setup_prover_without_arena() {
    setup_verifier();
}
