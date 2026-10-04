//! leanVM: a minimal zkVM for RISC-V (rv64im).
//!
//! # Overview
//!
//! A program is a guest's ELF executable, or a text written by hand with the assembler.
//!
//! The prover runs it on its advice and proves the run.
//!
//! The verifier checks the proof against two public things only:
//!
//! - the program,
//! - the output the run claims, the registers `a0..a3` at its exit.
//!
//! ```text
//!     prover  : program + advice  ──run──▶  output  ──prove──▶  proof
//!     verifier: program + output + proof  ──▶  accept or refuse
//! ```
//!
//! # The advice
//!
//! The advice is the words the program finds at the advice base.
//!
//! It is the prover's alone: the statement says nothing about it, beyond how many words fit.
//!
//! So a proof shows that *some* advice makes the program exit with the output.
//!
//! What a program reads there, it must check itself.
//!
//! # Examples
//!
//! ```no_run
//! use leanvm::{Program, Proof, Prover, Rate};
//!
//! // The prover's side.
//! let program = Program::from_elf(&std::fs::read("guest.elf")?)?;
//! let run = Prover::new(Rate::MIN).prove(&program, &[42])?;
//! let bytes = run.proof.to_bytes();
//!
//! // The verifier's side: the same program, the claimed output, and the bytes.
//! program.verify(run.output, &Proof::from_bytes(&bytes)?)?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Many proofs of one program aggregate into one proof through the aggregation module.

pub mod aggregate;
mod envelope;
mod error;
mod output;
mod program;
mod proof;
mod prover;

#[cfg(test)]
mod fixtures;

pub use error::{DecodeError, VerifyError};
pub use output::Output;
pub use program::Program;
pub use proof::Proof;
pub use prover::{ProvenRun, Prover};

pub use leanvm_core::{
    cpu::{ProveError, Stats},
    pcs::{InvalidRate, Rate},
    rv::{ElfError, ProgramError, Region, Trap, asm},
};
