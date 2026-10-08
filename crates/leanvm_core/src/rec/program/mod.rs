//! The verifier of a leanVM proof as a RISC-V program: recursion on the machine itself.
//!
//! The verifier is written once over an arithmetic and a transcript (`fiat_shamir::arith`).
//!
//! Run over [`record::Gen`], it leaves the list of its steps, which [`lower`] turns into instructions: products on the
//! extension registers, hashes by the compression instruction, the proof read off the advice.
//!
//! The program depends on the shape of the proofs it verifies alone, the advice on the proofs.
//!
//! [`tree`] builds the two programs of an aggregation tree from it.

mod lower;
mod record;
pub mod tree;

use crate::ProgramError;
use crate::cpu::CpuError;

/// Why a verifier program could not be built.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BuildError {
    /// The shape is not one the verified program can announce, or the recorder's run of the verifier failed.
    #[error(transparent)]
    Shape(#[from] CpuError),
    /// The verifier does not fit a program.
    #[error(transparent)]
    Program(#[from] ProgramError),
}
