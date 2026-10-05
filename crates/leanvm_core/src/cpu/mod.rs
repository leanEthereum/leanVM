//! Proving a run of a RISC-V program, and verifying the proof (`doc/leanvm/main.tex`).
//!
//! The machine is RISC-V: `pc`, register numbers, addresses and timestamps are integers.
//!
//! Each is read as the field element of `K = F64` with those bits.
//!
//! What an instruction computes is a flock circuit.
//!
//! The tables only move words between the bytecode, the registers and those circuits.
//!
//! Challenges and transcript scalars live in `E = F192`.
//!
//! A proof goes through these stages:
//!
//! - the program runs, and its rows are recorded, then padded to powers of two;
//! - the rows fill one stacked witness, which is committed;
//! - the bus balance, one batch of table constraints, and every circuit's reduction are proven;
//! - one opening discharges every claim they leave.

mod batch;
mod deferred;
mod error;
pub(crate) mod execute;
pub mod filler;
mod layout;
mod output;
mod program;
mod proof;
mod prover;
mod reduce;
mod witness;

pub use deferred::{Claim, DeferredClaims, MalformedClaim, ProgramPoint};
pub use error::{CpuError, DecodeError, ProveError, VerifyError};
pub use execute::Execution;
pub(crate) use execute::{Payload, Payloads, Row, RowRef, Trace};
pub use layout::{Framework, Layout, Lookup, N_BYTECODE_COLUMNS, N_SHARED, Q_BASE, Schema, Shared, Sizes};
pub use output::Output;
pub use program::{Program, Stats};
pub use proof::Proof;
pub use prover::{ProvenRun, Prover};
pub(crate) use reduce::TableReduction;

/// Each table holds at most `2^MAX_LOG_ROWS` rows: its class's executed instructions.
///
/// With the bytecode cap, these are the instance caps the verifier checks before any reduction.
///
/// No counting argument needs them: they bound the layout an announcement describes.
pub const MAX_LOG_ROWS: usize = 32;

/// The base-two logarithm of the most bytecode entries whose bus needs no grinding.
///
/// Each bit of entries past it doubles the bus's degree, so it costs one bit of grinding (§sec:e2e-ledger).
pub const UNGROUND_LOG_BYTECODE: usize = 21;
