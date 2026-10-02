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
mod error;
mod execute;
pub mod filler;
mod layout;
mod program;
mod witness;

pub use error::{CpuError, ProveError};
pub use execute::Execution;
pub(crate) use execute::{HashRow, Row, Trace};
pub use fiat_shamir::transcript::Proof;
pub use layout::{Framework, Layout, Lookup, N_BYTECODE_COLUMNS, N_SHARED, Q_BASE, Schema, Shared, Sizes};
pub use program::{Program, Stats};

/// Each table holds at most `2^MAX_LOG_ROWS` rows: its class's executed instructions.
///
/// With the bytecode cap, these are the instance caps the verifier checks before any reduction.
///
/// No counting argument needs them: they bound the layout an announcement describes.
pub const MAX_LOG_ROWS: usize = 32;
