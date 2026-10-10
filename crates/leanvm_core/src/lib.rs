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
//! # Zero knowledge
//!
//! A plain proof is no secret: a verifier who can guess the advice recomputes the proof and compares.
//!
//! A prover made with [`Prover::zk`] makes zero-knowledge proofs, which reveal nothing of the advice or the run beyond the statement and the run's shape (each table's height and the rate).
//!
//! A program whose advice is private must therefore prove at a fixed public shape.
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
//!
//! # Implementation
//!
//! Machine words, addresses, the pc and timestamps are integers, each read as the element of `K = GF(2^64)` with those bits.
//! A timestamp is `2^40 | cycle << 5 | slot`, and the clock circuit of each table orders its accesses and steps it (§sec:memchan).
//! Every committed column is `K`-valued; challenges and transcript scalars live in `E = GF(2^192)`.
//!
//! - `pcs`: `K`-committed witness, `E`-opened, via the stacked WHIR (§sec:stacking, §annex:pcs).
//! - `witness`: `K`-valued columns stacked into one committed witness.
//! - `gkr`: the grand product via GKR (§sec:gkr), balancing the bus.
//! - `leaf`: the shared bus: grand-product balance, decomposed to per-column claims (§sec:gp through §sec:leafstack, §sec:omc).
//! - `constraints`: one table sumcheck over every table's two bus forms, the extension-field identities and the lookup producers (§sec:air).
//! - `rv`: RISC-V (rv64im): the decoder, each instruction class's function and circuit, and the reference interpreter.
//! - `tables`: the instruction tables, one per class (columns, bus tuples, clock circuits).
//! - `class_flock`: the glue to flock: each circuit proven over its own packed witness, in the same commitment.
//! - `cpu`: whole-program assembly and the prove/verify entry points.
//! - `rec`: the recursion machine and the aggregation trees (§annex:rec).

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};

mod class_flock;
mod colval;
mod constraints;
mod cpu;
mod envelope;
mod gkr;
mod leaf;
mod pcs;
mod rec;
mod rv;
mod tables;
mod witness;
mod zk;

pub use crate::pcs::{InvalidRate, Rate, SECURITY_BITS};
pub use cpu::{DecodeError, Output, Program, Proof, ProveError, ProvenRun, Prover, Stats, VerifyError};
#[doc(hidden)]
pub use rec::tree::{
    CircuitStats, DensePoly, FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tree, TreeError, TreeProof,
    TreeShape, Unsatisfied,
};
pub use rv::{ElfError, ProgramError, Region, Trap, asm};
pub use zk::randomness::Randomness;

#[doc(hidden)]
pub use crate::pcs::{MAX_MU, MIN_MU};
#[doc(hidden)]
pub use class_flock::{FlockId, MIN_CUBE_LOG, N_FLOCKS};
#[doc(hidden)]
pub use constraints::ConstraintError;
#[doc(hidden)]
pub use cpu::{CpuError, DeferredClaims, Lookup, MAX_LOG_ROWS, MalformedClaim, Q_BASE, UNGROUND_LOG_BYTECODE};
#[doc(hidden)]
pub use leaf::{BusError, N_TUPLE_BITS};
#[doc(hidden)]
pub use rv::{Alu, Class, Guest, Hash, Machine, Reg, RegisterFile, Syscall};
#[doc(hidden)]
pub use tables::{BAD_SLOT, Clock, EXIT_SLOT, Fill, N_TABLES, PerTable, TableId, Word};

/// Prepare the process for proving: spawn the worker pool up front.
///
/// - No kernel then pays the spawn cost inside a timed region.
/// - Calling it again does nothing.
///
/// Thread placement is the pool's own business:
///
/// - Performance-core workers run at `USER_INTERACTIVE`.
/// - Efficiency-core workers (Apple silicon) run at `UTILITY`.
/// - All of them draw from one claim counter.
/// - `LEANVM_NUM_THREADS` sets the performance-worker count.
pub fn init_prover() {
    parallel::init();
}

/// Below this many parallelizable items a pass runs serially: the fan-out
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// Aggregation trees: many proofs of one program, verified as one.
///
/// # Overview
///
/// ```text
///                 node                  verifies `arity` tree proofs, of either kind
///               /      \
///        first-level   first-level      each verifies `arity_0` proofs of the program
///          /  \          /  \
///       leaf  leaf    leaf  leaf
/// ```
///
/// Every tree proof states the same few hundred words:
///
/// - a digest of its leaves' outputs,
/// - claims that only the root's verifier evaluates.
///
/// A tree over one leaf, with `arity_0 = 1`, is a single proof's recursion.
pub mod aggregate {
    pub use crate::rec::tree::{
        CircuitStats, DensePoly, FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tree, TreeError, TreeProof,
        TreeShape, Unsatisfied,
    };
}
