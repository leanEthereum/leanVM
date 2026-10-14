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
//! A plain proof hides nothing: a verifier who guesses the advice can recompute the proof and compare.
//!
//! A prover made zero knowledge proves the same statement and reveals nothing of the advice or the run beyond its shape.
//!
//! - The shape is each table's height and the rate.
//! - A program whose advice is private must therefore prove at a fixed public shape.
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
//! The modules:
//!
//! - `stacking`: `K`-valued columns stacked into one committed witness.
//! - `commitment`: that witness committed in `K` and opened in `E`, via the stacked WHIR (§sec:stacking, §annex:pcs).
//! - `gkr`: the grand product via GKR (§sec:gkr), which balances the bus.
//! - `bus`: the shared bus, its balance decomposed into per-column claims (§sec:gp through §sec:leafstack, §sec:omc).
//! - `constraints`: one table sumcheck over every table's bus forms, the extension-field identities and the lookup producers (§sec:air).
//! - `rv`: RISC-V (rv64im): the decoder, each instruction class's function and circuit, and the reference interpreter.
//! - `tables`: the instruction tables, one per class: columns, bus tuples, circuits and their packed witnesses.
//! - `cpu`: whole-program assembly and the prove and verify entry points.
//! - `rec`: the recursion machine and the aggregation trees (§annex:rec).

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};

mod bus;
mod commitment;
mod constraints;
mod cpu;
mod envelope;
mod gkr;
mod rec;
mod rv;
mod stacking;
mod tables;

pub use commitment::{InvalidRate, Rate, SECURITY_BITS};
pub use cpu::{DecodeError, Output, Program, Proof, ProveError, ProvenRun, Prover, Stats, VerifyError};
#[doc(hidden)]
pub use rec::tree::{
    Aggregate, Capacity, CircuitStats, Claim, ClaimGroup, ClaimLeaf, ClaimSet, ClaimSetError, ClaimShape, DensePoly,
    FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tier, Tree, TreeError, TreeProof, TreeShape, Unsatisfied,
};
pub use rv::{ElfError, ProgramError, Region, Trap, asm};
pub use zk::Randomness;

#[doc(hidden)]
pub use bus::{BusError, N_TUPLE_BITS};
#[doc(hidden)]
pub use commitment::{MAX_MU, MIN_MU};
#[doc(hidden)]
pub use constraints::ConstraintError;
#[doc(hidden)]
pub use cpu::{CpuError, DeferredClaims, Lookup, MAX_LOG_ROWS, MalformedClaim, Q_BASE, UNGROUND_LOG_BYTECODE};
#[doc(hidden)]
pub use rv::{Alu, Class, Guest, Hash, Machine, Reg, RegisterFile, Syscall};
#[doc(hidden)]
pub use tables::{
    BAD_SLOT, CircuitId, Clock, EXIT_SLOT, Fill, MIN_CUBE_LOG, N_CIRCUITS, N_TABLES, PerTable, TableId, Word,
};

/// The instruction tables' flush plans, slot lists and clock-port bindings for the Lean checker.
#[cfg(feature = "circuit-trace")]
#[doc(hidden)]
pub fn table_flushes() -> String {
    tables::ClassTable::flush_dump()
}

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
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`bus`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// Aggregation trees: many proofs of one program, verified as one.
///
/// # Overview
///
/// ```text
///                 node                  verifies tree proofs, of any kind
///               /      \
///        first-level   first-level      each verifies `arity_0` proofs of the program
///          /  \          /  \
///       leaf  leaf    leaf  leaf
/// ```
///
/// Every tree proof states the same few hundred words:
///
/// - a digest: of its leaves' outputs in a tree of outputs, of the claim set it declares in a claim-set tree,
/// - claims that only the root's verifier evaluates.
///
/// A tree of outputs has one node arity, and its root states its leaves' outputs in order. A claim-set tree
/// ([`TreeShape::claims`]) has nodes of every arity up to its largest: anyone combines any of its proofs
/// ([`Tree::aggregate`]), each node declaring the union of its children's claim sets or part of it, and its root states a
/// canonical claim set ([`Tree::verify_claims`]). A leaf program publishes the claims it checked (a [`ClaimSet`]: groups
/// of 6-word labels and 4-word members, whose meaning is the program's), its output the hash of the set's digest.
///
/// A tree over one leaf, with `arity_0 = 1`, is a single proof's recursion.
pub mod aggregate {
    pub use crate::rec::tree::{
        Aggregate, Capacity, CircuitStats, Claim, ClaimGroup, ClaimLeaf, ClaimSet, ClaimSetError, ClaimShape,
        DensePoly, FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tier, Tree, TreeError, TreeProof, TreeShape,
        Unsatisfied,
    };
}
