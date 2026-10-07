//! leanVM: the arithmetization of a RISC-V (rv64im) zkVM (see `doc/leanvm/main.tex`).
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
/// `stage!("Commit", || …)`: one named prover stage, run inside its `tracing` span,
/// which is what the CLI's `--tracing` tree shows.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

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

pub use self::pcs::{InvalidRate, Rate};
/// The shared soundness target of the commitment and the bus argument, in bits.
pub use ::pcs::whir::SECURITY_BITS;
pub use cpu::{DecodeError, Output, Program, Proof, ProveError, ProvenRun, Prover, Stats, VerifyError};
pub use rec::tree::{
    CircuitStats, DensePoly, FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tree, TreeError, TreeProof,
    TreeShape, Unsatisfied,
};
pub use rv::{ElfError, ProgramError, Region, Trap, asm};

#[doc(hidden)]
pub use self::pcs::{MAX_MU, MIN_MU};
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
pub use tables::{BAD_SLOT, Clock, EXIT_SLOT, Fill, N_TABLES, PerTable, TableId};

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
