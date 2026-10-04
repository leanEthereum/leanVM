//! leanVM: arithmetization of a minimal zkVM (see `doc/leanvm/main.tex`).
//!
//! Machine words, addresses, the pc and timestamps live in `K = GF(2^64)`.
//! What the machine computes with is an integer, read as the element with those bits;
//! what the proof system only ever steps (a timestamp) is a power of a
//! fixed generator `g`, so incrementing one is a multiplication by `g`, a free virtual
//! operation. Every physical witness column is K-valued and is committed directly by a
//! dense multilinear PCS.
//! Challenges and transcript scalars live in `E = GF(2^192)`, leaving ample margin
//! for 128-bit soundness.
//!
//! - [`pcs`]: `K`-committed witness, `E`-opened, via the stacked WHIR (§sec:stacking, §annex:pcs).
//! - [`witness`]: `K`-valued columns stacked into one committed witness.
//! - [`gkr`]: the grand product via GKR (§sec:gkr), balancing the bus.
//! - [`leaf`]: the shared bus: grand-product balance, decomposed to per-column claims (§sec:gp through §sec:leafstack, §sec:omc).
//! - [`constraints`]: one table sumcheck over all the tables'
//!   degree-2 identities plus their three bus forms (§sec:air).
//! - [`rv`]: RISC-V (rv64im): the decoder, each instruction class's function and circuit, and the reference interpreter.
//! - [`tables`]: the instruction tables, one per class (columns, flushes, constraints).
//! - [`class_flock`]: the glue to flock: a class's circuit proven over its own packed witness, in the same commitment.
//! - [`cpu`]: whole-program assembly and the prove/verify entry points.

pub mod arith;
pub mod class_flock;
pub mod colval;
pub mod constraints;
pub mod cpu;
pub mod gkr;
pub mod leaf;
pub mod pcs;
pub mod rec;
pub mod rv;
pub mod tables;
pub mod witness;

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

/// Target soundness of the whole proof, in bits. Every algebraic challenge is
/// sampled in F192, and the PCS derives a WHIR configuration whose query,
/// proximity-gap, and OOD-binding terms each clear this target.
pub const SECURITY_BITS: u32 = 128;

/// Below this many parallelizable items a pass runs serially: the fan-out
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// `stage!("Commit", || …)`: one named prover stage, run inside its `tracing` span,
/// which is what the CLI's `--tracing` tree shows.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};
