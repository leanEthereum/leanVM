//! leanVM: arithmetization of a minimal zkVM (see `doc/leanvm/main.tex`).
//!
//! Machine words, addresses, the pc, timestamps and read counters live in `K = GF(2^64)`.
//! What the machine computes with is an integer, read as the element with those bits;
//! what the proof system only ever steps (a timestamp, a read count) is a power of a
//! fixed generator `g`, so incrementing one is a multiplication by `g`, a free virtual
//! operation. Every physical witness column is K-valued and is committed directly by a
//! dense multilinear PCS.
//! Challenges and transcript scalars live in `E = GF(2^192)`, leaving ample margin
//! for 128-bit soundness.
//!
//! - [`transcript`]: the shared Fiat-Shamir transcript (re-exported from `fiat_shamir`).
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

pub mod class_flock;
pub mod colval;
pub mod constraints;
pub mod cpu;
pub mod gkr;
pub mod leaf;
pub mod pcs;
pub mod rv;
pub mod tables;
pub mod transcript;
pub mod witness;

/// Prepare the process for proving: the worker pool ([`init_prover_pool`]) plus
/// the proving arena ([`zk_alloc::enable_arena`]), which recycles the prover's
/// large transient buffers across proofs instead of re-faulting them.
///
/// Call once at program or test start.
///
/// Call [`init_prover_pool`] alone on a host where even the arena's recycled peak
/// does not fit: every [`ArenaVec`](zk_alloc::ArenaVec) then falls back to the
/// system allocator, which is slower where the arena fits, since the arena's
/// pages stay faulted in across proofs.
///
/// # Contract
/// The arena has one region per process, so two proofs must never run
/// concurrently in one process; [`zk_alloc::enter_phase`] asserts this. Use
/// separate processes to parallelize across proofs.
pub fn init_prover() {
    init_prover_pool();
    zk_alloc::enable_arena();
}

/// Spawn the worker pool up front, so no kernel pays the spawn cost inside a
/// timed region. Idempotent.
///
/// Thread placement is the pool's own business: performance-core workers run at
/// `USER_INTERACTIVE` and (on Apple silicon) efficiency-core workers at `UTILITY`,
/// all drawing from one claim counter. `LEANVM_NUM_THREADS` sets the
/// performance-worker count. See the `parallel` crate.
pub fn init_prover_pool() {
    parallel::init();
}

/// Target soundness of the whole proof, in bits. Every algebraic challenge is
/// sampled in F192, and the PCS derives a WHIR configuration whose query,
/// proximity-gap, and OOD-binding terms each clear this target.
pub const SECURITY_BITS: u32 = 128;

/// Below this many parallelizable items a pass runs serially: the fan-out
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// Run one prover stage inside its `tracing` span and, under `LEANVM_PROFILE`,
/// report its wall time. Called through [`stage!`], which spells the stage's name
/// once for both.
pub(crate) fn stage_impl<T>(name: &str, span: tracing::Span, f: impl FnOnce() -> T) -> T {
    static PROFILE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let t = std::time::Instant::now();
    let out = span.in_scope(f);
    if *PROFILE.get_or_init(|| std::env::var_os("LEANVM_PROFILE").is_some()) {
        eprintln!("[profile] {name:<20}: {:>8.2} ms", t.elapsed().as_secs_f64() * 1e3);
    }
    out
}

/// `stage!("Commit", || …)`: one named prover stage, a `tracing` span plus an
/// optional `LEANVM_PROFILE` timing line. A disabled span carries no metadata, so
/// the name has to travel separately from `info_span!`.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        $crate::stage_impl($name, tracing::info_span!($name), $f)
    };
}
pub(crate) use stage;

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};
