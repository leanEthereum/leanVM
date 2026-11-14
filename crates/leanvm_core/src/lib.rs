//! leanVM: arithmetization of a minimal zkVM (see `doc/leanvm/main.tex`).
//!
//! Machine words are `c0 + c1*y ∈ E = K[y]/(y² + x*y + 1)`.
//! Addresses, pc/fp, read counters, and logical indices live in
//! `K = GF(2^64)`; indices are powers of a fixed generator `g`, so incrementing
//! one is a multiplication by `g`, a free virtual operation. Every physical
//! witness column is K-valued (an E-valued word is two K-lane columns) and is
//! committed directly by a dense multilinear PCS. Challenges and transcript
//! scalars live in `E = GF(2^128)`.
//!
//! - [`transcript`]: the shared Fiat-Shamir transcript (re-exported from `fiat_shamir`).
//! - [`pcs`]: `K`-committed witness, `E`-opened, via the stacked WHIR (§sec:stacking, §annex:pcs).
//! - [`witness`]: `K`-valued columns stacked into one committed witness.
//! - [`gkr`]: the grand product via GKR (§sec:gkr), balancing the bus.
//! - [`leaf`]: the shared bus: grand-product balance, decomposed to per-column claims (§sec:gp through §sec:leafstack, §sec:omc).
//! - [`constraints`]: one table sumcheck over all six tables'
//!   degree-2 identities plus their bus forms, one per bus tree (§sec:air).
//! - [`tables`]: the six instruction tables (columns, flushes, constraints).
//! - [`cpu`]: whole-program assembly, control flow, and the prove/verify entry points.
//! - [`keccak`]: the `KECCAK` glue: the Keccak GKR reduction over the same commitment.
//! - [`vmhash`]: VM-native hashing (the one-block hash every Merkle node uses).

pub mod constraints;
pub mod cpu;
pub mod gkr;
pub mod keccak;
pub mod leaf;
pub mod pcs;
pub mod tables;
pub mod transcript;
pub mod vmhash;
pub mod witness;

/// Prepare the process for proving: spawn the worker pool up front, so no kernel
/// pays the spawn cost inside a timed region. Idempotent.
///
/// Thread placement is the pool's own business: performance-core workers run at
/// `USER_INTERACTIVE` and (on Apple silicon) efficiency-core workers at `UTILITY`,
/// all drawing from one claim counter. `LEANVM_NUM_THREADS` sets the
/// performance-worker count. See the `parallel` crate.
pub fn init_prover() {
    parallel::init();
}

/// Whether the prover's own consistency checks on its witness apply: always, but under the fuzzer's `fuzzing` feature
/// not once it has handed the witness to an edit ([`cpu::tamper`]), so a malicious prover's proof reaches the verifier.
#[inline]
pub(crate) fn witness_is_honest() -> bool {
    #[cfg(feature = "fuzzing")]
    return !cpu::tamper::tampered();
    #[cfg(not(feature = "fuzzing"))]
    true
}

/// Target soundness in bits: every verifier message's round-by-round error, after its grind, is at
/// most `2^-SECURITY_BITS`. Challenges are sampled in F128, so a message whose error is `N/|E|`
/// grinds `fiat_shamir::grinding_bits(N)` bits.
pub use fiat_shamir::SECURITY_BITS;

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
