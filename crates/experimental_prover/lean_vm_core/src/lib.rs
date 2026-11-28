//! leanVM: arithmetization of a minimal zkVM (see `doc/leanvm/main.tex`).
//!
//! Machine words are `c0 + c1*y ∈ E = K[y]/(y² + x*y + 1)`.
//! Addresses, pc/fp, and logical indices live in
//! `K = GF(2^64)`; indices are powers of a fixed generator `g`, so incrementing
//! one is a multiplication by `g`, a free virtual operation. Every physical
//! witness column is K-valued (an E-valued word is two K-lane columns) and is
//! committed directly by a dense multilinear PCS. Challenges and transcript
//! scalars live in `E = GF(2^128)`.
//!
//! - [`pcs`]: `K`-committed witness, `E`-opened, via the stacked WHIR (§sec:stacking, §annex:pcs).
//! - [`witness`]: `K`-valued columns stacked into one committed witness.
//! - [`form`]: the forms the tables' links are written in, and the claims on their columns.
//! - [`link`]: Hotwire, one-hot pointer links and the tables' identities checked by sum-checks.
//! - [`tables`]: the six instruction tables (columns, links, constraints).
//! - [`cpu`]: whole-program assembly, control flow, and the prove/verify entry points.
//! - [`keccak`]: the `KECCAK` glue: the Keccak GKR reduction over the same commitment.

pub mod cpu;
pub mod form;
pub mod keccak;
pub mod link;
pub mod pcs;
mod prover;
pub mod tables;
pub mod witness;

/// Target soundness in bits: every verifier message's round-by-round error, after its grind, is at
/// most `2^-SECURITY_BITS`. Challenges are sampled in F128, so a message whose error is `N/|E|`
/// grinds `fiat_shamir::grinding_bits(N)` bits.
pub use fiat_shamir::SECURITY_BITS;
pub use prover::ExperimentalProver;

/// Whether `scripts/tier-rustc` compiled this copy with a CPU tier's target features (`crates/experimental_tiers`).
#[doc(hidden)]
pub const __TIER: bool = cfg!(leanvm_tier);

/// `stage!("Commit", || …)`: one named prover stage, run inside its `tracing` span,
/// which is what the CLI's `--tracing` tree shows.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};
