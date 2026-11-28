//! leanVM's arithmetization and its prover (`doc/leanvm/main.tex`), the stable tree's.
//!
//! Machine words are `c0 + c1·y ∈ E = K[y]/(y² + x·y + 1)`. Addresses, `pc` and `fp` live in `K = GF(2^64)` as powers
//! of a fixed generator `g`, so an increment is a free multiplication by `g`. Every committed column is `K`-valued (a
//! word is two columns); challenges and transcript scalars are in `E`.
//!
//! A proof ([`cpu::prove`]) runs the program, commits every column in one stacked witness ([`witness`], [`pcs`]),
//! then proves:
//! - [`link`]: Hotwire, the one-hot pointer links between the tables, the memory and the program, and `JUMP`'s
//!   identities, by two chained sum-checks, over the index and over the rows;
//! - [`keccak`]: the `KECCAK` steps, by the Keccak reduction over the same commitment;
//! - and opens every claim in one stacked WHIR ([`pcs`]).
//!
//! [`tables`] declares the six instruction tables, [`cpu`] the whole program's layout, execution and witness.

pub mod cpu;
pub mod form;
pub mod keccak;
pub mod link;
pub mod pcs;
mod prover;
pub mod tables;
pub mod witness;

pub use prover::StableProver;

/// `stage!("Commit", || …)`: one named prover stage, run inside its `tracing` span, which is what the CLI's
/// `--tracing` tree shows.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};
