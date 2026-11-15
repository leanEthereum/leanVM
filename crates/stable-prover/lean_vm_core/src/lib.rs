//! leanVM's arithmetization and its prover (`doc/leanvm/main.tex`), the stable tree's.
//!
//! Machine words are `c0 + c1·y ∈ E = K[y]/(y² + x·y + 1)`. Addresses, `pc`/`fp`, access counts and row indices
//! live in `K = GF(2^64)` as powers of a fixed generator `g`, so an increment is a free multiplication by `g`. Every
//! committed column is `K`-valued (a word is two columns); challenges and transcript scalars are in `E`.
//!
//! A proof ([`cpu::prove`]) runs the program, commits every column in one stacked witness ([`witness`], [`pcs`]),
//! then proves:
//! - [`leaf`]: the bus balances, by one batched grand product ([`gkr`]) whose leaf claims split into column claims
//!   and one degree-two form per table (§sec:gp to §sec:leafstack);
//! - [`constraints`]: one sumcheck over every table for its identities and its bus forms (§sec:air);
//! - [`keccak`]: the `KECCAK` steps, by the Keccak reduction over the same commitment;
//! - and opens every claim in one stacked WHIR ([`pcs`]).
//!
//! [`tables`] declares the six instruction tables, [`cpu`] the whole program's layout, execution and witness.

pub mod constraints;
pub mod cpu;
mod eq;
pub mod gkr;
pub mod keccak;
pub mod leaf;
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

use primitives::field::{F64, F64x8, F128, F128x8};

/// Vectors of eight rows below which a pass runs on the calling thread: waking the pool would cost more than it
/// saves, and a proof makes many such passes (the GKR's and the table sumcheck's last rounds, the small tables).
const SERIAL_BELOW: usize = 1 << 10;

/// Vectors of eight rows per task of a pass over `n` of them: one task for a small pass, which the pool then runs on
/// the calling thread.
pub(crate) fn chunk(n: usize) -> usize {
    if n < SERIAL_BELOW { n.max(1) } else { 1 << 7 }
}

/// `n` copies of `value`, written by the pool only when the buffer is large.
pub(crate) fn filled<T: Copy + Send + Sync>(n: usize, value: T) -> Vec<T> {
    if n < 8 * SERIAL_BELOW {
        vec![value; n]
    } else {
        parallel::filled(n, value)
    }
}

/// `values[i..i + n]` as lanes, zero past `n` (`n` at least eight takes eight).
#[inline(always)]
pub(crate) fn load_k(values: &[F64], i: usize, n: usize) -> F64x8 {
    if n >= 8 {
        F64x8::load(&values[i..i + 8])
    } else {
        F64x8::from_array(&std::array::from_fn(|p| if p < n { values[i + p] } else { F64::ZERO }))
    }
}

/// `values[i..i + n]` as lanes, zero past `n` (`n` at least eight takes eight).
#[inline(always)]
pub(crate) fn load_e(values: &[F128], i: usize, n: usize) -> F128x8 {
    if n >= 8 {
        F128x8::load(&values[i..i + 8])
    } else {
        F128x8::from_array(&std::array::from_fn(|p| if p < n { values[i + p] } else { F128::ZERO }))
    }
}
