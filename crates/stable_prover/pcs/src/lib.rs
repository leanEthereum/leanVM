// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The stable prover's polynomial commitment (Annex B): the additive NTT, Merkle trees, ring switching and the
//! stacked WHIR opening. A stack of `K = GF(2^64)` words, each packing 64 witness bits, is committed and opened over
//! `E = GF(2^128)`.

pub mod merkle;
pub mod ntt;
mod ring_switch;
mod stack_open;
pub mod sumcheck;
pub mod whir;
mod whir_induce;
mod whir_lanes;
mod xmul;

// Merkle leaves and the ring switch read words as their bytes, which are the little-endian ones the verifier hashes.
const _: () = assert!(cfg!(target_endian = "little"));

pub use stack_open::{Committed, RingSwitchOpen, StackClaim, commit, open};

/// `len` values written by the pool `N` at a time, `chunk(k)` giving values `N k..N k + N`, those past `len` dropped.
fn collect_chunks<T: Send, const N: usize>(len: usize, chunk: impl Fn(usize) -> [T; N] + Sync) -> Vec<T> {
    let mut v = parallel::map_collect(len.div_ceil(N), chunk).into_flattened();
    v.truncate(len);
    v
}
