//! Keccak-256, the repo's one hash function: the shared [`keccak256`] crate, whose batched forms permute
//! [`LANES`](keccak256::LANES) states at once in vector registers.

pub use keccak256::*;
