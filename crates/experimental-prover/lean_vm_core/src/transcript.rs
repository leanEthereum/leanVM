//! The shared Fiat-Shamir transcript (see [`fiat_shamir`] for the state and
//! the prover's transport): the Keccak reduction's functions take this same `ps`
//! state, so the whole stack shares ONE transcript. Scalars ride its stream;
//! the stacked opening's Merkle data rides its opening phases.
pub use fiat_shamir::{FiatShamirState, Proof, RATE_SCALARS};
pub use primitives::transcript::ProverState;
