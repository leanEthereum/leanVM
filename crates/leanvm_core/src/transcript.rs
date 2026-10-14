//! The shared Fiat-Shamir transcript (see [`fiat_shamir`] for the state and
//! the wrapper states): the Keccak reduction's functions take these same `ps`/`vs`
//! states, so the whole stack shares ONE transcript. Scalars ride its stream;
//! the stacked opening's Merkle data rides its opening phases.
pub use fiat_shamir::transcript::{Challenger, Error, Receiver, Transmitter};
pub use fiat_shamir::{FiatShamirState, RATE_SCALARS};

pub type Proof = fiat_shamir::transcript::Proof;
pub type ProverState = fiat_shamir::transcript::ProverState;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a>;
