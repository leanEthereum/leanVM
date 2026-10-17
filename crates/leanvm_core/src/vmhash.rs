//! VM-provable hashing.
//!
//! The VM instruction exposes one step of the cell sponge
//! ([`primitives::hash::step`]) over a state held in memory, so a guest can run
//! [`primitives::hash::hash`] over any input: eight whole cells of message a
//! block, the padding placed by the program, the state carried between
//! instructions.

/// The hash of exactly 64 bytes (two 256-bit halves laid out little-endian), one
/// `SHA3` instruction from the zero state, which is also the PCS Merkle parent.
/// Lives in [`fiat_shamir`] (the shared [`fiat_shamir::FiatShamirState`] state is
/// built on it).
pub use fiat_shamir::compress;
