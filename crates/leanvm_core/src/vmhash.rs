//! VM-provable hashing.
//!
//! The VM instruction is Keccak-f\[1600\] of a state held in memory, so a guest can
//! run [`primitives::hash::hash`] over any input: 136 bytes of message a block,
//! eight and a half cells XORed into the state, the padding placed by the program,
//! the state carried between instructions.

/// The hash of exactly 64 bytes (two 256-bit halves laid out little-endian), one
/// `KECCAK` instruction from the zero state, which is also the PCS Merkle parent.
/// Lives in [`fiat_shamir`] (the shared [`fiat_shamir::FiatShamirState`] state is
/// built on it).
pub use fiat_shamir::compress;
