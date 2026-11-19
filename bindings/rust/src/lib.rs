#![doc = include_str!("../README.md")]

mod aggregate;
mod error;
pub mod sphincs;
pub mod vrf;
pub mod xmss;

pub use aggregate::{Aggregate, Sidecar, MAX_CHILDREN};
pub use error::{Encoding, Error};

/// Byte length of a message, the 256-bit digest both schemes sign.
///
/// Hash a longer message to 32 bytes before signing it.
pub const MESSAGE_LEN: usize = 32;

/// Byte length of a public key in both schemes.
///
/// Both keys are a 16-byte Merkle root and a 16-byte public parameter, in each scheme's own
/// order: leanXMSS encodes the root first, leanSPHINCS its `PK.seed` first, as FIPS 205 does.
pub const PUBLIC_KEY_LEN: usize = 32;

/// A message both schemes sign.
pub type Message = [u8; MESSAGE_LEN];

/// A fresh 32-byte seed from the operating system's randomness.
///
/// # Panics
///
/// Panics when the operating system cannot supply randomness.
fn random_seed() -> [u8; 32] {
    let mut seed = [0; 32];
    getrandom::fill(&mut seed).expect("the operating system's randomness is unavailable");
    seed
}
