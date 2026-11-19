//! leanSPHINCS: a stateless hash-based signature.
//!
//! Normative source: the leanSPHINCS specification, `doc/lean_sphincs/`, which follows the
//! layout of FIPS 205 (SLH-DSA) with Keccak-256 as the hash.
//!
//! ```text
//!     hash         Keccak-256, truncated to n = 16 bytes
//!     few-time     FORS: 24 trees of height 10 sign the message
//!     one-time     WOTS+C: w = 2, v = 64 chains, digit sum T = 128
//!     hypertree    three layers of WOTS+C trees, heights 8, 8 and 10 from the bottom,
//!                  sign the FORS key up to the public key
//!     lifetime     at most 2^30 messages per key
//!     verify       515 Keccak permutations
//! ```
//!
//! The message digest picks the FORS instance and its leaves, so no state is kept between
//! signatures.
//!
//! - The secret key is one 32-byte seed, all of the key.
//! - Key generation builds the top tree to get the public key.
//! - Signing builds the FORS instance and the three trees on the way up.

use std::fmt;

use lean_sphincs::{
    key_gen, sign as sphincs_sign, verify as sphincs_verify, LeanSphincsPublicKey,
    LeanSphincsSignature, SecretKey as UpstreamSecretKey, PUB_KEY_SIZE,
    SECRET_KEY_LEN as UPSTREAM_SECRET_KEY_LEN, SIG_SIZE,
};

use crate::{Encoding, Error, Message, PUBLIC_KEY_LEN};

/// Byte length of a seed, which derives `PK.seed`, `SK.prf` and every secret.
pub const SEED_LEN: usize = 32;

/// Byte length of an encoded secret key, which is its seed.
pub const SECRET_KEY_LEN: usize = SEED_LEN;

/// Byte length of an encoded signature.
///
/// ```text
///     randomizer        16
///     FORS openings   4224 = 24 trees * (secret 16 + 10 path nodes * 16)
///     bottom layer    1156 = counter 4 + 64 chain values * 16 + 8 path nodes * 16
///     middle layer    1156   same layout
///     top layer       1188 = counter 4 + 64 chain values * 16 + 10 path nodes * 16
///     total           7740
/// ```
pub const SIGNATURE_LEN: usize = 7740;

/// The seed a key is derived from.
pub type Seed = [u8; SEED_LEN];

// The sizes and types above are `lean_sphincs`'s.
const _: () = assert!(SEED_LEN == UPSTREAM_SECRET_KEY_LEN);
const _: () = assert!(SIGNATURE_LEN == SIG_SIZE);
const _: () = assert!(PUBLIC_KEY_LEN == PUB_KEY_SIZE);
const _: fn(UpstreamSecretKey) -> Seed = |seed| seed;

/// A leanSPHINCS public key: `PK.seed`, the public parameter every hash is keyed with, and
/// `PK.root`, the root of the top tree.
///
/// Keys order by their encoded bytes, the order aggregate claims are sorted in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PublicKey(pub(crate) LeanSphincsPublicKey);

impl PublicKey {
    /// Decodes a public key.
    ///
    /// Every 32-byte string is a well-formed key.
    ///
    /// # Errors
    ///
    /// Fails when the input is not 32 bytes long.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let array = bytes.try_into().map_err(|_| Error::InvalidLength {
            encoding: Encoding::SphincsPublicKey,
            expected: PUBLIC_KEY_LEN,
            actual: bytes.len(),
        })?;
        Ok(Self(LeanSphincsPublicKey::from_bytes(array)))
    }

    /// Encodes the key as `PK.seed` followed by `PK.root`, the order of FIPS 205.
    #[must_use]
    pub fn to_bytes(&self) -> [u8; PUBLIC_KEY_LEN] {
        self.0.to_bytes()
    }

    /// Checks a signature of a message under this key.
    ///
    /// # Errors
    ///
    /// Fails when the signature does not verify.
    pub fn verify(&self, message: &Message, signature: &Signature) -> Result<(), Error> {
        if sphincs_verify(&self.0, message, &signature.0) {
            Ok(())
        } else {
            Err(Error::SphincsVerify)
        }
    }
}

/// A leanSPHINCS secret key.
///
/// Its memory is not zeroized on drop.
pub struct SecretKey {
    /// The seed, all of the key.
    seed: Seed,
    /// The public key, kept because rebuilding it builds the whole top tree.
    public_key: LeanSphincsPublicKey,
}

impl SecretKey {
    /// Generates a key from the operating system's randomness.
    ///
    /// # Panics
    ///
    /// Panics when the operating system cannot supply randomness.
    #[must_use]
    pub fn generate() -> Self {
        Self::from_seed(crate::random_seed())
    }

    /// Derives a key from its seed, deterministically.
    ///
    /// The seed is the whole secret.
    #[must_use]
    pub fn from_seed(seed: Seed) -> Self {
        let public_key = key_gen(&seed);
        Self { seed, public_key }
    }

    /// Decodes a key from its 32-byte seed.
    ///
    /// # Errors
    ///
    /// Fails when the input is not 32 bytes long.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let seed = bytes.try_into().map_err(|_| Error::InvalidLength {
            encoding: Encoding::SphincsSecretKey,
            expected: SECRET_KEY_LEN,
            actual: bytes.len(),
        })?;
        Ok(Self::from_seed(seed))
    }

    /// Encodes the key as its seed.
    ///
    /// The bytes are secret key material.
    #[must_use]
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_LEN] {
        self.seed
    }

    /// Returns the key's public key.
    #[must_use]
    pub fn public_key(&self) -> PublicKey {
        PublicKey(self.public_key)
    }

    /// Signs a message.
    ///
    /// Signing is deterministic: the randomizer derives from the seed and the message.
    ///
    /// # Panics
    ///
    /// Panics when every encoding counter of a layer misses a codeword, which happens with
    /// probability below `2^-378193`.
    #[must_use]
    pub fn sign(&self, message: &Message) -> Signature {
        Signature(sphincs_sign(&self.seed, message))
    }
}

impl fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Only public data: the seed must never reach a log.
        f.debug_struct("SecretKey")
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

/// A leanSPHINCS signature.
#[derive(Clone, PartialEq, Eq)]
pub struct Signature(pub(crate) LeanSphincsSignature);

impl Signature {
    /// Decodes a signature.
    ///
    /// Every 7740-byte string decodes, and re-encodes to the same bytes.
    ///
    /// # Errors
    ///
    /// Fails when the input is not 7740 bytes long.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let array = bytes.try_into().map_err(|_| Error::InvalidLength {
            encoding: Encoding::SphincsSignature,
            expected: SIGNATURE_LEN,
            actual: bytes.len(),
        })?;
        Ok(Self(LeanSphincsSignature::from_bytes(array)))
    }

    /// Encodes the signature.
    #[must_use]
    pub fn to_bytes(&self) -> [u8; SIGNATURE_LEN] {
        self.0.to_bytes()
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 7740 bytes would drown a log line.
        f.debug_struct("Signature").finish_non_exhaustive()
    }
}
