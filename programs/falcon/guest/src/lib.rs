//! Falcon-512 signature verification, as the round-3 specification ([Falcon]) defines it.
//!
//! A signature on a message `m` is a 40-byte nonce `r` and a short polynomial `s2`.
//!
//! It is valid when `s1 = c - s2 * h` is short too:
//!
//! ```text
//!   c   = HashToPoint(SHAKE256(r || m))       the message, as a polynomial mod q
//!   s1  = c - s2 * h  in Z_q[x] / (x^512 + 1)  h the public key
//!   accept  iff  ||s1||^2 + ||s2||^2 <= 34034726
//! ```
//!
//! Verification is integer-only: the floating point of Falcon lives in signing, which the host does.
//!
//! Values are 64-bit words, as the machine loads them:
//!
//! - the bit-packed encodings (the key's `h`, the signature's compressed `s2`) are big-endian words;
//! - the bytes SHAKE256 absorbs (the nonce, the message) are little-endian words, its lanes.
//!
//! Either way a word's bytes are the specification's, in order.
//!
//! [Falcon]: https://falcon-sign.info/falcon.pdf
#![no_std]
use thiserror::Error;

mod codec;
pub mod ntt;
mod shake;

pub use shake::Shake256;

/// The ring degree: polynomials mod `x^512 + 1`.
pub const N: usize = 512;
/// The modulus: `12289 = 3 * 2^12 + 1`, so `Z_q` has the `1024`-th roots of unity the NTT needs.
pub const Q: i64 = 12289;
/// The bound on the squared norm of `(s1, s2)`: `floor(beta^2)` for Falcon-512.
pub const SIG_BOUND: i64 = 34_034_726;

/// Words of the key's encoding: 512 coefficients of 14 bits, 896 bytes.
pub const PUBLIC_KEY_WORDS: usize = N * 14 / 64;
/// Words of the nonce: 40 bytes.
pub const NONCE_WORDS: usize = 5;
/// Bytes of the compressed `s2`: a 666-byte signature less its header byte and nonce.
pub const BODY_BYTES: usize = 625;
/// Words holding the compressed `s2`, zero past its 625 bytes.
///
/// One more than the bytes need, so a 64-bit window at any bit of the body stays in it.
pub const BODY_WORDS: usize = BODY_BYTES.div_ceil(8) + 1;

/// A public key: the polynomial `h`, its coefficients packed 14 bits each, most significant bit first.
///
/// The encoding's header byte (`0x09`) is implied.
///
/// Its fields are words, so it has no padding and any 896 bytes are one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PublicKey {
    /// The 896 bytes after the header, as big-endian words.
    pub h: [u64; PUBLIC_KEY_WORDS],
}

/// A signature: its nonce, and `s2` compressed.
///
/// The encoding's header byte (`0x39`) is implied.
///
/// Its fields are words, so it has no padding and any 680 bytes are one.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Signature {
    /// The 40-byte nonce, as little-endian words.
    pub nonce: [u64; NONCE_WORDS],
    /// The 625 bytes of the compressed `s2`, as big-endian words, then zeros.
    pub body: [u64; BODY_WORDS],
}

/// The message signed, as little-endian words.
pub type Message = [u64; 4];

/// Why a signature is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum FalconVerifyError {
    /// A coefficient of `h` is not below `q`.
    #[error("a coefficient of the public key is not below q")]
    InvalidPublicKey,
    /// The compressed `s2` is not the canonical encoding of 512 coefficients in 625 bytes.
    #[error("the signature is not a canonical encoding")]
    InvalidEncoding,
    /// `(s1, s2)` is too long.
    #[error("the signature is not short enough")]
    TooLong,
}

/// Check a signature on a message.
///
/// One verification: `Verifier::verify` reuses its scratch space for many.
pub fn verify(pk: &PublicKey, message: &[u64], signature: &Signature) -> Result<(), FalconVerifyError> {
    Verifier::new().verify(pk, message, signature)
}

/// A verifier, and the three polynomials it works in.
///
/// Each verification overwrites them, so verifying many signatures zeroes them once.
pub struct Verifier {
    /// The public key's `h`, then its transform.
    h: [i64; N],
    /// The signature's `s2`, then `s2 * h`.
    s2: [i64; N],
    /// The message as a polynomial, `HashToPoint(r || m)`.
    c: [i64; N],
}

impl Verifier {
    /// A verifier, its polynomials zero.
    pub const fn new() -> Self {
        Self {
            h: [0; N],
            s2: [0; N],
            c: [0; N],
        }
    }

    /// Check a signature on a message.
    ///
    /// ```text
    ///   hash      c  = HashToPoint(r || m)          9 Keccak permutations, about
    ///   decode    h, s2                             from their packed words
    ///   multiply  s2 * h                            two forward NTTs, an inverse with the pointwise product
    ///   measure   ||c - s2 * h||^2 + ||s2||^2
    /// ```
    pub fn verify(&mut self, pk: &PublicKey, message: &[u64], signature: &Signature) -> Result<(), FalconVerifyError> {
        let Self { h, s2, c } = self;
        codec::decode_public_key(pk, h)?;
        let s2_norm = codec::decompress(&signature.body, s2)?;
        hash_to_point(&signature.nonce, message, c);

        // s1 = c - s2 * h, centered, and its norm.
        ntt::multiply(s2, h);
        let s1_norm: i64 = c
            .iter()
            .zip(s2.iter())
            .map(|(&c, &p)| {
                let s1 = ntt::sub_centered(c, p);
                s1 * s1
            })
            .sum();
        if s1_norm + s2_norm <= SIG_BOUND {
            Ok(())
        } else {
            Err(FalconVerifyError::TooLong)
        }
    }
}

impl Default for Verifier {
    fn default() -> Self {
        Self::new()
    }
}

/// `HashToPoint`: SHAKE256 of the nonce and the message, read as 16-bit big-endian samples.
///
/// A sample below `5q = 61445` is kept, the rest skipped, so each is uniform mod `q`.
///
/// The samples are left unreduced: `c` is only ever used mod `q`.
pub fn hash_to_point(nonce: &[u64; NONCE_WORDS], message: &[u64], c: &mut [i64; N]) {
    let mut sponge = Shake256::new();
    sponge.absorb(nonce);
    sponge.absorb(message);
    let mut squeeze = sponge.finalize();

    let mut i = 0;
    while i < N {
        // Each lane holds four samples, its bytes in order.
        //
        //     lane bytes   b0 b1 | b2 b3 | b4 b5 | b6 b7
        //     samples      b0 b1   b2 b3   b4 b5   b6 b7     each b_even * 256 + b_odd
        //
        // Swapping the bytes of each 16-bit half once makes every sample a plain shift.
        let lane = squeeze.next_lane();
        let swapped = ((lane & 0x00FF_00FF_00FF_00FF) << 8) | ((lane >> 8) & 0x00FF_00FF_00FF_00FF);
        for k in 0..4 {
            let w = ((swapped >> (16 * k)) & 0xFFFF) as i64;
            if w < 5 * Q {
                c[i] = w;
                i += 1;
                if i == N {
                    break;
                }
            }
        }
    }
}
