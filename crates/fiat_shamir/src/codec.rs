//! Codecs: how values become sponge bytes, and how sponge bytes become challenges.
//!
//! The three traits follow spongefish and `draft-irtf-cfrg-fiat-shamir`:
//!
//! - A prover message is encoded to bytes, absorbed, and written to the proof.
//! - The verifier reads those bytes back, refusing any that are not canonical.
//! - A verifier message is decoded from squeezed bytes, without bias.
//!
//! The sponge absorbs exactly the bytes the proof carries.
//!
//! So a value the verifier reads is always a value it binds.

use primitives::field::F192;

/// How a value enters the sponge, and the proof.
///
/// The encodings of one type must be prefix-free: no encoding starts another.
///
/// Every encoding here has a fixed length, which makes it prefix-free.
///
/// The recursive verifier absorbs whole 64-bit words.
/// So a message it replays must encode to a multiple of 8 bytes.
pub trait Encoding {
    /// The encoding's byte container: an array for a fixed length.
    type Bytes: AsRef<[u8]>;

    /// The value's bytes.
    fn encode(&self) -> Self::Bytes;
}

/// How a value is read back from the proof.
///
/// Reading inverts encoding, and refuses bytes no value encodes.
///
/// So every value has exactly one encoding in a proof.
pub trait FromNarg: Encoding + Sized {
    /// Read one value off the front of `narg`, advancing it.
    ///
    /// Returns nothing when `narg` is too short or holds no canonical encoding.
    fn from_narg(narg: &mut &[u8]) -> Option<Self>;
}

/// How a verifier message is drawn from uniform sponge bytes.
///
/// The value must be uniform, or within the statistical distance the protocol budgets for.
///
/// Every implementation here is a bijection, so its draw is exactly uniform.
pub trait FromUniform: Sized {
    /// The squeezed bytes one value takes.
    type Repr: Default + AsMut<[u8]>;

    /// The value these uniform bytes give.
    fn from_uniform(repr: Self::Repr) -> Self;
}

/// An element of `E = GF(2^192)`: its three coordinates, lowest first, each eight little-endian bytes.
impl Encoding for F192 {
    type Bytes = [u8; 24];

    fn encode(&self) -> [u8; 24] {
        let mut bytes = [0u8; 24];
        for (slot, limb) in bytes.as_chunks_mut::<8>().0.iter_mut().zip([self.c0, self.c1, self.c2]) {
            *slot = limb.to_le_bytes();
        }
        bytes
    }
}

impl FromNarg for F192 {
    fn from_narg(narg: &mut &[u8]) -> Option<Self> {
        // Every 24-byte string is an element, so only a short proof is refused.
        let [c0, c1, c2] = limbs(take::<24>(narg)?);
        Some(Self::new(c0, c1, c2))
    }
}

/// A uniform element of `E`.
///
/// Why unbiased: the 24 bytes map to the element bijectively, as `E` has `2^192` elements.
impl FromUniform for F192 {
    type Repr = [u8; 24];

    fn from_uniform(repr: [u8; 24]) -> Self {
        // The layout of a message: three little-endian limbs, lowest first.
        let [c0, c1, c2] = limbs(&repr);
        Self::new(c0, c1, c2)
    }
}

/// A fixed-length byte string, such as a digest, sent as itself.
impl<const N: usize> Encoding for [u8; N] {
    type Bytes = Self;

    fn encode(&self) -> Self {
        *self
    }
}

impl<const N: usize> FromNarg for [u8; N] {
    fn from_narg(narg: &mut &[u8]) -> Option<Self> {
        take::<N>(narg).copied()
    }
}

/// Uniform bytes, such as a proof-of-work challenge.
impl<const N: usize> FromUniform for [u8; N]
where
    Self: Default,
{
    type Repr = Self;

    fn from_uniform(repr: Self) -> Self {
        repr
    }
}

/// A 64-bit integer, such as a proof-of-work nonce: eight little-endian bytes.
impl Encoding for u64 {
    type Bytes = [u8; 8];

    fn encode(&self) -> [u8; 8] {
        self.to_le_bytes()
    }
}

impl FromNarg for u64 {
    fn from_narg(narg: &mut &[u8]) -> Option<Self> {
        take::<8>(narg).map(|bytes| Self::from_le_bytes(*bytes))
    }
}

/// A fixed number of values, one after another.
///
/// The count is the type's, so the encoding stays fixed-length.
impl<T: Encoding, const N: usize> Encoding for [T; N] {
    type Bytes = Vec<u8>;

    fn encode(&self) -> Vec<u8> {
        self.iter().flat_map(|x| x.encode().as_ref().to_vec()).collect()
    }
}

/// A list of values whose count varies, its count first.
///
/// The count makes lists of different lengths prefix-free.
///
/// It takes eight little-endian bytes, where spongefish takes four.
/// Why: every encoding then stays a whole number of 64-bit words, which the recursive verifier absorbs.
pub struct LengthPrefixed<'a, T>(pub &'a [T]);

impl<T: Encoding> Encoding for LengthPrefixed<'_, T> {
    type Bytes = Vec<u8>;

    fn encode(&self) -> Vec<u8> {
        let mut bytes = (self.0.len() as u64).to_le_bytes().to_vec();
        for x in self.0 {
            bytes.extend_from_slice(x.encode().as_ref());
        }
        bytes
    }
}

/// The first `N` bytes of `narg`, which advances past them.
fn take<'a, const N: usize>(narg: &mut &'a [u8]) -> Option<&'a [u8; N]> {
    let (head, rest) = narg.split_first_chunk::<N>()?;
    *narg = rest;
    Some(head)
}

/// Three little-endian 64-bit limbs, lowest first.
fn limbs(bytes: &[u8; 24]) -> [u64; 3] {
    let (chunks, _) = bytes.as_chunks::<8>();
    std::array::from_fn(|i| u64::from_le_bytes(chunks[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn a_field_element_round_trips_through_the_proof(c0: u64, c1: u64, c2: u64, tail: Vec<u8>) {
            // Encode an element, append unrelated bytes, read it back.
            //
            //     narg = [24 element bytes | tail]
            //     -> the element, and the cursor left on the tail
            let x = F192::new(c0, c1, c2);
            let narg = [&x.encode()[..], &tail].concat();
            let mut cursor = narg.as_slice();
            prop_assert_eq!(F192::from_narg(&mut cursor), Some(x));
            prop_assert_eq!(cursor, tail.as_slice());
        }

        #[test]
        fn a_field_challenge_inverts_the_encoding(repr: [u8; 24]) {
            // The challenge map is the inverse of the encoding, hence a bijection.
            let x = F192::from_uniform(repr);
            prop_assert_eq!(x.encode(), repr);
        }

        #[test]
        fn a_short_proof_reads_nothing(narg in proptest::collection::vec(any::<u8>(), 0..24)) {
            // Fewer than 24 bytes hold no element, nor fewer than 8 a nonce.
            let mut cursor = narg.as_slice();
            prop_assert_eq!(F192::from_narg(&mut cursor), None);
            if narg.len() < 8 {
                prop_assert_eq!(u64::from_narg(&mut narg.as_slice()), None);
            }
        }
    }

    #[test]
    fn field_limbs_are_little_endian_lowest_first() {
        // Fixture: the element 1 + 2y + 3y^2.
        //
        //     bytes 0..8   -> c0 = 1
        //     bytes 8..16  -> c1 = 2
        //     bytes 16..24 -> c2 = 3
        let bytes = F192::new(1, 2, 3).encode();
        assert_eq!((bytes[0], bytes[8], bytes[16]), (1, 2, 3));
        assert_eq!(bytes.iter().filter(|&&b| b != 0).count(), 3);
    }

    #[test]
    fn length_prefixed_lists_are_prefix_free() {
        // Without the count, [a] followed by b would read as the list [a, b].
        //
        //     [1]    -> 01 00 .. 00 | 1
        //     [1, 2] -> 02 00 .. 00 | 1 | 2
        let one = LengthPrefixed(&[1u64]).encode();
        let two = LengthPrefixed(&[1u64, 2]).encode();
        assert_eq!(one.len(), 16);
        assert!(!two.starts_with(&one));
    }
}
