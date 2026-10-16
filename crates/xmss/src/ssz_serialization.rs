//! SSZ encodings (Ethereum consensus-layer compatibility) for the public key and
//! the signature, the two objects that appear in consensus data. The secret key
//! never does, so it keeps only its serde persistence.
//!
//! Both are SSZ containers of fixed-size byte vectors, so each encoding is the
//! plain concatenation of its fields and every byte string of the right length
//! decodes:
//!
//! - [`XmssPublicKey`]: `merkle_root | public_param`, [`PUB_KEY_SSZ_LEN`] bytes.
//! - [`XmssSignature`]: `leaf_index | chain_tips | randomness | merkle_proof`,
//!   [`SIGNATURE_SSZ_LEN`] bytes, the leaf index a little-endian `uint32`.

pub use ssz::{Decode, DecodeError, Encode};

use crate::*;

/// SSZ length of an encoded public key. Equal to [`PUB_KEY_SIZE`]: both encodings
/// concatenate the same fixed-size fields.
pub const PUB_KEY_SSZ_LEN: usize = PUB_KEY_SIZE;
/// SSZ length of an encoded signature. Equal to [`SIG_SIZE`], for the same reason.
pub const SIGNATURE_SSZ_LEN: usize = SIG_SIZE;

/// Peels fixed-size fields off a buffer whose length was checked up front.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> [u8; N] {
        let (head, tail) = self.0.split_at(N);
        self.0 = tail;
        head.try_into().unwrap()
    }
}

fn check_len(bytes: &[u8], expected: usize) -> Result<Reader<'_>, DecodeError> {
    if bytes.len() == expected {
        Ok(Reader(bytes))
    } else {
        Err(DecodeError::InvalidByteLength {
            len: bytes.len(),
            expected,
        })
    }
}

impl Encode for WotsSignature {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        WOTS_SIG_SIZE
    }

    fn ssz_bytes_len(&self) -> usize {
        WOTS_SIG_SIZE
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        for chain_tip in &self.chain_tips {
            buf.extend_from_slice(chain_tip);
        }
        buf.extend_from_slice(&self.randomness);
    }
}

impl Decode for WotsSignature {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        WOTS_SIG_SIZE
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut reader = check_len(bytes, WOTS_SIG_SIZE)?;
        Ok(Self {
            chain_tips: std::array::from_fn(|_| reader.take()),
            randomness: reader.take(),
        })
    }
}

impl Encode for XmssPublicKey {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        PUB_KEY_SSZ_LEN
    }

    fn ssz_bytes_len(&self) -> usize {
        PUB_KEY_SSZ_LEN
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.merkle_root);
        buf.extend_from_slice(&self.public_param);
    }
}

impl Decode for XmssPublicKey {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        PUB_KEY_SSZ_LEN
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut reader = check_len(bytes, PUB_KEY_SSZ_LEN)?;
        Ok(Self {
            merkle_root: reader.take(),
            public_param: reader.take(),
        })
    }
}

impl Encode for XmssSignature {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        SIGNATURE_SSZ_LEN
    }

    fn ssz_bytes_len(&self) -> usize {
        SIGNATURE_SSZ_LEN
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.leaf_index.to_le_bytes());
        self.wots_signature.ssz_append(buf);
        for neighbour in &self.merkle_proof {
            buf.extend_from_slice(neighbour);
        }
    }
}

impl Decode for XmssSignature {
    fn is_ssz_fixed_len() -> bool {
        true
    }

    fn ssz_fixed_len() -> usize {
        SIGNATURE_SSZ_LEN
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut reader = check_len(bytes, SIGNATURE_SSZ_LEN)?;
        Ok(Self {
            leaf_index: LeafIndex::from_le_bytes(reader.take()),
            wots_signature: WotsSignature::from_ssz_bytes(&reader.take::<WOTS_SIG_SIZE>())?,
            merkle_proof: std::array::from_fn(|_| reader.take()),
        })
    }
}
