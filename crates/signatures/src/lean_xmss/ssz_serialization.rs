//! SSZ encodings (Ethereum consensus-layer compatibility) for the public key and
//! the signature, the two objects that appear in consensus data. The secret key
//! never does, so it keeps only its serde persistence.
//!
//! Both are SSZ containers of fixed-size fields, so each encoding is the plain
//! concatenation of its fields and every byte string of the right length decodes:
//!
//! - [`LeanXmssPublicKey`]: `merkle_root | public_param`, [`PUB_KEY_SSZ_LEN`] bytes.
//! - [`LeanXmssSignature`]: `leaf_index | bottom | top`, [`SIGNATURE_SSZ_LEN`]
//!   bytes, the leaf index a little-endian `uint32` and each layer
//!   `randomizer | chain_values | path`.

pub use ssz::{Decode, DecodeError, Encode};

use crate::lean_xmss::*;

/// SSZ length of an encoded public key. Equal to [`PUB_KEY_SIZE`]: both encodings
/// concatenate the same fixed-size fields.
pub const PUB_KEY_SSZ_LEN: usize = PUB_KEY_SIZE;
/// SSZ length of an encoded signature. Equal to [`SIG_SIZE`], for the same reason.
pub const SIGNATURE_SSZ_LEN: usize = SIG_SIZE;

/// Peels fixed-size fields off a buffer whose length was checked up front.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take<const L: usize>(&mut self) -> [u8; L] {
        let (head, tail) = self.0.split_at(L);
        self.0 = tail;
        head.try_into().unwrap()
    }

    fn layer(&mut self) -> LayerSignature {
        LayerSignature {
            randomizer: self.take(),
            chain_values: std::array::from_fn(|_| self.take()),
            path: std::array::from_fn(|_| self.take()),
        }
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

fn append_layer(layer: &LayerSignature, buf: &mut Vec<u8>) {
    buf.extend_from_slice(&layer.randomizer);
    for value in layer.chain_values.iter().chain(&layer.path) {
        buf.extend_from_slice(value);
    }
}

impl Encode for LeanXmssPublicKey {
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
        buf.extend_from_slice(&self.flatten());
    }
}

impl Decode for LeanXmssPublicKey {
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

impl Encode for LeanXmssSignature {
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
        append_layer(&self.bottom, buf);
        append_layer(&self.top, buf);
    }
}

impl Decode for LeanXmssSignature {
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
            bottom: reader.layer(),
            top: reader.layer(),
        })
    }
}
