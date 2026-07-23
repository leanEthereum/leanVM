//! SSZ encodings (Ethereum consensus-layer compatibility) for the public key and the
//! signature — the two objects that appear in consensus data. The secret key never does,
//! so it only gets serde persistence. Field elements are serialized as their canonical
//! u32, little-endian; non-canonical values are rejected on decode.
//!
//! - `XmssPublicKey`: fixed length, `merkle_root | public_param` (32 bytes).
//! - `XmssSignature`: fixed length, `chain_tips | randomness | merkle_proof` (1208 bytes).

use backend::{PrimeCharacteristicRing, PrimeField32};
use ssz::{Decode, DecodeError, Encode};

use crate::*;

const FE_BYTES: usize = 4;
const DIGEST_BYTES: usize = XMSS_DIGEST_LEN * FE_BYTES;

/// SSZ length of an encoded public key: 32 bytes.
pub const PUB_KEY_SSZ_LEN: usize = PUB_KEY_FLAT_SIZE * FE_BYTES;
/// SSZ length of an encoded signature: 1208 bytes.
pub const SIGNATURE_SSZ_LEN: usize = (WOTS_SIG_SIZE_FE + LOG_LIFETIME * XMSS_DIGEST_LEN) * FE_BYTES;

fn append_fes(buf: &mut Vec<u8>, fes: &[F]) {
    for fe in fes {
        buf.extend_from_slice(&fe.as_canonical_u32().to_le_bytes());
    }
}

/// Parses `N` field elements, rejecting non-canonical (>= p) encodings.
fn read_fes<const N: usize>(bytes: &[u8]) -> Result<[F; N], DecodeError> {
    debug_assert_eq!(bytes.len(), N * FE_BYTES);
    let mut out = [F::ZERO; N];
    for (fe, chunk) in out.iter_mut().zip(bytes.as_chunks::<FE_BYTES>().0) {
        let value = u32::from_le_bytes(*chunk);
        if value >= F::ORDER_U32 {
            return Err(DecodeError::BytesInvalid(format!(
                "non-canonical field element: {value}"
            )));
        }
        *fe = F::from_u32(value);
    }
    Ok(out)
}

fn check_len(bytes: &[u8], expected: usize) -> Result<(), DecodeError> {
    if bytes.len() != expected {
        return Err(DecodeError::InvalidByteLength {
            len: bytes.len(),
            expected,
        });
    }
    Ok(())
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
        append_fes(buf, &self.merkle_root);
        append_fes(buf, &self.public_param);
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
        check_len(bytes, PUB_KEY_SSZ_LEN)?;
        Ok(Self {
            merkle_root: read_fes(&bytes[..XMSS_DIGEST_LEN * FE_BYTES])?,
            public_param: read_fes(&bytes[XMSS_DIGEST_LEN * FE_BYTES..])?,
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
        for chain_tip in &self.wots_signature.chain_tips {
            append_fes(buf, chain_tip);
        }
        append_fes(buf, &self.wots_signature.randomness);
        for neighbour in &self.merkle_proof {
            append_fes(buf, neighbour);
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
        check_len(bytes, SIGNATURE_SSZ_LEN)?;
        let mut digests = bytes.as_chunks::<DIGEST_BYTES>().0.iter();
        let mut chain_tips = [[F::ZERO; XMSS_DIGEST_LEN]; V];
        for chain_tip in &mut chain_tips {
            *chain_tip = read_fes(digests.next().unwrap())?;
        }
        let randomness_start = V * DIGEST_BYTES;
        let randomness = read_fes(&bytes[randomness_start..randomness_start + RANDOMNESS_LEN_FE * FE_BYTES])?;
        let mut digests = bytes[randomness_start + RANDOMNESS_LEN_FE * FE_BYTES..]
            .as_chunks::<DIGEST_BYTES>()
            .0
            .iter();
        let mut merkle_proof = [[F::ZERO; XMSS_DIGEST_LEN]; LOG_LIFETIME];
        for neighbour in &mut merkle_proof {
            *neighbour = read_fes(digests.next().unwrap())?;
        }
        Ok(Self {
            wots_signature: WotsSignature { chain_tips, randomness },
            merkle_proof,
        })
    }
}
