//! The claims an aggregate proof attests, and their byte form.

use lean_sphincs::LeanSphincsPublicKey;
use lean_xmss::LeanXmssPublicKey;

/// One leanXMSS claim: a pubkey, and the message it signed at whatever leaf index its
/// signature carries.
pub type LeanXmssClaim = (LeanXmssPublicKey, lean_xmss::Message);

/// One leanSPHINCS claim: a pubkey, and the message it signed.
pub type LeanSphincsClaim = (LeanSphincsPublicKey, lean_sphincs::Message);

/// What an aggregate proof proves: every `(pubkey, message)` claim of two lists, one of leanXMSS and one of
/// leanSPHINCS, had a valid signature, and, optionally, a commitment is the root of a well-formed matrix of blobs
/// (`lean_da::BlobMatrix`).
///
/// Each list is strictly sorted (so without duplicates), and may be empty.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AggregateClaims {
    pub lean_xmss: Vec<LeanXmssClaim>,
    pub lean_sphincs: Vec<LeanSphincsClaim>,
    /// `None` for no blobs.
    pub da_commitment: Option<[u8; 32]>,
}

/// Which covered claims an aggregation proves.
#[derive(Clone, Copy, Debug)]
pub enum OutputClaims<'a> {
    /// Every covered signature claim. The DA root is `blobs`' if any, otherwise the first
    /// child's that has one, otherwise none.
    All,
    /// Exactly these, each covered by the inputs.
    Only(&'a AggregateClaims),
}

// Decoding is canonical: it rejects any other flag and trailing bytes. Order is kept, sorted or not.

const _: () = assert!(lean_xmss::PUB_KEY_SIZE == 32 && lean_sphincs::PUB_KEY_SIZE == 32);
const _: () = assert!(lean_xmss::MESSAGE_LEN == 32 && lean_sphincs::MESSAGE_LEN == 32);

fn encode_claims<K>(out: &mut Vec<u8>, claims: &[(K, [u8; 32])], pk_bytes: impl Fn(&K) -> [u8; 32]) {
    out.extend((claims.len() as u64).to_le_bytes());
    for (pk, message) in claims {
        out.extend(pk_bytes(pk));
        out.extend(message);
    }
}

/// Reads a count and that many `(pubkey, message)` pairs off the front of `bytes`. A forged count allocates nothing.
fn decode_claims<K>(bytes: &mut &[u8], pk: impl Fn(&[u8; 32]) -> K) -> Option<Vec<(K, [u8; 32])>> {
    let (count, rest) = bytes.split_first_chunk::<8>()?;
    let count = usize::try_from(u64::from_le_bytes(*count)).ok()?;
    let (pairs, rest) = rest.split_at_checked(count.checked_mul(64)?)?;
    *bytes = rest;
    let pairs = pairs.as_chunks::<32>().0.as_chunks::<2>().0;
    Some(pairs.iter().map(|[key, message]| (pk(key), *message)).collect())
}

impl AggregateClaims {
    /// The number of `(pubkey, message)` claims, not of distinct signers: a pubkey may sign
    /// several messages.
    pub fn num_signature_claims(&self) -> usize {
        self.lean_xmss.len() + self.lean_sphincs.len()
    }

    /// Encode claims, which [`Self::from_bytes`] reads back: for leanXMSS, then leanSPHINCS, a little-endian `u64`
    /// count and that many 32-byte pubkey, 32-byte message pairs; then `0`, or `1` and the 32-byte DA root.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_claims(&mut out, &self.lean_xmss, LeanXmssPublicKey::to_bytes);
        encode_claims(&mut out, &self.lean_sphincs, LeanSphincsPublicKey::to_bytes);
        match self.da_commitment {
            None => out.push(0),
            Some(root) => {
                out.push(1);
                out.extend(root);
            }
        }
        out
    }

    /// Decode claims, `None` if the bytes are not exactly one encoding.
    pub fn from_bytes(mut bytes: &[u8]) -> Option<Self> {
        let lean_xmss = decode_claims(&mut bytes, LeanXmssPublicKey::from_bytes)?;
        let lean_sphincs = decode_claims(&mut bytes, LeanSphincsPublicKey::from_bytes)?;
        let da_commitment = match bytes {
            [0] => None,
            [1, root @ ..] => Some(<[u8; 32]>::try_from(root).ok()?),
            _ => return None,
        };
        Some(Self {
            lean_xmss,
            lean_sphincs,
            da_commitment,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bytes_round_trip_and_decode_canonically() {
        let claims = AggregateClaims {
            lean_xmss: vec![(LeanXmssPublicKey::from_bytes(&[1; 32]), [2; 32])],
            lean_sphincs: vec![(LeanSphincsPublicKey::from_bytes(&[3; 32]), [4; 32])],
            da_commitment: Some([5; 32]),
        };
        let bytes = claims.to_bytes();
        assert_eq!(bytes.len(), 2 * (8 + 64) + 1 + 32);
        let decoded = AggregateClaims::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.to_bytes(), bytes);
        assert!(AggregateClaims::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        assert!(AggregateClaims::from_bytes(&[bytes.as_slice(), &[0]].concat()).is_none());
        let mut flag = bytes;
        flag[2 * (8 + 64)] = 2;
        assert!(AggregateClaims::from_bytes(&flag).is_none());
    }
}
