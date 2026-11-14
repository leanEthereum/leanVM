//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredBytecodeClaim, bytecode_vars};
use super::guest::scalar_bytecode;
use super::statement::statement_digest;
use super::{LeanSphincsClaim, LeanXmssClaim};
use verifier::E;

/// What an  [`AggregateProof`] proves: a list of `(pubkey, message)` leanXMSS claims and a list of `(pubkey, message)`
/// leanSphincs claims had a valid signature, and (optional) some digest represent a correct matrix of blobs (see
/// [`lean_da::BlobMatrix`]).
///
/// Each of the first 2 list must be strictly sorted (so without duplicates), potentially empty.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AggregateClaims {
    pub lean_xmss: Vec<LeanXmssClaim>,
    pub lean_sphincs: Vec<LeanSphincsClaim>,
    /// `None` for no blobs.
    pub da_commitment: Option<[u8; 32]>,
}

/// Which covered claims [`aggregate`](super::aggregate) proves.
#[derive(Clone, Copy, Debug)]
pub enum OutputClaims<'a> {
    /// Every covered signature claim. The DA root is `blobs`' if any, otherwise the first
    /// child's that has one, otherwise none.
    All,
    /// Exactly these, each covered by the inputs.
    Only(&'a AggregateClaims),
}

/// A proof of some [`AggregateClaims`], which travel separately: [`Self::verify`] checks it against
/// the claims the receiver expects.
#[derive(Clone, Debug)]
pub struct AggregateProof {
    /// The point of the deferred bytecode claim; its value is computed from it.
    pub(super) bytecode_point: Vec<E>,
    pub(super) proof: verifier::Proof,
}

// Wire format: the deferred point (a u64 count, then each element as two u64 limbs, all little-endian),
// then the VM proof. The encoding is canonical: the VM proof's decoder rejects trailing bytes.

pub(super) fn encode(point: &[E], proof: &[u8]) -> Vec<u8> {
    let mut out = (point.len() as u64).to_le_bytes().to_vec();
    out.extend(point.iter().flat_map(|x| [x.c0, x.c1]).flat_map(u64::to_le_bytes));
    out.extend(proof);
    out
}

/// The deferred point and the VM proof's bytes. A forged count allocates nothing.
pub(super) fn decode(bytes: &[u8]) -> Option<(Vec<E>, &[u8])> {
    let (count, rest) = bytes.split_first_chunk::<8>()?;
    let count = usize::try_from(u64::from_le_bytes(*count)).ok()?;
    let (limbs, proof) = rest.split_at_checked(count.checked_mul(16)?)?;
    let limb = |bytes: &[u8; 8]| u64::from_le_bytes(*bytes);
    let pairs = limbs.as_chunks::<8>().0.as_chunks::<2>().0;
    let point = pairs.iter().map(|[c0, c1]| E::new(limb(c0), limb(c1))).collect();
    Some((point, proof))
}

/// Whether each list is strictly sorted, so that no claim counts twice.
pub(super) fn is_sorted(claims: &AggregateClaims) -> bool {
    claims.lean_xmss.windows(2).all(|w| w[0] < w[1]) && claims.lean_sphincs.windows(2).all(|w| w[0] < w[1])
}

impl AggregateClaims {
    /// The number of `(pubkey, message)` claims, not of distinct signers: a pubkey may sign
    /// several messages.
    pub fn num_signature_claims(&self) -> usize {
        self.lean_xmss.len() + self.lean_sphincs.len()
    }
}

/// The VM's public input: the digest of the claims and the deferred claim.
pub(super) fn public_input(claims: &AggregateClaims, defer: &DeferredBytecodeClaim) -> [E; 2] {
    let da = verifier::da::digest(claims.da_commitment);
    statement_digest(&claims.lean_xmss, &claims.lean_sphincs, da, defer)
}

/// The statement as the 32 bytes the `verifier` crate takes: the two limbs of each half, little-endian.
pub(crate) fn public_input_bytes(public_input: &[E; 2]) -> [u8; 32] {
    let limbs = public_input.iter().flat_map(|half| [half.c0, half.c1]);
    let mut bytes = [0; 32];
    for (chunk, limb) in bytes.as_chunks_mut().0.iter_mut().zip(limbs) {
        *chunk = limb.to_le_bytes();
    }
    bytes
}

impl AggregateProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        encode(&self.bytecode_point, &crate::wire::to_bytes(&self.proof))
    }

    /// Decode a proof, `None` if the bytes are not one. This does not verify: call [`Self::verify`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (bytecode_point, proof) = decode(bytes)?;
        if bytecode_point.len() != bytecode_vars() {
            return None;
        }
        let proof = crate::wire::from_bytes(proof)?;
        Some(Self { bytecode_point, proof })
    }

    /// Whether this proves `claims`: the lists are sorted, the deferred claim holds, and the stark
    /// proof is valid.
    pub fn verify(&self, claims: &AggregateClaims) -> bool {
        // The cheap check first: the rest evaluates the bytecode at a point the sender chose.
        if !is_sorted(claims) {
            return false;
        }
        let Some(defer) = DeferredBytecodeClaim::recompute_scalar(self.bytecode_point.clone()) else {
            return false;
        };
        let pi = public_input(claims, &defer);
        let verdict = verifier::verify_execution(scalar_bytecode(), &public_input_bytes(&pi), &self.proof);
        if let Err(error) = &verdict {
            tracing::debug!(%error, "the proof does not verify");
        }
        verdict.is_ok()
    }
}
