//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredBytecodeClaim, bytecode_vars};
use super::guest::scalar_bytecode;
use super::statement::statement_digest;
use super::{LeanSphincsClaim, LeanXmssClaim};
use lean_vm_core::cpu::public_input_bytes;
use primitives::field::F128;

/// What an [`AggregateProof`] proves: every `(pubkey, message)` claim of two lists, one of leanXMSS and one of
/// leanSPHINCS, had a valid signature, and, optionally, a commitment is the root of a well-formed matrix of blobs (see
/// [`lean_da::BlobMatrix`]).
///
/// Each list is strictly sorted (so without duplicates), and may be empty.
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
    /// The point of the deferred bytecode claim, `bytecode_vars()` long; its value is computed from it.
    pub(super) bytecode_point: Vec<F128>,
    pub(super) proof: verifier::Proof,
}

// Wire format: the deferred point (a u64 count, then each element as two u64 limbs, all little-endian),
// then the VM proof. The encoding is canonical: the VM proof's decoder rejects trailing bytes.

pub(super) fn encode(point: &[F128], proof: &[u8]) -> Vec<u8> {
    let mut out = (point.len() as u64).to_le_bytes().to_vec();
    out.extend(point.iter().flat_map(|x| x.to_limbs()).flat_map(u64::to_le_bytes));
    out.extend(proof);
    out
}

/// The deferred point and the VM proof's bytes. A forged count allocates nothing.
pub(super) fn decode(bytes: &[u8]) -> Option<(Vec<F128>, &[u8])> {
    let (count, rest) = bytes.split_first_chunk::<8>()?;
    let count = usize::try_from(u64::from_le_bytes(*count)).ok()?;
    let (limbs, proof) = rest.split_at_checked(count.checked_mul(16)?)?;
    let limb = |bytes: &[u8; 8]| u64::from_le_bytes(*bytes);
    let pairs = limbs.as_chunks::<8>().0.as_chunks::<2>().0;
    let point = pairs.iter().map(|[c0, c1]| F128::new(limb(c0), limb(c1))).collect();
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

impl AggregateProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        encode(&self.bytecode_point, &self.proof.to_bytes())
    }

    /// Decode a proof, `None` if the bytes are not one. This does not verify: call [`Self::verify`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (bytecode_point, proof) = decode(bytes)?;
        if bytecode_point.len() != bytecode_vars() {
            return None;
        }
        let proof = verifier::Proof::from_bytes(proof)?;
        Some(Self { bytecode_point, proof })
    }

    /// Whether this proves `claims`: the lists are sorted, the deferred claim holds, and the stark
    /// proof is valid.
    pub fn verify(&self, claims: &AggregateClaims) -> bool {
        // The cheap check first: the rest evaluates the bytecode at a point the sender chose.
        if !is_sorted(claims) {
            return false;
        }
        let defer = DeferredBytecodeClaim::recompute(self.bytecode_point.clone());
        let pi = statement_digest(claims, &defer);
        let verdict = verifier::verify_execution(scalar_bytecode(), &public_input_bytes(&pi), &self.proof);
        if let Err(error) = &verdict {
            tracing::debug!(%error, "the proof does not verify");
        }
        verdict.is_ok()
    }
}
