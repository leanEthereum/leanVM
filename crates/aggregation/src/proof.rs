//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredBytecodeClaim, bytecode_vars};
use super::guest::unified_guest;
use super::statement::{Claim, claim_lists, statement_digest};
use claims::AggregateClaims;
use lean_vm_core::cpu::public_input_bytes;
use primitives::field::F128;

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

/// The point, then what `proof` appends.
pub(super) fn encode(point: &[F128], proof: impl FnOnce(&mut Vec<u8>)) -> Vec<u8> {
    let mut out = (point.len() as u64).to_le_bytes().to_vec();
    // Both limbs, little-endian, are the element's `u128` little-endian.
    for &x in point {
        out.extend_from_slice(&u128::from(x).to_le_bytes());
    }
    proof(&mut out);
    out
}

/// The deferred point and the VM proof's bytes. A forged count allocates nothing.
pub(super) fn decode(bytes: &[u8]) -> Option<(Vec<F128>, &[u8])> {
    let (count, rest) = bytes.split_first_chunk::<8>()?;
    let count = usize::try_from(u64::from_le_bytes(*count)).ok()?;
    let (limbs, proof) = rest.split_at_checked(count.checked_mul(16)?)?;
    let point = limbs
        .as_chunks()
        .0
        .iter()
        .map(|&x| F128::from(u128::from_le_bytes(x)))
        .collect();
    Some((point, proof))
}

/// Whether each list is strictly sorted, so that no claim counts twice.
pub(super) fn is_sorted(lists: &[Vec<Claim>; 2]) -> bool {
    lists.iter().all(|list| list.is_sorted_by(|a, b| a < b))
}

impl AggregateProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        encode(&self.bytecode_point, |out| self.proof.write_bytes(out))
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

    /// The proof from its deferred point and VM proof, `None` if the point is not `bytecode_vars()` long. Nothing is
    /// verified.
    #[doc(hidden)]
    pub fn __from_parts(bytecode_point: Vec<F128>, proof: verifier::Proof) -> Option<Self> {
        (bytecode_point.len() == bytecode_vars()).then_some(Self { bytecode_point, proof })
    }

    /// The deferred point and the VM proof.
    #[doc(hidden)]
    pub fn __parts(&self) -> (&[F128], &verifier::Proof) {
        (&self.bytecode_point, &self.proof)
    }

    /// Whether this proves `claims`: the lists are sorted, the deferred claim holds, and the stark
    /// proof is valid.
    pub fn verify(&self, claims: &AggregateClaims) -> bool {
        // The cheap check first: the rest evaluates the bytecode at a point the sender chose.
        let lists = claim_lists(claims);
        if !is_sorted(&lists) {
            return false;
        }
        let defer = DeferredBytecodeClaim::recompute(self.bytecode_point.clone());
        let pi = statement_digest(&lists, claims.da_commitment, &defer);
        let verdict = verifier::verify_execution(unified_guest().bytecode(), &public_input_bytes(&pi), &self.proof);
        #[cfg(feature = "spans")]
        if let Err(error) = &verdict {
            tracing::debug!(%error, "the proof does not verify");
        }
        verdict.is_ok()
    }
}
