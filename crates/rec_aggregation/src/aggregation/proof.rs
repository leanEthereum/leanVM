//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredBytecodeClaim, scalar_bytecode};
use super::error::{AggregateVerifyError, StarkVerifyError};
use super::statement::statement_digest;
use super::{LeanSphincsClaim, LeanXmssClaim};
use leanvm_core::cpu::{public_input_bytes, scalar_proof};
use primitives::field::F128;

/// What an aggregate attests: each `(pubkey, message)` in [`Self::lean_xmss`] and
/// [`Self::lean_sphincs`] has a valid signature under that scheme, and [`Self::da_commitment`], if
/// any, commits to blobs that are valid Reed-Solomon codewords.
///
/// Each list must be strictly sorted (so without duplicates), or [`EthereumProof::verify`] rejects
/// it. Either may be empty.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EthereumClaims {
    pub lean_xmss: Vec<LeanXmssClaim>,
    pub lean_sphincs: Vec<LeanSphincsClaim>,
    /// `None` for no blobs.
    pub da_commitment: Option<[u8; 32]>,
}

/// A proof of some [`EthereumClaims`], which travel separately: [`Self::verify`] checks it against
/// the claims the receiver expects.
#[derive(Clone, Debug)]
pub struct EthereumProof {
    /// The bytecode claim left to the parent proof, or to [`Self::verify`].
    pub(super) defer: DeferredBytecodeClaim,
    pub(super) proof: leanvm_core::cpu::Proof,
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

/// Each list must be strictly sorted, so that no claim counts twice.
pub(super) fn check_signer_set(claims: &EthereumClaims) -> Result<(), AggregateVerifyError> {
    if !claims.lean_xmss.windows(2).all(|w| w[0] < w[1]) || !claims.lean_sphincs.windows(2).all(|w| w[0] < w[1]) {
        return Err(AggregateVerifyError::MalformedSignerSet);
    }
    Ok(())
}

impl EthereumClaims {
    /// The number of `(pubkey, message)` claims, not of distinct signers: a pubkey may sign
    /// several messages.
    pub fn num_signature_claims(&self) -> usize {
        self.lean_xmss.len() + self.lean_sphincs.len()
    }
}

/// The VM's public input: the digest of the claims and the deferred claim.
pub(super) fn public_input(claims: &EthereumClaims, defer: &DeferredBytecodeClaim) -> [F128; 2] {
    let da = verifier::da::digest(claims.da_commitment);
    statement_digest(&claims.lean_xmss, &claims.lean_sphincs, da, defer)
}

impl EthereumProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        encode(&self.defer.bytecode_point, &self.proof.to_bytes())
    }

    /// Decode a proof. This does not verify: call [`Self::verify`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (bytecode_point, proof) = decode(bytes).ok_or(AggregateVerifyError::MalformedEncoding)?;
        let proof = leanvm_core::cpu::Proof::from_bytes(proof).ok_or(AggregateVerifyError::MalformedEncoding)?;
        Ok(Self {
            defer: DeferredBytecodeClaim::recompute_scalar(bytecode_point)?,
            proof,
        })
    }

    /// Verify that this proves `claims`: the lists are sorted, the deferred claim holds, and the stark
    /// proof is valid.
    ///
    /// `formal/` proves this for one node only (`formal/statement.tex`, "What is not proved").
    pub fn verify(&self, claims: &EthereumClaims) -> Result<(), AggregateVerifyError> {
        check_signer_set(claims)?;
        let _s = tracing::info_span!("Recompute deferred claims").entered();
        let defer = DeferredBytecodeClaim::recompute_scalar(self.defer.bytecode_point.clone())?;
        drop(_s);
        if defer != self.defer {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        let _s = tracing::info_span!("Statement digest").entered();
        let pi = public_input(claims, &self.defer);
        drop(_s);
        verifier::verify_execution(scalar_bytecode(), &public_input_bytes(&pi), &scalar_proof(&self.proof))
            .map(|_| ())
            .map_err(|e| AggregateVerifyError::Snark(StarkVerifyError(e)))
    }
}
