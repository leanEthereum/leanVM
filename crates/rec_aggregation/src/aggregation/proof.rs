//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredClaim, scalar_bytecode};
use super::error::{AggregateVerifyError, SnarkVerifyError};
use super::statement::statement_digest;
use super::{LeanSphincsClaim, LeanXmssClaim, MAX_KEYS};
use bincode::Options as _;
use leanvm_core::cpu::{public_input_bytes, scalar_proof};
use primitives::field::F192;

/// A proof that every `(pubkey, message)` in [`Self::xmss_signers`] is backed by a
/// valid leanXMSS signature, at a leaf index the statement does not record, and every
/// one in [`Self::lean_sphincs_signers`] by a valid leanSPHINCS signature. Its
/// [`Self::da_commitment`], if any, also attests that the committed blob rows are valid Reed-Solomon codewords.
/// These claims can be established directly or carried from verified child proofs.
///
/// The two lists describe the signature claims and remain separate because the proof says which scheme
/// verified which claim (the module docs give the coverage argument). Until
/// [`Self::verify`] returns `Ok` they are claims, not attestation, and even then
/// the messages are the prover's, so a caller that reads either list
/// as attestation of something must compare it against what it expected.
///
/// **Neither length counts signers, only claims.** One pubkey may appear under several
/// messages, so a committee threshold has to count distinct pubkeys itself.
#[derive(Clone, Debug)]
pub struct EthereumProof {
    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair. The
    /// claims of both schemes together are strictly fewer than [`MAX_KEYS`].
    pub(super) xmss_signers: Vec<LeanXmssClaim>,
    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair.
    pub(super) lean_sphincs_signers: Vec<LeanSphincsClaim>,
    /// At most one LeanDA root, checked here or by a descendant. The statement carries
    /// its [`verifier::da::digest`].
    pub(super) da_root: Option<[u8; 32]>,
    /// What this aggregate defers to whoever discharges it: its parent, in
    /// circuit, or [`Self::verify`], natively.
    pub(super) defer: DeferredClaim,
    pub(super) proof: leanvm_core::cpu::Proof,
}

/// Everything but the signer set, which a receiver may already hold.
type WireCore = (Option<[u8; 32]>, Vec<F192>, leanvm_core::cpu::Proof);

/// Signature claims grouped by scheme, each a `(pubkey, message)` pair.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SignatureClaims {
    pub xmss: Vec<LeanXmssClaim>,
    pub lean_sphincs: Vec<LeanSphincsClaim>,
}

/// Exactly the claims to publish: empty lists publish no claims of that kind, and a
/// `None` DA commitment no root.
#[derive(Clone, Copy)]
pub struct ClaimSelection<'a> {
    pub signatures: &'a SignatureClaims,
    pub da_commitment: Option<[u8; 32]>,
}

/// The wire encoding: bincode's fixed-width integers, as the free functions use,
/// but rejecting trailing bytes, which they do not. Without that an accepted
/// aggregate has unboundedly many encodings, so anything downstream that dedupes
/// or indexes on the serialized bytes can be made to see one aggregate as many.
pub(super) fn wire() -> impl bincode::Options {
    bincode::DefaultOptions::new().with_fixint_encoding()
}

/// Reject a signer set that the coverage argument does not cover: strict sorting
/// within each list is what stops one claim being counted many times, so each
/// list's length is a count of distinct `(pubkey, message)` claims. Either list may be
/// empty; both may be empty for a blob proof. [`MAX_KEYS`] is exclusive here, as in
/// the guest.
pub(super) fn check_signer_set(
    xmss_signers: &[LeanXmssClaim],
    lean_sphincs_signers: &[LeanSphincsClaim],
) -> Result<(), AggregateVerifyError> {
    if xmss_signers.len() + lean_sphincs_signers.len() >= MAX_KEYS
        || !xmss_signers.windows(2).all(|w| w[0] < w[1])
        || !lean_sphincs_signers.windows(2).all(|w| w[0] < w[1])
    {
        return Err(AggregateVerifyError::MalformedSignerSet);
    }
    Ok(())
}

impl EthereumProof {
    /// This aggregate's own public statement, as the VM publishes it, given its DA digest.
    pub(super) fn statement(&self, da: [u8; 32]) -> [F192; 2] {
        statement_digest(&self.xmss_signers, &self.lean_sphincs_signers, da, &self.defer)
    }

    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair. May be
    /// empty, including in a blob-only proof.
    pub fn xmss_signers(&self) -> &[LeanXmssClaim] {
        &self.xmss_signers
    }

    /// Strictly sorted and deduplicated on the whole `(pubkey, message)` pair.
    pub fn lean_sphincs_signers(&self) -> &[LeanSphincsClaim] {
        &self.lean_sphincs_signers
    }

    /// The LeanDA root proved here or by a descendant, if any. `None` makes no blob claim.
    pub fn da_commitment(&self) -> Option<[u8; 32]> {
        self.da_root
    }

    /// The declared claims, as many as the coverage table's declared slots.
    ///
    /// NOT a count of distinct signers: a pubkey of either scheme may hold several
    /// claims, one per message it signed. A caller that wants signers has to
    /// deduplicate by pubkey itself.
    pub fn num_signature_claims(&self) -> usize {
        self.xmss_signers.len() + self.lean_sphincs_signers.len()
    }

    /// The wire format: the signer set, the DA root, the deferred point, and
    /// the VM proof. The claim *value* is not transmitted; [`Self::from_bytes`]
    /// recomputes it, so there is nothing to lie about.
    pub fn to_bytes(&self) -> Vec<u8> {
        wire()
            .serialize(&((&self.xmss_signers, &self.lean_sphincs_signers), self.core()))
            .expect("an aggregate serializes")
    }

    /// Parsing does NOT verify: the proof is untouched, only shapes are checked.
    /// Call [`Self::verify`] before believing any of it.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (claims, core): (SignatureClaims, WireCore) = wire()
            .deserialize(bytes)
            .map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        Self::from_parts(claims, core)
    }

    /// Without the signer set, for a receiver that already knows it. A set other
    /// than the one aggregated fails verification.
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        wire().serialize(&self.core()).expect("an aggregate serializes")
    }

    /// The serialized size of the VM proof alone, without the statement.
    pub fn proof_size(&self) -> usize {
        wire().serialized_size(&self.proof).expect("a proof serializes") as usize
    }

    /// Inverse of [`Self::to_bytes_without_pubkeys`], verifying nothing either.
    pub fn from_bytes_without_pubkeys(bytes: &[u8], claims: SignatureClaims) -> Result<Self, AggregateVerifyError> {
        Self::from_parts(
            claims,
            wire()
                .deserialize(bytes)
                .map_err(|_| AggregateVerifyError::MalformedEncoding)?,
        )
    }

    fn core(&self) -> (&Option<[u8; 32]>, &[F192], &leanvm_core::cpu::Proof) {
        (&self.da_root, &self.defer.bytecode_point, &self.proof)
    }

    fn from_parts(claims: SignatureClaims, core: WireCore) -> Result<Self, AggregateVerifyError> {
        let SignatureClaims {
            xmss: xmss_signers,
            lean_sphincs: lean_sphincs_signers,
        } = claims;
        let (da_root, bytecode_point, proof) = core;
        // Cheap rejections first. `recompute_scalar` below is a pass over the whole stacked
        // bytecode, on a point a peer chose, so
        // anything decidable without it has to be decided before it.
        check_signer_set(&xmss_signers, &lean_sphincs_signers)?;
        Ok(Self {
            xmss_signers,
            lean_sphincs_signers,
            da_root,
            // The wire carries no value, only the points to derive it from.
            defer: DeferredClaim::recompute_scalar(bytecode_point)?,
            proof,
        })
    }

    /// Verify the aggregate's internal consistency: the signer set is well
    /// formed, the deferred bytecode claim holds at its
    /// transmitted point, and the VM proof satisfies the statement built from
    /// all of it.
    ///
    /// This says "every `(pubkey, message)` in `xmss_signers` is a valid leanXMSS signature,
    /// and every one in `lean_sphincs_signers` a valid leanSPHINCS signature", with the
    /// messages chosen by whoever produced the aggregate: an aggregate over the same
    /// pubkeys under different messages verifies just as well. Which leaf index each
    /// leanXMSS signature used is not part of the claim. A caller that
    /// expects particular pairs has to check the two lists against them. The
    /// [`Self::da_commitment`], if any, also attests to a well-formed blob matrix; callers
    /// check that it is the commitment they require.
    ///
    /// Every field operation, the proof check and its Merkle hashing run in the `verifier` crate: one thread, no explicit SIMD.
    pub fn verify(&self) -> Result<(), AggregateVerifyError> {
        check_signer_set(&self.xmss_signers, &self.lean_sphincs_signers)?;
        // Discharging the deferred claim IS recomputing it: its value has
        // to be the true evaluation, or the recursion below proves nothing about
        // the bytecode.
        let _s = tracing::info_span!("Recompute deferred claims").entered();
        let defer = DeferredClaim::recompute_scalar(self.defer.bytecode_point.clone())?;
        drop(_s);
        if defer != self.defer {
            return Err(AggregateVerifyError::MalformedClaim);
        }
        let _s = tracing::info_span!("Statement digest").entered();
        let pi = self.statement(verifier::da::digest(self.da_root));
        drop(_s);
        verifier::verify_execution(scalar_bytecode(), &public_input_bytes(&pi), &scalar_proof(&self.proof))
            .map(|_| ())
            .map_err(|e| AggregateVerifyError::Snark(SnarkVerifyError(e)))
    }
}
