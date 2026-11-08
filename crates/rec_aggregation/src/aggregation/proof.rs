//! The aggregate, its wire format and its native verification.

use super::deferred::{DeferredClaim, scalar_bytecode};
use super::error::{AggregateVerifyError, SnarkVerifyError};
use super::statement::statement_digest;
use super::{LeanSphincsClaim, LeanXmssClaim, MAX_KEYS};
use leanvm_core::cpu::{public_input_bytes, scalar_proof};
use primitives::field::F192;
use signatures::lean_sphincs::LeanSphincsPublicKey;
use signatures::lean_xmss::LeanXmssPublicKey;

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

/// Signature claims grouped by scheme, each a `(pubkey, message)` pair.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

// The wire format, little-endian:
//
//     claims : for xmss, then lean_sphincs, a u64 count, then each claim's key (its
//              scheme's `to_bytes`) and message
//     core   : the DA root as a byte 0 or 1, then its 32 bytes if 1; the deferred point
//              as a u64 count of limb triples `c0, c1, c2`; the VM proof as a u64
//              length and its bytes
//
// Decoding rejects trailing bytes. Without that an accepted aggregate has unboundedly
// many encodings, so anything downstream that dedupes or indexes on the serialized
// bytes can be made to see one aggregate as many.

/// Everything but the signer set, which a receiver may already hold.
type WireCore = (Option<[u8; 32]>, Vec<F192>, Vec<u8>);

/// The wire bytes of the claims, if sent, and of the core.
pub(super) fn encode(
    claims: Option<(&[LeanXmssClaim], &[LeanSphincsClaim])>,
    da_root: Option<[u8; 32]>,
    point: &[F192],
    proof: &[u8],
) -> Vec<u8> {
    fn put_u64(out: &mut Vec<u8>, x: u64) {
        out.extend(x.to_le_bytes());
    }
    let mut out = Vec::new();
    if let Some((xmss, lean_sphincs)) = claims {
        put_u64(&mut out, xmss.len() as u64);
        for (pk, message) in xmss {
            out.extend(pk.to_bytes());
            out.extend(message);
        }
        put_u64(&mut out, lean_sphincs.len() as u64);
        for (pk, message) in lean_sphincs {
            out.extend(pk.to_bytes());
            out.extend(message);
        }
    }
    match da_root {
        None => out.push(0),
        Some(root) => {
            out.push(1);
            out.extend(root);
        }
    }
    put_u64(&mut out, point.len() as u64);
    for limb in point.iter().flat_map(|x| x.to_limbs()) {
        put_u64(&mut out, limb);
    }
    put_u64(&mut out, proof.len() as u64);
    out.extend(proof);
    out
}

/// The claims and the core.
pub(super) fn decode(bytes: &[u8]) -> Option<(SignatureClaims, WireCore)> {
    WireReader::parse(bytes, |r| Some((r.claims()?, r.core()?)))
}

/// The core alone.
pub(super) fn decode_core(bytes: &[u8]) -> Option<WireCore> {
    WireReader::parse(bytes, WireReader::core)
}

/// A cursor over wire bytes: the bytes not yet read.
struct WireReader<'a>(&'a [u8]);

impl<'a> WireReader<'a> {
    /// What `read` reads from `bytes`, which it must read to the end: trailing bytes are an error.
    fn parse<T>(bytes: &'a [u8], read: impl FnOnce(&mut Self) -> Option<T>) -> Option<T> {
        let mut r = Self(bytes);
        let value = read(&mut r)?;
        r.0.is_empty().then_some(value)
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N)?.try_into().ok()
    }

    fn u64(&mut self) -> Option<u64> {
        self.array().map(u64::from_le_bytes)
    }

    fn count(&mut self) -> Option<usize> {
        usize::try_from(self.u64()?).ok()
    }

    /// A counted list. Every item reads input, so a forged count fails once the input runs out, and the list
    /// grows only as its items arrive.
    fn list<T>(&mut self, read: impl Fn(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let n = self.count()?;
        (0..n).map(|_| read(self)).collect()
    }

    fn claims(&mut self) -> Option<SignatureClaims> {
        let xmss = self.list(|r| Some((LeanXmssPublicKey::from_bytes(&r.array()?), r.array()?)))?;
        let lean_sphincs = self.list(|r| Some((LeanSphincsPublicKey::from_bytes(&r.array()?), r.array()?)))?;
        Some(SignatureClaims { xmss, lean_sphincs })
    }

    fn core(&mut self) -> Option<WireCore> {
        let da_root = match self.array()? {
            [0] => None,
            [1] => Some(self.array()?),
            _ => return None,
        };
        let point = self.list(|r| Some(F192::new(r.u64()?, r.u64()?, r.u64()?)))?;
        let n = self.count()?;
        let proof = self.take(n)?.to_vec();
        Some((da_root, point, proof))
    }
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
        let claims = (&self.xmss_signers[..], &self.lean_sphincs_signers[..]);
        encode(
            Some(claims),
            self.da_root,
            &self.defer.bytecode_point,
            &self.proof.to_bytes(),
        )
    }

    /// Parsing does NOT verify: the proof is untouched, only shapes are checked.
    /// Call [`Self::verify`] before believing any of it.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (claims, core) = decode(bytes).ok_or(AggregateVerifyError::MalformedEncoding)?;
        Self::from_parts(claims, core)
    }

    /// Without the signer set, for a receiver that already knows it. A set other
    /// than the one aggregated fails verification.
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        encode(None, self.da_root, &self.defer.bytecode_point, &self.proof.to_bytes())
    }

    /// The serialized size of the VM proof alone, without the statement.
    pub fn proof_size(&self) -> usize {
        self.proof.to_bytes().len()
    }

    /// Inverse of [`Self::to_bytes_without_pubkeys`], verifying nothing either.
    pub fn from_bytes_without_pubkeys(bytes: &[u8], claims: SignatureClaims) -> Result<Self, AggregateVerifyError> {
        let core = decode_core(bytes).ok_or(AggregateVerifyError::MalformedEncoding)?;
        Self::from_parts(claims, core)
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
        let proof = leanvm_core::cpu::Proof::from_bytes(&proof).ok_or(AggregateVerifyError::MalformedEncoding)?;
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
