use crate::signature::Kind;
use crate::{Claim, Error, PublicKey, Signature, aggregate, encode_public_key, require_setup};
use rec_aggregation::{
    MultiMessageAggregateSignature, merge_single_message_aggregates, verify_multi_message_aggregate,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Debug, Formatter};

const MAGIC: &[u8; 4] = b"LMCM";
const VERSION: u8 = 1;
const HEADER_LEN: usize = MAGIC.len() + 1;

/// One claim and the exact signer set authorized for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClaimSigners {
    /// The message and slot this group signed.
    pub claim: Claim,
    /// The exact public-key set authorized for this claim.
    pub signers: Vec<PublicKey>,
}

/// A self-contained proof binding one or more distinct claims to their signer sets.
///
/// Build this from any mixture of raw and aggregated [`Signature`] values with
/// [`merge_claims`]. Inputs sharing a claim are grouped automatically.
#[derive(Clone)]
pub struct MultiClaimProof(pub(crate) MultiMessageAggregateSignature);

impl Debug for MultiClaimProof {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MultiClaimProof")
            .field("claims", &self.0.info.len())
            .finish_non_exhaustive()
    }
}

impl MultiClaimProof {
    /// Serializes the proof, claims, and signer sets into one versioned envelope.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let payload = self.0.to_bytes();
        let mut bytes = Vec::with_capacity(HEADER_LEN + payload.len());
        bytes.extend_from_slice(MAGIC);
        bytes.push(VERSION);
        bytes.extend(payload);
        bytes
    }

    /// Restores a self-contained multi-claim proof produced by [`Self::to_bytes`].
    ///
    /// Call [`crate::setup`] before using this function.
    ///
    /// This checks framing, canonical encodings, and unique claims only. Use
    /// [`verify_claims`] or [`verified_claims`] to establish cryptographic validity.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() <= HEADER_LEN || &bytes[..MAGIC.len()] != MAGIC || bytes[MAGIC.len()] != VERSION {
            return Err(Error::MalformedMultiClaimProof);
        }
        require_setup()?;
        let proof =
            MultiMessageAggregateSignature::from_bytes(&bytes[HEADER_LEN..]).ok_or(Error::MalformedMultiClaimProof)?;
        let claims = proof
            .info
            .iter()
            .map(|info| Claim::new(info.core.message, info.core.slot))
            .collect::<BTreeSet<_>>();
        if proof.info.is_empty() || proof.info.len() > crate::MAX_CLAIMS || claims.len() != proof.info.len() {
            return Err(Error::MalformedMultiClaimProof);
        }
        Ok(Self(proof))
    }
}

/// Groups signatures by claim and proves all groups in one self-contained bundle.
///
/// Call [`crate::setup`] before using this function.
///
/// Raw and already aggregated signatures may be mixed freely. Signatures for the same claim
/// are combined before the resulting per-claim proofs are merged.
pub fn merge_claims(signatures: Vec<Signature>) -> Result<MultiClaimProof, Error> {
    if signatures.is_empty() {
        return Err(Error::Empty);
    }

    let mut groups: BTreeMap<Claim, Vec<Signature>> = BTreeMap::new();
    for signature in signatures {
        groups.entry(signature.claim()).or_default().push(signature);
    }
    if groups.len() > crate::MAX_CLAIMS {
        return Err(Error::TooManyClaims {
            got: groups.len(),
            max: crate::MAX_CLAIMS,
        });
    }

    let single_claims = groups
        .into_iter()
        .map(|(claim, signatures)| {
            let signature = aggregate(signatures, &claim)?;
            let Kind::Aggregate(signature) = signature.0 else {
                unreachable!("aggregate always returns an aggregate representation")
            };
            Ok(signature)
        })
        .collect::<Result<Vec<_>, Error>>()?;

    merge_single_message_aggregates(single_claims, crate::plan::RATE_ROOT)
        .map(MultiClaimProof)
        .map_err(Into::into)
}

/// Verifies a multi-claim proof and returns its canonical claim-to-signer mapping.
///
/// Call [`crate::setup`] before using this function.
///
/// Most callers should use [`verify_claims`] so the expected authorization decision cannot be
/// accidentally omitted.
#[must_use = "a valid signature is useful only after checking its claims and signers"]
pub fn verified_claims(proof: &MultiClaimProof) -> Result<Vec<ClaimSigners>, Error> {
    require_setup()?;
    verify_multi_message_aggregate(&proof.0)?;
    let mut groups = proof
        .0
        .info
        .iter()
        .map(|info| ClaimSigners {
            claim: Claim::new(info.core.message, info.core.slot),
            signers: info.pubkeys.iter().map(encode_public_key).collect(),
        })
        .collect::<Vec<_>>();
    groups.sort_by_key(|group| group.claim);
    Ok(groups)
}

fn canonical_groups(groups: &[ClaimSigners]) -> Option<BTreeMap<Claim, BTreeSet<PublicKey>>> {
    let mut canonical = BTreeMap::new();
    for group in groups {
        let signers = group.signers.iter().copied().collect();
        if canonical.insert(group.claim, signers).is_some() {
            return None;
        }
    }
    Some(canonical)
}

/// Verifies a multi-claim proof against the exact expected claims and signer sets.
///
/// Claim-group and signer ordering are ignored, as are duplicate signers within one expected
/// group. Repeating an expected claim as a second group is rejected.
pub fn verify_claims(proof: &MultiClaimProof, expected: &[ClaimSigners]) -> Result<(), Error> {
    let proved = verified_claims(proof)?;
    let Some(proved) = canonical_groups(&proved) else {
        return Err(Error::ClaimSetMismatch);
    };
    let Some(expected) = canonical_groups(expected) else {
        return Err(Error::ClaimSetMismatch);
    };
    if proved == expected {
        Ok(())
    } else {
        Err(Error::ClaimSetMismatch)
    }
}
