use crate::signature::Kind;
use crate::{Claim, Error, PublicKey, Signature, aggregate, decode_public_keys, encode_public_key, require_setup};
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
    /// The exact public-key set authorized for this claim. Resolve validator bitlists to public
    /// keys before constructing this value.
    pub signers: Vec<PublicKey>,
}

/// A proof binding one or more distinct claims to their signer sets.
///
/// Build this from any mixture of raw and aggregated [`Signature`] values with
/// [`merge_claims`]. Inputs sharing a claim are grouped automatically. Serialized values rely on
/// claims and signer sets carried by the outer protocol container.
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
    /// Serializes only the cryptographic proof material into a versioned envelope.
    ///
    /// Claims and signer sets are intentionally omitted. They belong in the outer protocol
    /// container and must be supplied to [`Self::from_bytes`].
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let payload = self.0.to_bytes_without_context();
        let mut bytes = Vec::with_capacity(HEADER_LEN + payload.len());
        bytes.extend_from_slice(MAGIC);
        bytes.push(VERSION);
        bytes.extend(payload);
        bytes
    }

    /// Restores a multi-claim proof produced by [`Self::to_bytes`] using context resolved from the
    /// outer protocol container.
    ///
    /// Call [`crate::setup`] before using this function.
    ///
    /// Claim-group and signer ordering are ignored, as are duplicate signers within a group.
    /// Repeating a claim is rejected. This checks framing and canonical encodings only; use
    /// [`verify_claims`] or [`verified_claims`] to establish that the supplied context is proved.
    pub fn from_bytes(bytes: &[u8], groups: &[ClaimSigners]) -> Result<Self, Error> {
        if bytes.len() <= HEADER_LEN || &bytes[..MAGIC.len()] != MAGIC || bytes[MAGIC.len()] != VERSION {
            return Err(Error::MalformedMultiClaimProof);
        }
        require_setup()?;
        let groups = canonical_groups(groups).ok_or(Error::ClaimSetMismatch)?;
        if groups.is_empty() {
            return Err(Error::Empty);
        }
        if groups.len() > crate::MAX_CLAIMS {
            return Err(Error::TooManyClaims {
                got: groups.len(),
                max: crate::MAX_CLAIMS,
            });
        }
        let contexts = groups
            .into_iter()
            .map(|(claim, signers)| {
                if signers.is_empty() {
                    return Err(Error::SignerSetMismatch);
                }
                let signers = signers.into_iter().collect::<Vec<_>>();
                let signers = decode_public_keys(&signers)?;
                if signers.len() > rec_aggregation::MAX_XMSS_AGGREGATED {
                    return Err(Error::TooManySigners {
                        got: signers.len(),
                        max: rec_aggregation::MAX_XMSS_AGGREGATED,
                    });
                }
                Ok((*claim.message(), claim.slot(), signers))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let proof = MultiMessageAggregateSignature::from_bytes_without_context(&bytes[HEADER_LEN..], contexts)
            .ok_or(Error::MalformedMultiClaimProof)?;
        Ok(Self(proof))
    }
}

/// Groups signatures by claim and proves all groups in one bundle.
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
