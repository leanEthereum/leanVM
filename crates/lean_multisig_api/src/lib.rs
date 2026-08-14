//! A small, opinionated facade over XMSS and recursive aggregation.
//!
//! [`Signature`] hides whether one-claim contribution is a raw XMSS signature or an aggregate.
//! [`MultiClaimProof`] groups any mixture of those contributions by claim and binds the
//! resulting groups in one self-contained proof. The recursion topology, proof parameters,
//! bytecode initialization, public-key pairing, and proof representations are internal choices.
#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod error;
mod key;
mod multi_claim_proof;
mod plan;
mod signature;

use rec_aggregation::{
    MAX_XMSS_AGGREGATED, SingleMessageAggregateSignature, aggregate_single_message_signatures,
    init_aggregation_bytecode, verify_single_message_aggregate,
};
use signature::Kind;
use ssz::Encode;
use std::borrow::Cow;
use std::collections::BTreeSet;
use xmss::{XmssPublicKey, XmssSignature, xmss_verify};

pub use error::Error;
pub use key::SecretKey;
pub use multi_claim_proof::{ClaimSigners, MultiClaimProof, merge_claims, verified_claims, verify_claims};
pub use signature::{Claim, Signature};

/// A canonically encoded, 32-byte XMSS public key.
///
/// This alias documents where public-key bytes are expected without imposing a wrapper on
/// callers' storage or serialization types.
pub type PublicKey = [u8; 32];

/// Maximum number of distinct claim components in one [`MultiClaimProof`].
pub const MAX_CLAIMS: usize = rec_aggregation::MAX_RECURSIONS;

const _: () = assert!(xmss::PUB_KEY_SSZ_LEN == size_of::<PublicKey>());

type Raw = (XmssPublicKey, XmssSignature);

pub(crate) fn encode_public_key(public_key: &XmssPublicKey) -> PublicKey {
    public_key
        .as_ssz_bytes()
        .try_into()
        .expect("XMSS public-key SSZ encoding must be 32 bytes")
}

fn proves(signature: &SingleMessageAggregateSignature, claim: &Claim) -> bool {
    signature.info.core.message == *claim.message() && signature.info.core.slot == claim.slot()
}

/// Pays the one-time aggregation-bytecode compilation cost at startup.
///
/// Calling this is optional. Aggregation and aggregate verification initialize the bytecode
/// lazily themselves.
pub fn warm_up() {
    init_aggregation_bytecode();
}

/// Combines raw and previously aggregated signatures proving one [`Claim`].
///
/// Every input is self-contained: a raw signature already owns its public key, while an aggregate
/// already owns its signer set. Callers neither classify entries nor maintain a parallel public-key
/// vector. Raw signatures and supplied aggregate proofs are verified before proving begins.
pub fn aggregate(signatures: Vec<Signature>, claim: &Claim) -> Result<Signature, Error> {
    if signatures.is_empty() {
        return Err(Error::Empty);
    }
    init_aggregation_bytecode();

    let mut raw = Vec::new();
    let mut children = Vec::new();
    for (index, signature) in signatures.into_iter().enumerate() {
        if signature.claim() != *claim {
            return Err(Error::MessageMismatch);
        }
        match signature.0 {
            Kind::Raw {
                public_key, signature, ..
            } => {
                xmss_verify(&public_key, claim.slot(), claim.message(), &signature)
                    .map_err(|source| Error::InvalidSignature { index, source })?;
                raw.push((public_key, *signature));
            }
            Kind::Aggregate(signature) => {
                // Do this before executing any raw leaf. The upstream aggregation call verifies
                // children again at their consuming node, but waiting until then makes the error
                // and wasted work depend on the private recursion shape.
                verify_single_message_aggregate(&signature)?;
                children.push(signature);
            }
        }
    }

    dedup_signers(&mut raw);

    check_signer_limit(&raw, &children)?;

    let tree = plan::plan(raw.len(), children.len());
    execute(&tree, &raw, &children, *claim).map(|signature| Signature::aggregate(signature.into_owned()))
}

fn check_signer_limit(raw: &[Raw], children: &[SingleMessageAggregateSignature]) -> Result<(), Error> {
    let mut signers: BTreeSet<&XmssPublicKey> = raw.iter().map(|(public_key, _)| public_key).collect();
    signers.extend(children.iter().flat_map(|child| child.info.pubkeys.iter()));
    let got = signers.len();
    if got > MAX_XMSS_AGGREGATED {
        return Err(Error::TooManySigners {
            got,
            max: MAX_XMSS_AGGREGATED,
        });
    }
    Ok(())
}

fn dedup_signers(raw: &mut Vec<Raw>) {
    raw.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw.dedup_by(|(a, _), (b, _)| a == b);
}

fn execute<'a>(
    node: &plan::Plan,
    raw: &[Raw],
    children: &'a [SingleMessageAggregateSignature],
    claim: Claim,
) -> Result<Cow<'a, SingleMessageAggregateSignature>, Error> {
    match node {
        plan::Plan::Passthrough(index) => Ok(Cow::Borrowed(&children[*index])),
        plan::Plan::Node {
            raw: range,
            children: child_plans,
            log_inv_rate,
        } => {
            let proved = child_plans
                .iter()
                .map(|child| execute(child, raw, children, claim).map(Cow::into_owned))
                .collect::<Result<Vec<_>, _>>()?;
            aggregate_single_message_signatures(
                &proved,
                raw[range.clone()].to_vec(),
                *claim.message(),
                claim.slot(),
                *log_inv_rate,
            )
            .map(Cow::Owned)
            .map_err(Into::into)
        }
    }
}

/// Verifies a signature and returns the canonical, deduplicated signer set it proves.
///
/// This is the inspection-oriented operation. Most callers should use [`verify`], which also
/// checks the expected signer set and cannot accidentally omit that authorization decision.
#[must_use = "a valid signature is useful only after checking who signed it"]
pub fn verified_signers(signature: &Signature, claim: &Claim) -> Result<Vec<PublicKey>, Error> {
    if signature.claim() != *claim {
        return Err(Error::MessageMismatch);
    }
    match &signature.0 {
        Kind::Raw {
            public_key, signature, ..
        } => {
            xmss_verify(public_key, claim.slot(), claim.message(), signature)
                .map_err(|source| Error::InvalidSignature { index: 0, source })?;
            Ok(vec![encode_public_key(public_key)])
        }
        Kind::Aggregate(signature) => {
            init_aggregation_bytecode();
            if !proves(signature, claim) {
                return Err(Error::MessageMismatch);
            }
            verify_single_message_aggregate(signature)?;
            Ok(signature.info.pubkeys.iter().map(encode_public_key).collect())
        }
    }
}

/// Verifies a signature against its claim and exact expected signer set.
///
/// Ordering and duplicate entries in `expected` are ignored; both sides are compared as sets.
pub fn verify(signature: &Signature, expected: &[PublicKey], claim: &Claim) -> Result<(), Error> {
    let proved = verified_signers(signature, claim)?;
    let expected: BTreeSet<&PublicKey> = expected.iter().collect();
    if proved.len() == expected.len() && proved.iter().all(|key| expected.contains(key)) {
        Ok(())
    } else {
        Err(Error::SignerSetMismatch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lean_vm::{EF, F};
    use ssz::Decode;
    use xmss::XmssSignature;

    const CLAIM: Claim = Claim::new([42u8; 32], 100);

    #[test]
    fn aggregate_rejects_a_wrong_raw_public_key_before_proving() {
        let alice = SecretKey::from_seed([1u8; 32], 100..=115).unwrap();
        let bob = SecretKey::from_seed([2u8; 32], 100..=115).unwrap();
        let Kind::Raw { signature, .. } = alice.sign(&CLAIM).unwrap().0 else {
            unreachable!()
        };
        let wrong_public_key = XmssPublicKey::from_ssz_bytes(&bob.public_key()).unwrap();
        let signature = Signature::raw(CLAIM, wrong_public_key, *signature);

        assert!(matches!(
            aggregate(vec![signature], &CLAIM),
            Err(Error::InvalidSignature { index: 0, .. })
        ));
    }

    #[test]
    fn invalid_child_proofs_have_one_error_in_every_plan_shape() {
        let invalid = unprovable_aggregate();
        assert!(matches!(aggregate(vec![invalid.clone()], &CLAIM), Err(Error::Proof(_))));
        assert!(matches!(
            aggregate(vec![invalid.clone(), invalid], &CLAIM),
            Err(Error::Proof(_))
        ));
    }

    #[test]
    fn signer_limit_is_checked_before_proving() {
        let signature = XmssSignature::from_ssz_bytes(&[0u8; xmss::SIGNATURE_SSZ_LEN]).unwrap();
        let n = MAX_XMSS_AGGREGATED + 1;
        let raw = (0..u32::try_from(n).unwrap())
            .map(|index| {
                let mut bytes = vec![0u8; xmss::PUB_KEY_SSZ_LEN];
                bytes[..4].copy_from_slice(&index.to_le_bytes());
                (XmssPublicKey::from_ssz_bytes(&bytes).unwrap(), signature.clone())
            })
            .collect::<Vec<_>>();

        assert!(matches!(
            check_signer_limit(&raw, &[]),
            Err(Error::TooManySigners { got, max }) if got == n && max == MAX_XMSS_AGGREGATED
        ));
    }

    fn unprovable_aggregate() -> Signature {
        warm_up();
        let point = vec![EF::default(); rec_aggregation::get_aggregation_bytecode().cumulated_n_vars()];
        let mut public_key = vec![0u8; xmss::PUB_KEY_SSZ_LEN];
        public_key[0] = 1;
        let public_keys = vec![XmssPublicKey::from_ssz_bytes(&public_key).unwrap()];
        let payload = postcard::to_allocvec(&(
            (*CLAIM.message(), CLAIM.slot(), point),
            public_keys,
            (Vec::<F>::new(), Vec::<u8>::new()),
        ))
        .unwrap();
        let mut envelope = b"LMSI\x01\x01".to_vec();
        envelope.extend(payload);
        Signature::from_bytes(&envelope).unwrap()
    }
}
