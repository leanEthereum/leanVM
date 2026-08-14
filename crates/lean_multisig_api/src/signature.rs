use crate::{Error, PublicKey, decode_public_keys, require_setup};
use rec_aggregation::SingleMessageAggregateSignature;
use ssz::{Decode, Encode};
use std::fmt::{Debug, Formatter};
use xmss::{XmssPublicKey, XmssSignature};

const MAGIC: &[u8; 4] = b"LMSI";
const VERSION: u8 = 1;
const RAW: u8 = 0;
const AGGREGATE: u8 = 1;
const HEADER_LEN: usize = MAGIC.len() + 2;
const RAW_LEN: usize = HEADER_LEN + xmss::SIGNATURE_SSZ_LEN;

/// The statement signed by every input to one aggregation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Claim {
    message: [u8; 32],
    slot: u32,
}

impl Claim {
    #[must_use]
    pub const fn new(message: [u8; 32], slot: u32) -> Self {
        Self { message, slot }
    }

    #[must_use]
    pub const fn message(&self) -> &[u8; 32] {
        &self.message
    }

    #[must_use]
    pub const fn slot(&self) -> u32 {
        self.slot
    }
}

/// One signature contribution, whether it is raw XMSS or recursively aggregated.
///
/// The representation is deliberately private. Values produced by [`crate::SecretKey::sign`]
/// and [`crate::aggregate`] can be mixed in one vector, serialized with [`Self::to_bytes`], and
/// restored with [`Self::from_bytes`] without the caller identifying which representation they
/// contain. Serialized values rely on the claim and signer set carried by the outer protocol
/// container.
#[derive(Clone)]
pub struct Signature(pub(crate) Kind);

#[derive(Clone)]
pub(crate) enum Kind {
    Raw {
        claim: Claim,
        public_key: XmssPublicKey,
        signature: Box<XmssSignature>,
    },
    Aggregate(SingleMessageAggregateSignature),
}

impl Debug for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Signature")
            .field("claim", &self.claim())
            .field(
                "representation",
                &match self.0 {
                    Kind::Raw { .. } => "raw",
                    Kind::Aggregate(_) => "aggregate",
                },
            )
            .finish_non_exhaustive()
    }
}

impl Signature {
    pub(crate) fn raw(claim: Claim, public_key: XmssPublicKey, signature: XmssSignature) -> Self {
        Self(Kind::Raw {
            claim,
            public_key,
            signature: Box::new(signature),
        })
    }

    pub(crate) const fn aggregate(signature: SingleMessageAggregateSignature) -> Self {
        Self(Kind::Aggregate(signature))
    }

    #[must_use]
    pub fn claim(&self) -> Claim {
        match &self.0 {
            Kind::Raw { claim, .. } => *claim,
            Kind::Aggregate(signature) => Claim::new(signature.info.core.message, signature.info.core.slot),
        }
    }

    /// Serializes the cryptographic material into a tagged envelope.
    ///
    /// The claim and signer set are intentionally omitted. They belong in the outer protocol
    /// container and must be supplied to [`Self::from_bytes`].
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        out.push(VERSION);
        match &self.0 {
            Kind::Raw { signature, .. } => {
                out.reserve(RAW_LEN - out.len());
                out.push(RAW);
                out.extend_from_slice(&signature.as_ssz_bytes());
            }
            Kind::Aggregate(signature) => {
                out.push(AGGREGATE);
                out.extend_from_slice(&signature.to_bytes_without_context());
            }
        }
        out
    }

    /// Restores a signature produced by [`Self::to_bytes`] using context resolved from the outer
    /// protocol container.
    ///
    /// Call [`crate::setup`] first when decoding an aggregate. Raw signatures do not require
    /// setup.
    ///
    /// Signer ordering and duplicates are ignored. A raw signature requires exactly one distinct
    /// signer. When signers originate in a validator bitlist, resolve that bitlist to public keys
    /// before calling this method. This checks framing and canonical encodings only; use
    /// [`crate::verify`] or [`crate::aggregate`] to establish that the supplied context is the one
    /// proved.
    pub fn from_bytes(bytes: &[u8], claim: &Claim, signers: &[PublicKey]) -> Result<Self, Error> {
        if bytes.len() < HEADER_LEN || &bytes[..MAGIC.len()] != MAGIC || bytes[MAGIC.len()] != VERSION {
            return Err(Error::MalformedSignature);
        }
        let public_keys = decode_public_keys(signers)?;
        if public_keys.len() > rec_aggregation::MAX_XMSS_AGGREGATED {
            return Err(Error::TooManySigners {
                got: public_keys.len(),
                max: rec_aggregation::MAX_XMSS_AGGREGATED,
            });
        }
        if public_keys.is_empty() {
            return Err(Error::SignerSetMismatch);
        }
        match bytes[MAGIC.len() + 1] {
            RAW if bytes.len() == RAW_LEN => {
                let [public_key] = public_keys.as_slice() else {
                    return Err(Error::SignerSetMismatch);
                };
                let signature =
                    XmssSignature::from_ssz_bytes(&bytes[HEADER_LEN..]).map_err(|_| Error::MalformedSignature)?;
                Ok(Self::raw(*claim, public_key.clone(), signature))
            }
            AGGREGATE => {
                require_setup()?;
                SingleMessageAggregateSignature::from_bytes_without_context(
                    &bytes[HEADER_LEN..],
                    *claim.message(),
                    claim.slot(),
                    public_keys,
                )
                .map(Self::aggregate)
                .ok_or(Error::MalformedSignature)
            }
            _ => Err(Error::MalformedSignature),
        }
    }
}
