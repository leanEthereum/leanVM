use crate::Error;
use rec_aggregation::{SingleMessageAggregateSignature, init_aggregation_bytecode};
use ssz::{Decode, Encode};
use std::fmt::{Debug, Formatter};
use xmss::{XmssPublicKey, XmssSignature};

const MAGIC: &[u8; 4] = b"LMSI";
const VERSION: u8 = 1;
const RAW: u8 = 0;
const AGGREGATE: u8 = 1;
const HEADER_LEN: usize = MAGIC.len() + 2;
const RAW_LEN: usize = HEADER_LEN + 32 + 4 + xmss::PUB_KEY_SSZ_LEN + xmss::SIGNATURE_SSZ_LEN;

/// The statement signed by every input to one aggregation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
/// contain.
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

    /// Serializes this facade signature into a tagged, self-describing envelope.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        out.push(VERSION);
        match &self.0 {
            Kind::Raw {
                claim,
                public_key,
                signature,
            } => {
                out.reserve(RAW_LEN - out.len());
                out.push(RAW);
                out.extend_from_slice(claim.message());
                out.extend_from_slice(&claim.slot().to_le_bytes());
                out.extend_from_slice(&public_key.as_ssz_bytes());
                out.extend_from_slice(&signature.as_ssz_bytes());
            }
            Kind::Aggregate(signature) => {
                out.push(AGGREGATE);
                out.extend_from_slice(&signature.to_bytes());
            }
        }
        out
    }

    /// Restores a signature produced by [`Self::to_bytes`].
    ///
    /// This checks framing and canonical encodings only. Use [`crate::verify`] or
    /// [`crate::aggregate`] to establish cryptographic validity.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < HEADER_LEN || &bytes[..MAGIC.len()] != MAGIC || bytes[MAGIC.len()] != VERSION {
            return Err(Error::MalformedSignature);
        }
        match bytes[MAGIC.len() + 1] {
            RAW if bytes.len() == RAW_LEN => {
                let mut offset = HEADER_LEN;
                let message = bytes[offset..offset + 32]
                    .try_into()
                    .map_err(|_| Error::MalformedSignature)?;
                offset += 32;
                let slot = u32::from_le_bytes(
                    bytes[offset..offset + 4]
                        .try_into()
                        .map_err(|_| Error::MalformedSignature)?,
                );
                offset += 4;
                let public_key = XmssPublicKey::from_ssz_bytes(&bytes[offset..offset + xmss::PUB_KEY_SSZ_LEN])
                    .map_err(|_| Error::MalformedSignature)?;
                offset += xmss::PUB_KEY_SSZ_LEN;
                let signature =
                    XmssSignature::from_ssz_bytes(&bytes[offset..]).map_err(|_| Error::MalformedSignature)?;
                Ok(Self::raw(Claim::new(message, slot), public_key, signature))
            }
            AGGREGATE => {
                init_aggregation_bytecode();
                SingleMessageAggregateSignature::from_bytes(&bytes[HEADER_LEN..])
                    .map(Self::aggregate)
                    .ok_or(Error::MalformedSignature)
            }
            _ => Err(Error::MalformedSignature),
        }
    }
}
