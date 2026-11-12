//! One request, from its payload to its response body.

use crate::wire::{
    FLAG_VERIFY_CHILDREN, OP_AGGREGATE, OP_RECURSE, OP_VERIFY, OP_VERIFY_NARROW, Reader, Request, ST_AGGREGATION_FAILED,
    ST_BAD_REQUEST, ST_INVALID_PROOF, proved,
};
use leanvm::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature, Message};
use leanvm::{AggregateVerifyError, AggregationError, EthereumClaims, EthereumProof, MAX_RECURSIONS, aggregate};
use std::error::Error;

pub struct Failure {
    pub status: u32,
    pub detail: u32,
    /// For a human; written to the response region, truncated to its capacity.
    pub text: String,
}

impl Failure {
    pub fn bad_request(text: &str) -> Self {
        Self {
            status: ST_BAD_REQUEST,
            detail: 0,
            text: text.into(),
        }
    }
}

fn malformed() -> Failure {
    Failure::bad_request("malformed payload")
}

/// The `detail` of `ST_AGGREGATION_FAILED`. Part of the protocol: a variant keeps its number.
fn aggregation_code(error: &AggregationError) -> u32 {
    match error {
        AggregationError::InvalidChild(_) => 1,
        AggregationError::Empty => 2,
        AggregationError::NotCovered => 3,
        AggregationError::MalformedRawSignature => 4,
        AggregationError::TooLarge => 5,
        AggregationError::InvalidBlobSize { .. } => 6,
        AggregationError::BlobNotCovered => 7,
        AggregationError::BlobsUnpublished => 8,
        AggregationError::InvalidRate { .. } => 9,
        AggregationError::ChildOutOfRange { .. } => 10,
        AggregationError::ProofError(_) => 11,
    }
}

/// Child `index` of the request, decoded against `claims` and natively verified if `verify`.
fn child(proof: &[u8], claims: EthereumClaims, index: usize, verify: bool) -> Result<EthereumProof, Failure> {
    let invalid = |error: AggregateVerifyError| Failure {
        status: ST_INVALID_PROOF,
        detail: index as u32,
        text: error.to_string(),
    };
    let proof = EthereumProof::from_proof_bytes(proof, claims).map_err(invalid)?;
    if verify {
        proof.verify().map_err(invalid)?;
    }
    Ok(proof)
}

fn prove(
    children: &[EthereumProof],
    signatures: Vec<(LeanXmssPublicKey, Message, LeanXmssSignature)>,
    declare: Option<&EthereumClaims>,
    log_inv_rate: usize,
) -> Result<Vec<u8>, Failure> {
    match aggregate(children, signatures, vec![], &[], declare, log_inv_rate) {
        Ok(proof) => Ok(proved(&proof)),
        Err(error) => Err(Failure {
            status: ST_AGGREGATION_FAILED,
            detail: aggregation_code(&error),
            text: match error.source() {
                Some(source) => format!("{error}: {source}"),
                None => error.to_string(),
            },
        }),
    }
}

/// The response body of `request`, whose payload is `payload`.
pub fn handle(request: &Request, payload: &[u8]) -> Result<Vec<u8>, Failure> {
    let log_inv_rate = request.log_inv_rate as usize;
    let mut reader = Reader(payload);
    match request.op {
        OP_AGGREGATE => {
            let signatures = reader.signatures().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            prove(&[], signatures, None, log_inv_rate)
        }
        OP_RECURSE => {
            let count = reader.u32().ok_or_else(malformed)? as usize;
            if !(1..=MAX_RECURSIONS).contains(&count) {
                return Err(Failure::bad_request("child count outside 1..=16"));
            }
            let mut encoded = Vec::with_capacity(count);
            for _ in 0..count {
                let claims = reader.claims().ok_or_else(malformed)?;
                encoded.push((claims, reader.proof().ok_or_else(malformed)?));
            }
            reader.end().ok_or_else(malformed)?;
            let verify = request.flags & FLAG_VERIFY_CHILDREN != 0;
            let mut children = Vec::with_capacity(count);
            for (index, (claims, proof)) in encoded.into_iter().enumerate() {
                children.push(child(proof, claims, index, verify)?);
            }
            prove(&children, vec![], None, log_inv_rate)
        }
        OP_VERIFY => {
            let claims = reader.claims().ok_or_else(malformed)?;
            let proof = reader.proof().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            child(proof, claims, 0, true)?;
            Ok(Vec::new())
        }
        OP_VERIFY_NARROW => {
            let claims = reader.claims().ok_or_else(malformed)?;
            let proof = reader.proof().ok_or_else(malformed)?;
            let retained = reader.claims().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            let verified = child(proof, claims, 0, true)?;
            prove(&[verified], vec![], Some(&retained), log_inv_rate)
        }
        _ => Err(Failure::bad_request("unknown op")),
    }
}
