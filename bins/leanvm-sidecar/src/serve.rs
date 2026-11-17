//! One request, from its payload to its response body.

use crate::wire::{
    FLAG_KEEP_PROOF, FLAG_USE_KEPT, FLAG_VERIFY_CHILDREN, OP_AGGREGATE, OP_EXTEND, OP_RECURSE, OP_VERIFY,
    OP_VERIFY_NARROW, Reader, Request, ST_AGGREGATION_FAILED, ST_BAD_REQUEST, ST_INVALID_PROOF, proved,
};
use lean_vm::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature, Message};
use lean_vm::{AggregateClaims, AggregateError, AggregateProof, MAX_RECURSIONS, OutputClaims, aggregate};

/// A proof with the claims it proves, which travel apart.
pub type Proved = (AggregateClaims, AggregateProof);

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
fn aggregation_code(error: &AggregateError) -> u32 {
    match error {
        AggregateError::InvalidChild => 1,
        AggregateError::InvalidSignature => 4,
        AggregateError::ProvingFailed => 11,
        AggregateError::InvalidInput(_) => 12,
    }
}

/// Child `index` of the request, decoded and, if `verify`, natively verified against `claims`.
fn child(proof: &[u8], claims: AggregateClaims, index: usize, verify: bool) -> Result<Proved, Failure> {
    let invalid = |text: &str| Failure {
        status: ST_INVALID_PROOF,
        detail: index as u32,
        text: text.into(),
    };
    let proof = AggregateProof::from_bytes(proof).ok_or_else(|| invalid("the proof does not decode"))?;
    if verify && !proof.verify(&claims) {
        return Err(invalid("the proof does not verify against its claims"));
    }
    Ok((claims, proof))
}

fn prove(
    children: &[Proved],
    signatures: Vec<(LeanXmssPublicKey, Message, LeanXmssSignature)>,
    declare: Option<&AggregateClaims>,
    log_inv_rate: usize,
) -> Result<Proved, Failure> {
    let output = declare.map_or(OutputClaims::All, OutputClaims::Only);
    aggregate(children, signatures, vec![], None, output, log_inv_rate).map_err(|error| Failure {
        status: ST_AGGREGATION_FAILED,
        detail: aggregation_code(&error),
        text: error.to_string(),
    })
}

/// The response body of `request`, whose payload is `payload`. `kept` is the proof held between
/// requests under `FLAG_KEEP_PROOF`; a request that fails leaves it as it was.
pub fn handle(request: &Request, payload: &[u8], kept: &mut Option<Proved>) -> Result<Vec<u8>, Failure> {
    let log_inv_rate = request.log_inv_rate as usize;
    let mut reader = Reader(payload);
    let proof = match request.op {
        OP_AGGREGATE => {
            let signatures = reader.signatures().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            prove(&[], signatures, None, log_inv_rate)?
        }
        OP_RECURSE | OP_EXTEND => {
            let use_kept = request.flags & FLAG_USE_KEPT != 0;
            if use_kept && kept.is_none() {
                return Err(Failure::bad_request("no kept proof"));
            }
            let count = reader.u32().ok_or_else(malformed)? as usize;
            if !(1..=MAX_RECURSIONS).contains(&(count + usize::from(use_kept))) {
                return Err(Failure::bad_request("child count outside 1..=16"));
            }
            let mut encoded = Vec::with_capacity(count);
            for _ in 0..count {
                let claims = reader.claims().ok_or_else(malformed)?;
                encoded.push((claims, reader.proof().ok_or_else(malformed)?));
            }
            let signatures = match request.op {
                OP_EXTEND => reader.signatures().ok_or_else(malformed)?,
                _ => vec![],
            };
            reader.end().ok_or_else(malformed)?;
            let verify = request.flags & FLAG_VERIFY_CHILDREN != 0;
            let mut children = Vec::with_capacity(count);
            for (index, (claims, proof)) in encoded.into_iter().enumerate() {
                children.push(child(proof, claims, index, verify)?);
            }
            // Last, so a payload child keeps its index.
            if use_kept {
                children.extend(kept.take());
            }
            let result = prove(&children, signatures, None, log_inv_rate);
            if use_kept && result.is_err() {
                *kept = children.pop();
            }
            result?
        }
        OP_VERIFY => {
            let claims = reader.claims().ok_or_else(malformed)?;
            let proof = reader.proof().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            child(proof, claims, 0, true)?;
            return Ok(Vec::new());
        }
        OP_VERIFY_NARROW => {
            let claims = reader.claims().ok_or_else(malformed)?;
            let proof = reader.proof().ok_or_else(malformed)?;
            let retained = reader.claims().ok_or_else(malformed)?;
            reader.end().ok_or_else(malformed)?;
            let verified = child(proof, claims, 0, true)?;
            prove(&[verified], vec![], Some(&retained), log_inv_rate)?
        }
        _ => return Err(Failure::bad_request("unknown op")),
    };
    let body = proved(&proof.0, &proof.1);
    if request.flags & FLAG_KEEP_PROOF != 0 {
        *kept = Some(proof);
    }
    Ok(body)
}
