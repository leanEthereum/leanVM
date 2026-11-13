//! Message and payload encodings: little-endian, fixed offsets. `PROTOCOL.md` is the specification.

use leanvm::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature, MESSAGE_LEN, Message, PUB_KEY_SIZE, SIG_SIZE};
use leanvm::{EthereumClaims, EthereumProof};

/// Size of a ring slot, request or response.
pub const MSG_SIZE: usize = 64;

pub const OP_AGGREGATE: u32 = 1;
pub const OP_RECURSE: u32 = 2;
pub const OP_VERIFY: u32 = 3;
pub const OP_VERIFY_NARROW: u32 = 4;
pub const OP_EXTEND: u32 = 5;

/// `OP_RECURSE`, `OP_EXTEND`: verify every child natively before proving.
pub const FLAG_VERIFY_CHILDREN: u32 = 1;
/// A proving op: the server keeps the proof it returns, in place of any it held.
pub const FLAG_KEEP_PROOF: u32 = 2;
/// `OP_RECURSE`, `OP_EXTEND`: the kept proof is one more child, and is no longer kept.
pub const FLAG_USE_KEPT: u32 = 4;

pub const ST_OK: u32 = 0;
/// A region outside the arena, an unknown op or a payload that does not decode.
pub const ST_BAD_REQUEST: u32 = 1;
/// The response does not fit `resp_cap`; `resp_len` is the size needed.
pub const ST_RESP_TOO_SMALL: u32 = 2;
/// A proof does not decode or verify against its claims; `detail` is its index in the request.
pub const ST_INVALID_PROOF: u32 = 3;
/// `aggregate` refused or failed; `detail` is the `AggregationError` variant.
pub const ST_AGGREGATION_FAILED: u32 = 4;

const CLAIM_SIZE: usize = PUB_KEY_SIZE + MESSAGE_LEN;
const TRIPLE_SIZE: usize = CLAIM_SIZE + SIG_SIZE;

pub struct Request {
    pub id: u64,
    pub op: u32,
    pub flags: u32,
    pub req_off: u64,
    pub req_len: u64,
    pub resp_off: u64,
    pub resp_cap: u64,
    pub log_inv_rate: u32,
}

fn u32_at(bytes: &[u8; MSG_SIZE], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8; MSG_SIZE], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

impl Request {
    pub fn decode(bytes: &[u8; MSG_SIZE]) -> Self {
        Self {
            id: u64_at(bytes, 0),
            op: u32_at(bytes, 8),
            flags: u32_at(bytes, 12),
            req_off: u64_at(bytes, 16),
            req_len: u64_at(bytes, 24),
            resp_off: u64_at(bytes, 32),
            resp_cap: u64_at(bytes, 40),
            log_inv_rate: u32_at(bytes, 48),
        }
    }
}

pub struct Response {
    pub id: u64,
    pub status: u32,
    pub detail: u32,
    pub resp_len: u64,
}

impl Response {
    pub fn encode(&self) -> [u8; MSG_SIZE] {
        let mut out = [0; MSG_SIZE];
        out[0..8].copy_from_slice(&self.id.to_le_bytes());
        out[8..12].copy_from_slice(&self.status.to_le_bytes());
        out[12..16].copy_from_slice(&self.detail.to_le_bytes());
        out[16..24].copy_from_slice(&self.resp_len.to_le_bytes());
        out
    }
}

/// A payload being decoded. Every count is checked against the bytes left before anything is allocated for it.
pub struct Reader<'a>(pub &'a [u8]);

impl<'a> Reader<'a> {
    fn bytes(&mut self, len: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(len)?;
        self.0 = rest;
        Some(head)
    }

    pub fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }

    /// `n u32 | n x (pubkey | message)`
    pub fn claims(&mut self) -> Option<EthereumClaims> {
        let count = self.u32()? as usize;
        let raw = self.bytes(count.checked_mul(CLAIM_SIZE)?)?;
        let xmss = raw.as_chunks::<CLAIM_SIZE>().0.iter().map(claim).collect();
        Some(EthereumClaims {
            xmss,
            ..EthereumClaims::default()
        })
    }

    /// `len u64 | bytes`
    pub fn proof(&mut self) -> Option<&'a [u8]> {
        let len = u64::from_le_bytes(self.bytes(8)?.try_into().unwrap());
        self.bytes(usize::try_from(len).ok()?)
    }

    /// `n u32 | n x (pubkey | message | signature)`
    pub fn signatures(&mut self) -> Option<Vec<(LeanXmssPublicKey, Message, LeanXmssSignature)>> {
        let count = self.u32()? as usize;
        let raw = self.bytes(count.checked_mul(TRIPLE_SIZE)?)?;
        let triples = raw.as_chunks::<TRIPLE_SIZE>().0.iter().map(|triple| {
            let (head, signature) = triple.split_first_chunk::<CLAIM_SIZE>().unwrap();
            let (pub_key, message) = claim(head);
            let signature = LeanXmssSignature::from_bytes(signature.try_into().unwrap());
            (pub_key, message, signature)
        });
        Some(triples.collect())
    }

    /// `Some` if the payload was consumed whole.
    pub fn end(self) -> Option<()> {
        self.0.is_empty().then_some(())
    }
}

fn claim(bytes: &[u8; CLAIM_SIZE]) -> (LeanXmssPublicKey, Message) {
    let (pub_key, message) = bytes.split_first_chunk::<PUB_KEY_SIZE>().unwrap();
    (LeanXmssPublicKey::from_bytes(pub_key), message.try_into().unwrap())
}

pub fn put_claims(out: &mut Vec<u8>, claims: &EthereumClaims) {
    out.extend((claims.xmss.len() as u32).to_le_bytes());
    for (pub_key, message) in &claims.xmss {
        out.extend(pub_key.to_bytes());
        out.extend(message);
    }
}

pub fn put_proof(out: &mut Vec<u8>, proof: &[u8]) {
    out.extend((proof.len() as u64).to_le_bytes());
    out.extend(proof);
}

/// `proof | claims`: the response to every op that proves.
pub fn proved(proof: &EthereumProof) -> Vec<u8> {
    let mut out = Vec::new();
    put_proof(&mut out, &proof.proof_bytes());
    put_claims(&mut out, proof.claims());
    out
}
