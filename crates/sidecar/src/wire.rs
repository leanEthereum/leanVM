//! The protocol's bytes, as `bins/leanvm-sidecar/README.md` specifies them: frames, the hello, requests and
//! responses. Every integer is little-endian; every variable-length field is a `u64` length, then its bytes.

use crate::Rejection;
use aggregation::{AggregateClaims, AggregateProof, OutputClaims};
use lean_da::Blob;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use std::io::{self, Read};

/// The hello's first bytes.
pub(crate) const MAGIC: [u8; 8] = *b"leanvmsc";

/// The protocol's version, which the hello announces right after [`MAGIC`], where every version keeps it.
pub(crate) const VERSION: u32 = 1;

const OP_AGGREGATE: u8 = 1;
const OK: u8 = 0;

const XMSS_RECORD: usize = lean_xmss::PUB_KEY_SIZE + lean_xmss::MESSAGE_LEN + lean_xmss::SIG_SIZE;
const SPHINCS_RECORD: usize = lean_sphincs::PUB_KEY_SIZE + lean_sphincs::MESSAGE_LEN + lean_sphincs::SIG_SIZE;
const BLOB_BYTES: usize = 16 * lean_da::BLOB_SYMBOLS;

pub(crate) type RawLeanXmss = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
pub(crate) type RawLeanSphincs = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);
pub(crate) type Proven = (AggregateClaims, AggregateProof);
/// A request's proof, or why there is none.
pub(crate) type Outcome = Result<Proven, (Rejection, String)>;

/// A frame being built: its length is patched in by [`Self::finish`].
struct Frame(Vec<u8>);

impl Frame {
    fn new() -> Self {
        Self(vec![0; 8])
    }

    fn u8(&mut self, x: u8) {
        self.0.push(x);
    }

    fn u64(&mut self, x: u64) {
        self.0.extend(x.to_le_bytes());
    }

    fn raw(&mut self, bytes: &[u8]) {
        self.0.extend(bytes);
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.u64(bytes.len() as u64);
        self.raw(bytes);
    }

    fn finish(mut self) -> Vec<u8> {
        let len = (self.0.len() as u64 - 8).to_le_bytes();
        self.0[..8].copy_from_slice(&len);
        self.0
    }
}

/// What [`read_frame`] read.
pub(crate) enum Incoming {
    Body(Vec<u8>),
    /// The stream ended cleanly, between frames.
    End,
    /// A frame longer than the reader takes: its announced length. The body is left unread.
    TooLarge(u64),
}

/// Reads one frame. A body is read as it arrives, so a forged length allocates nothing it does not receive.
pub(crate) fn read_frame(r: &mut impl Read, max_len: u64) -> io::Result<Incoming> {
    let mut len = [0; 8];
    let mut got = 0;
    while got < len.len() {
        match r.read(&mut len[got..]) {
            Ok(0) if got == 0 => return Ok(Incoming::End),
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => got += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    let len = u64::from_le_bytes(len);
    if len > max_len {
        return Ok(Incoming::TooLarge(len));
    }
    let mut body = Vec::new();
    r.take(len).read_to_end(&mut body)?;
    if body.len() as u64 != len {
        return Err(io::ErrorKind::UnexpectedEof.into());
    }
    Ok(Incoming::Body(body))
}

/// Reads fields off the front of a body.
struct Cursor<'a>(&'a [u8]);

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn array<const N: usize>(&mut self) -> Option<&'a [u8; N]> {
        self.take(N).map(|bytes| bytes.try_into().unwrap())
    }

    fn u8(&mut self) -> Option<u8> {
        self.array::<1>().map(|[x]| *x)
    }

    fn u32(&mut self) -> Option<u32> {
        self.array().map(|x| u32::from_le_bytes(*x))
    }

    fn u64(&mut self) -> Option<u64> {
        self.array().map(|x| u64::from_le_bytes(*x))
    }

    fn bytes(&mut self) -> Option<&'a [u8]> {
        let len = usize::try_from(self.u64()?).ok()?;
        self.take(len)
    }

    /// A count of records of `size` bytes each, all of which must follow: a forged count allocates nothing.
    fn count(&mut self, size: usize) -> Option<usize> {
        let n = usize::try_from(self.u64()?).ok()?;
        (n.checked_mul(size)? <= self.0.len()).then_some(n)
    }

    /// A count of records of `size` bytes each, then the records, each read by `record`.
    fn records<T>(&mut self, size: usize, record: impl Fn(&mut Self) -> T) -> Option<Vec<T>> {
        let n = self.count(size)?;
        Some((0..n).map(|_| record(self)).collect())
    }

    fn claims(&mut self) -> Option<AggregateClaims> {
        AggregateClaims::from_bytes(self.bytes()?)
    }

    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.bytes()?.to_vec()).ok()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// What the server says first on every connection, after [`MAGIC`] and [`VERSION`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Hello {
    pub max_request: u64,
    pub tag: Vec<u8>,
    /// The aggregation program's Fiat-Shamir IV, which pins the program and the verifier tag.
    pub program: [u8; 32],
    pub prover: String,
}

pub(crate) fn encode_hello(hello: &Hello) -> Vec<u8> {
    let mut f = Frame::new();
    f.raw(&MAGIC);
    f.raw(&VERSION.to_le_bytes());
    f.u64(hello.max_request);
    f.bytes(&hello.tag);
    f.raw(&hello.program);
    f.bytes(hello.prover.as_bytes());
    f.finish()
}

/// The version a hello announces, `None` unless the body starts with [`MAGIC`].
pub(crate) fn hello_version(body: &[u8]) -> Option<u32> {
    let mut c = Cursor(body);
    (c.array::<8>()? == &MAGIC).then(|| c.u32())?
}

/// `None` unless the body is a whole hello of this version's layout.
pub(crate) fn decode_hello(body: &[u8]) -> Option<Hello> {
    let mut c = Cursor(body);
    hello_version(c.take(12)?)?;
    let hello = Hello {
        max_request: c.u64()?,
        tag: c.bytes()?.to_vec(),
        program: *c.array()?,
        prover: c.string()?,
    };
    c.is_empty().then_some(hello)
}

/// An `aggregate` call, as the server decodes it.
pub(crate) struct Request {
    pub children: Vec<Proven>,
    pub raw_lean_xmss: Vec<RawLeanXmss>,
    pub raw_lean_sphincs: Vec<RawLeanSphincs>,
    pub blobs: Vec<Blob>,
    /// `None` for [`OutputClaims::All`].
    pub output: Option<AggregateClaims>,
    pub log_inv_rate: usize,
}

pub(crate) fn encode_request(
    children: &[Proven],
    raw_lean_xmss: &[RawLeanXmss],
    raw_lean_sphincs: &[RawLeanSphincs],
    blobs: &[Blob],
    output: OutputClaims,
    log_inv_rate: usize,
) -> Vec<u8> {
    let mut f = Frame::new();
    f.u8(OP_AGGREGATE);
    // A rate past a byte is out of range anyway: the server refuses it as it would any other.
    f.u8(u8::try_from(log_inv_rate).unwrap_or(u8::MAX));
    f.u64(children.len() as u64);
    for (claims, proof) in children {
        f.bytes(&claims.to_bytes());
        f.bytes(&proof.to_bytes());
    }
    f.u64(raw_lean_xmss.len() as u64);
    for (pk, message, signature) in raw_lean_xmss {
        f.raw(&pk.to_bytes());
        f.raw(message);
        f.raw(&signature.to_bytes());
    }
    f.u64(raw_lean_sphincs.len() as u64);
    for (pk, message, signature) in raw_lean_sphincs {
        f.raw(&pk.to_bytes());
        f.raw(message);
        f.raw(&signature.to_bytes());
    }
    f.u64(blobs.len() as u64);
    for blob in blobs {
        for symbol in blob {
            f.raw(&symbol.to_le_bytes());
        }
    }
    match output {
        OutputClaims::All => f.u8(0),
        OutputClaims::Only(claims) => {
            f.u8(1);
            f.bytes(&claims.to_bytes());
        }
    }
    f.finish()
}

pub(crate) fn decode_request(body: &[u8]) -> Result<Request, (Rejection, String)> {
    let malformed = |what: &str| (Rejection::Malformed, format!("malformed request: {what}"));
    let mut c = Cursor(body);
    match c.u8() {
        Some(OP_AGGREGATE) => {}
        Some(op) => return Err((Rejection::Malformed, format!("unknown operation {op}"))),
        None => return Err(malformed("empty")),
    }
    let log_inv_rate = c.u8().ok_or_else(|| malformed("no rate"))?.into();

    // Each child is at least its two lengths. Nothing is reserved: `aggregate` bounds the count, not this.
    let n = c.count(16).ok_or_else(|| malformed("children"))?;
    let mut children = Vec::new();
    for i in 0..n {
        let claims = c.claims().ok_or_else(|| malformed(&format!("child {i}'s claims")))?;
        let proof = c.bytes().ok_or_else(|| malformed(&format!("child {i}'s proof")))?;
        let proof = AggregateProof::from_bytes(proof)
            .ok_or_else(|| (Rejection::InvalidChild, format!("child {i}'s proof does not decode")))?;
        children.push((claims, proof));
    }

    let raw_lean_xmss = c
        .records(XMSS_RECORD, |c| {
            let pk = LeanXmssPublicKey::from_bytes(c.array().unwrap());
            (
                pk,
                *c.array().unwrap(),
                LeanXmssSignature::from_bytes(c.array().unwrap()),
            )
        })
        .ok_or_else(|| malformed("leanXMSS signatures"))?;
    let raw_lean_sphincs = c
        .records(SPHINCS_RECORD, |c| {
            let pk = LeanSphincsPublicKey::from_bytes(c.array().unwrap());
            (
                pk,
                *c.array().unwrap(),
                LeanSphincsSignature::from_bytes(c.array().unwrap()),
            )
        })
        .ok_or_else(|| malformed("leanSPHINCS signatures"))?;

    let n = c.count(BLOB_BYTES).ok_or_else(|| malformed("blobs"))?;
    let mut blobs = vec![[0; lean_da::BLOB_SYMBOLS]; n];
    for blob in &mut blobs {
        let bytes = c.take(BLOB_BYTES).unwrap();
        for (symbol, bytes) in blob.iter_mut().zip(bytes.as_chunks::<16>().0) {
            *symbol = u128::from_le_bytes(*bytes);
        }
    }

    let output = match c.u8() {
        Some(0) => None,
        Some(1) => Some(c.claims().ok_or_else(|| malformed("output claims"))?),
        _ => return Err(malformed("output")),
    };
    if !c.is_empty() {
        return Err(malformed("trailing bytes"));
    }
    Ok(Request {
        children,
        raw_lean_xmss,
        raw_lean_sphincs,
        blobs,
        output,
        log_inv_rate,
    })
}

pub(crate) fn encode_response(result: &Outcome) -> Vec<u8> {
    let mut f = Frame::new();
    match result {
        Ok((claims, proof)) => {
            f.u8(OK);
            f.bytes(&claims.to_bytes());
            f.bytes(&proof.to_bytes());
        }
        Err((rejection, message)) => {
            f.u8(*rejection as u8);
            f.bytes(message.as_bytes());
        }
    }
    f.finish()
}

/// `None` if the body is not a response.
pub(crate) fn decode_response(body: &[u8]) -> Option<Outcome> {
    let mut c = Cursor(body);
    let result = match c.u8()? {
        OK => Ok((c.claims()?, AggregateProof::from_bytes(c.bytes()?)?)),
        status => Err((Rejection::from_code(status)?, c.string()?)),
    };
    c.is_empty().then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn body(frame: Vec<u8>) -> Vec<u8> {
        assert_eq!(
            u64::from_le_bytes(frame[..8].try_into().unwrap()),
            frame.len() as u64 - 8
        );
        frame[8..].to_vec()
    }

    #[test]
    fn hello_round_trips() {
        let hello = Hello {
            max_request: 1 << 30,
            tag: verifier::TAG.to_vec(),
            program: [7; 32],
            prover: "stable".into(),
        };
        let bytes = body(encode_hello(&hello));
        assert_eq!(hello_version(&bytes), Some(VERSION));
        assert_eq!(decode_hello(&bytes), Some(hello));
        assert_eq!(decode_hello(&bytes[..bytes.len() - 1]), None);
        assert_eq!(decode_hello(&[&bytes[..], &[0]].concat()), None);
        let mut other = bytes.clone();
        other[0] ^= 1;
        assert_eq!(hello_version(&other), None);
    }

    /// A request decodes to what was encoded; every truncation, and a trailing byte, is refused, never a panic.
    #[test]
    fn requests_round_trip_and_truncations_are_refused() {
        let xmss = (
            LeanXmssPublicKey::from_bytes(&[1; 32]),
            [2; 32],
            LeanXmssSignature::from_bytes(&std::array::from_fn(|i| i as u8)),
        );
        let sphincs = (
            LeanSphincsPublicKey::from_bytes(&[3; 32]),
            [4; 32],
            LeanSphincsSignature::from_bytes(&std::array::from_fn(|i| (i * 7) as u8)),
        );
        let blob: Blob = std::array::from_fn(|i| ((i as u128) << 100) | i as u128);
        let only = AggregateClaims {
            lean_xmss: vec![(xmss.0, xmss.1)],
            lean_sphincs: vec![(sphincs.0, sphincs.1)],
            da_commitment: Some([5; 32]),
        };
        let frame = encode_request(
            &[],
            std::slice::from_ref(&xmss),
            std::slice::from_ref(&sphincs),
            &[blob],
            OutputClaims::Only(&only),
            3,
        );
        let bytes = body(frame);
        let request = decode_request(&bytes).unwrap_or_else(|(_, m)| panic!("{m}"));
        assert!(request.children.is_empty());
        assert_eq!(request.raw_lean_xmss, vec![xmss]);
        assert_eq!(request.raw_lean_sphincs, vec![sphincs]);
        assert_eq!(request.blobs, vec![blob]);
        assert_eq!(request.output, Some(only));
        assert_eq!(request.log_inv_rate, 3);
        for len in 0..bytes.len() {
            assert!(
                decode_request(&bytes[..len]).is_err(),
                "a prefix of {len} bytes decoded"
            );
        }
        assert!(decode_request(&[&bytes[..], &[0]].concat()).is_err());
        // A count no body could hold.
        let mut huge = vec![OP_AGGREGATE, 1];
        huge.extend(u64::MAX.to_le_bytes());
        assert!(decode_request(&huge).is_err());
    }

    #[test]
    fn rejections_round_trip() {
        let rejection = (Rejection::InvalidInput, "log_inv_rate out of range".to_string());
        let bytes = body(encode_response(&Err(rejection.clone())));
        assert_eq!(decode_response(&bytes).unwrap().unwrap_err(), rejection);
        assert!(decode_response(&[42, 0, 0, 0, 0, 0, 0, 0, 0]).is_none());
    }
}
