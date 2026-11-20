//! The protocol's bytes, as `bins/leanvm-sidecar/README.md` specifies them: frames, the hello, and the client's half,
//! requests out and responses in (the server's half is beside the server). Every integer is little-endian; every
//! variable-length field is a `u64` length, then its bytes.

use crate::{Blob, Rejection};
use claims::{AggregateClaims, OutputClaims};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use std::io::{self, Read};

/// The hello's first bytes.
pub(crate) const MAGIC: [u8; 8] = *b"leanvmsc";

/// The protocol's version, which the hello announces right after [`MAGIC`], where every version keeps it.
pub(crate) const VERSION: u32 = 1;

pub(crate) const OP_AGGREGATE: u8 = 1;
pub(crate) const OP_VERIFY: u8 = 2;
pub(crate) const OK: u8 = 0;

pub(crate) type RawLeanXmss = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
pub(crate) type RawLeanSphincs = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);
/// Claims, and the bytes of their proof.
pub(crate) type Proven = (AggregateClaims, Vec<u8>);
/// A request's proof, or why there is none.
pub(crate) type Outcome = Result<Proven, (Rejection, String)>;

/// A frame being built: its length is patched in by [`Self::finish`].
pub(crate) struct Frame(Vec<u8>);

impl Frame {
    pub(crate) fn new() -> Self {
        Self(vec![0; 8])
    }

    pub(crate) fn u8(&mut self, x: u8) {
        self.0.push(x);
    }

    pub(crate) fn u64(&mut self, x: u64) {
        self.0.extend(x.to_le_bytes());
    }

    pub(crate) fn raw(&mut self, bytes: &[u8]) {
        self.0.extend(bytes);
    }

    pub(crate) fn bytes(&mut self, bytes: &[u8]) {
        self.u64(bytes.len() as u64);
        self.raw(bytes);
    }

    pub(crate) fn finish(mut self) -> Vec<u8> {
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
pub(crate) struct Cursor<'a>(pub(crate) &'a [u8]);

impl<'a> Cursor<'a> {
    pub(crate) fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    pub(crate) fn array<const N: usize>(&mut self) -> Option<&'a [u8; N]> {
        self.take(N).map(|bytes| bytes.try_into().unwrap())
    }

    pub(crate) fn u8(&mut self) -> Option<u8> {
        self.array::<1>().map(|[x]| *x)
    }

    fn u32(&mut self) -> Option<u32> {
        self.array().map(|x| u32::from_le_bytes(*x))
    }

    pub(crate) fn u64(&mut self) -> Option<u64> {
        self.array().map(|x| u64::from_le_bytes(*x))
    }

    pub(crate) fn bytes(&mut self) -> Option<&'a [u8]> {
        let len = usize::try_from(self.u64()?).ok()?;
        self.take(len)
    }

    pub(crate) fn claims(&mut self) -> Option<AggregateClaims> {
        AggregateClaims::from_bytes(self.bytes()?)
    }

    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.bytes()?.to_vec()).ok()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// What the server says first on every connection, after [`MAGIC`] and [`VERSION`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Hello {
    pub max_request: u64,
    pub tag: Vec<u8>,
    pub prover: String,
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
        prover: c.string()?,
    };
    c.is_empty().then_some(hello)
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
        f.bytes(proof);
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

pub(crate) fn encode_verify(claims: &AggregateClaims, proof: &[u8]) -> Vec<u8> {
    let mut f = Frame::new();
    f.u8(OP_VERIFY);
    f.bytes(&claims.to_bytes());
    f.bytes(proof);
    f.finish()
}

/// `None` if the body is not a verify request's response.
pub(crate) fn decode_verdict(body: &[u8]) -> Option<Result<bool, (Rejection, String)>> {
    decode(body, |c| match c.u8()? {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    })
}

/// `None` if the body is not an aggregate request's response.
pub(crate) fn decode_response(body: &[u8]) -> Option<Outcome> {
    decode(body, |c| Some((c.claims()?, c.bytes()?.to_vec())))
}

/// A response: `ok` reads what follows status 0, any other status is a rejection and its message.
fn decode<T>(body: &[u8], ok: impl FnOnce(&mut Cursor) -> Option<T>) -> Option<Result<T, (Rejection, String)>> {
    let mut c = Cursor(body);
    let result = match c.u8()? {
        OK => Ok(ok(&mut c)?),
        status => Err((Rejection::from_code(status)?, c.string()?)),
    };
    c.is_empty().then_some(result)
}
