//! The stable prover's aggregation as one function from bytes to bytes, [`leanvm_fv_prove`]: the function the proofs
//! about the x86 binary are about, everything it calls included.
//!
//! The input, every length and count a little-endian `u32`:
//! - `log_inv_rate`, one byte;
//! - the children: a count, then each child's claims and proof (`AggregateClaims::to_bytes`,
//!   `AggregateProof::to_bytes`), each a length and its bytes;
//! - the leanXMSS signatures: a count, then each public key, message and signature;
//! - the leanSPHINCS signatures, the same way.
//!
//! The output: the claims' length, the claims, then the proof. The node publishes every claim it covers
//! (`OutputClaims::All`) and takes no blobs.

use aggregation::{AggregateClaims, AggregateProof, OutputClaims};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};

type P = stable_lean_vm_core::StableProver;

/// A leanXMSS signer: public key, message, signature.
pub type XmssSigner = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
/// A leanSPHINCS signer: public key, message, signature.
pub type SphincsSigner = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);

/// Why [`prove`] wrote no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The input is not one encoding.
    Decode,
    /// The aggregation failed.
    Prove,
    /// The output does not fit.
    OutputTooSmall,
}

/// [`prove`] for a caller outside Rust: the bytes written, or `-1`, `-2`, `-3` for [`Error::Decode`],
/// [`Error::Prove`], [`Error::OutputTooSmall`].
///
/// # Safety
/// `input` is readable for `input_len` bytes, `out` writable for `out_cap` bytes, and the two do not overlap.
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn leanvm_fv_prove(input: *const u8, input_len: usize, out: *mut u8, out_cap: usize) -> isize {
    // SAFETY: the caller's contract.
    let (input, out) = unsafe {
        (
            std::slice::from_raw_parts(input, input_len),
            std::slice::from_raw_parts_mut(out, out_cap),
        )
    };
    match prove(input, out) {
        Ok(written) => written as isize,
        Err(Error::Decode) => -1,
        Err(Error::Prove) => -2,
        Err(Error::OutputTooSmall) => -3,
    }
}

/// Aggregate what `input` encodes into `out`; the bytes written.
///
/// # Errors
/// [`Error`] says why there is no proof.
pub fn prove(input: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    let (log_inv_rate, children, xmss, sphincs) = decode(input).ok_or(Error::Decode)?;
    let (claims, proof, _) =
        aggregation::aggregate::<P>(&children, xmss, sphincs, None, OutputClaims::All, log_inv_rate)
            .map_err(|_| Error::Prove)?;
    let (claims, proof) = (claims.to_bytes(), proof.to_bytes());
    let written = 4 + claims.len() + proof.len();
    let out = out.get_mut(..written).ok_or(Error::OutputTooSmall)?;
    let (len, rest) = out.split_at_mut(4);
    let (claims_out, proof_out) = rest.split_at_mut(claims.len());
    len.copy_from_slice(
        &u32::try_from(claims.len())
            .map_err(|_| Error::OutputTooSmall)?
            .to_le_bytes(),
    );
    claims_out.copy_from_slice(&claims);
    proof_out.copy_from_slice(&proof);
    Ok(written)
}

/// The input [`prove`] reads.
pub fn encode(
    log_inv_rate: u8,
    children: &[(AggregateClaims, AggregateProof)],
    xmss: &[XmssSigner],
    sphincs: &[SphincsSigner],
) -> Vec<u8> {
    let mut out = vec![log_inv_rate];
    let len = |out: &mut Vec<u8>, n: usize| out.extend(u32::try_from(n).expect("a u32 length").to_le_bytes());
    len(&mut out, children.len());
    for (claims, proof) in children {
        for bytes in [claims.to_bytes(), proof.to_bytes()] {
            len(&mut out, bytes.len());
            out.extend(bytes);
        }
    }
    len(&mut out, xmss.len());
    for (pk, message, sig) in xmss {
        out.extend(pk.to_bytes().into_iter().chain(*message).chain(sig.to_bytes()));
    }
    len(&mut out, sphincs.len());
    for (pk, message, sig) in sphincs {
        out.extend(pk.to_bytes().into_iter().chain(*message).chain(sig.to_bytes()));
    }
    out
}

/// Split [`prove`]'s output into the claims and the proof.
pub fn decode_output(output: &[u8]) -> Option<(AggregateClaims, AggregateProof)> {
    let mut r = Reader(output);
    let claims = AggregateClaims::from_bytes(r.bytes()?)?;
    Some((claims, AggregateProof::from_bytes(r.0)?))
}

type Input = (
    usize,
    Vec<(AggregateClaims, AggregateProof)>,
    Vec<XmssSigner>,
    Vec<SphincsSigner>,
);

fn decode(input: &[u8]) -> Option<Input> {
    let mut r = Reader(input);
    let log_inv_rate = usize::from(r.array::<1>()?[0]);
    let children = (0..r.len()?)
        .map(|_| {
            Some((
                AggregateClaims::from_bytes(r.bytes()?)?,
                AggregateProof::from_bytes(r.bytes()?)?,
            ))
        })
        .collect::<Option<_>>()?;
    let xmss = (0..r.len()?)
        .map(|_| {
            let pk = LeanXmssPublicKey::from_bytes(r.array()?);
            Some((pk, *r.array()?, LeanXmssSignature::from_bytes(r.array()?)))
        })
        .collect::<Option<_>>()?;
    let sphincs = (0..r.len()?)
        .map(|_| {
            let pk = LeanSphincsPublicKey::from_bytes(r.array()?);
            Some((pk, *r.array()?, LeanSphincsSignature::from_bytes(r.array()?)))
        })
        .collect::<Option<_>>()?;
    r.0.is_empty().then_some((log_inv_rate, children, xmss, sphincs))
}

struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn array<const N: usize>(&mut self) -> Option<&'a [u8; N]> {
        self.take(N)?.try_into().ok()
    }

    fn len(&mut self) -> Option<usize> {
        usize::try_from(u32::from_le_bytes(*self.array()?)).ok()
    }

    fn bytes(&mut self) -> Option<&'a [u8]> {
        let n = self.len()?;
        self.take(n)
    }
}
