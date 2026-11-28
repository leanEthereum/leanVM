//! The stable prover's aggregation as one function from bytes to bytes, [`leanvm_fv_prove`]: the function the proofs
//! about the x86 binary are about, everything it calls included.
//!
//! The guest is an input of its own, the compiled aggregation program (`Program::to_bytes` of
//! `aggregation::unified_guest`), so the binary holds no compiler. The other input, every length and count a
//! little-endian `u32`:
//! - `log_inv_rate`, one byte;
//! - the children: a count, then each child's claims (`AggregateClaims::to_bytes`, a length and its bytes) and proof,
//!   its Merkle paths in full: the deferred point and the stream, each a count and its elements as two little-endian
//!   `u64` words, then the phases, a count and each phase's paths, a count and each path's leaf index (a `u64`), leaf
//!   (a count and its `u64` words) and siblings (a count and their 32 bytes);
//! - the leanXMSS signatures: a count, then each public key, message and signature;
//! - the leanSPHINCS signatures, the same way.
//!
//! The output: the claims' length, the claims, then the proof. The node publishes every claim it covers
//! (`OutputClaims::All`) and takes no blobs.

use aggregation::{AggregateClaims, AggregateProof, OutputClaims};
use isa::Program;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use stable_lean_vm_core::cpu::from_scalar;
use verifier::{E, K, MerklePath, Proof};

type P = stable_lean_vm_core::StableProver;

/// A leanXMSS signer: public key, message, signature.
pub type XmssSigner = (LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature);
/// A leanSPHINCS signer: public key, message, signature.
pub type SphincsSigner = (LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature);

/// Why [`prove`] wrote no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The guest is not one program's encoding.
    Guest,
    /// The input is not one encoding.
    Decode,
    /// The aggregation failed.
    Prove,
    /// The output does not fit.
    OutputTooSmall,
}

/// [`prove`] for a caller outside Rust: the bytes written, or `-1`, `-2`, `-3`, `-4` for [`Error::Decode`],
/// [`Error::Prove`], [`Error::OutputTooSmall`], [`Error::Guest`].
///
/// # Safety
/// `guest` and `input` are readable for `guest_len` and `input_len` bytes, `out` writable for `out_cap` bytes, and
/// `out` overlaps neither.
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn leanvm_fv_prove(
    guest: *const u8,
    guest_len: usize,
    input: *const u8,
    input_len: usize,
    out: *mut u8,
    out_cap: usize,
) -> isize {
    // SAFETY: the caller's contract.
    let (guest, input, out) = unsafe {
        (
            std::slice::from_raw_parts(guest, guest_len),
            std::slice::from_raw_parts(input, input_len),
            std::slice::from_raw_parts_mut(out, out_cap),
        )
    };
    match prove(guest, input, out) {
        Ok(written) => written as isize,
        Err(Error::Decode) => -1,
        Err(Error::Prove) => -2,
        Err(Error::OutputTooSmall) => -3,
        Err(Error::Guest) => -4,
    }
}

/// Aggregate what `input` encodes into `out`, on the guest `guest` encodes; the bytes written. The first call's guest
/// stays for the process.
///
/// # Errors
/// [`Error`] says why there is no proof.
pub fn prove(guest: &[u8], input: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    aggregation::set_unified_guest(Program::from_bytes(guest).ok_or(Error::Guest)?);
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
    let words = |out: &mut Vec<u8>, words: &[u64]| {
        len(out, words.len() / 2);
        out.extend(words.iter().flat_map(|w| w.to_le_bytes()));
    };
    for (claims, proof) in children {
        let claims = claims.to_bytes();
        len(&mut out, claims.len());
        out.extend(claims);
        let (point, proof) = proof.__parts();
        words(&mut out, &point.iter().flat_map(|x| [x.c0, x.c1]).collect::<Vec<_>>());
        words(
            &mut out,
            &proof.stream.iter().flat_map(|x| [x.c0, x.c1]).collect::<Vec<_>>(),
        );
        len(&mut out, proof.merkle_openings.len());
        for phase in &proof.merkle_openings {
            len(&mut out, phase.len());
            for path in phase {
                out.extend(path.leaf_index.to_le_bytes());
                len(&mut out, path.leaf.len());
                out.extend(path.leaf.iter().flat_map(|w| w.0.to_le_bytes()));
                len(&mut out, path.siblings.len());
                out.extend(path.siblings.as_flattened());
            }
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
    let (mut children, mut xmss, mut sphincs) = (Vec::new(), Vec::new(), Vec::new());
    for _ in 0..r.len()? {
        let claims = AggregateClaims::from_bytes(r.bytes()?)?;
        children.push((claims, r.proof()?));
    }
    for _ in 0..r.len()? {
        let pk = LeanXmssPublicKey::from_bytes(r.array()?);
        xmss.push((pk, *r.array()?, LeanXmssSignature::from_bytes(r.array()?)));
    }
    for _ in 0..r.len()? {
        let pk = LeanSphincsPublicKey::from_bytes(r.array()?);
        sphincs.push((pk, *r.array()?, LeanSphincsSignature::from_bytes(r.array()?)));
    }
    if !r.0.is_empty() {
        return None;
    }
    Some((log_inv_rate, children, xmss, sphincs))
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

    fn word(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(*self.array()?))
    }

    fn scalars(&mut self) -> Option<Vec<E>> {
        let mut out = Vec::new();
        for _ in 0..self.len()? {
            out.push(E::new(self.word()?, self.word()?));
        }
        Some(out)
    }

    /// A child's proof, as [`encode`] writes it. Every item takes input bytes, so a forged count allocates little.
    fn proof(&mut self) -> Option<AggregateProof> {
        let point = self.scalars()?.into_iter().map(from_scalar).collect();
        let stream = self.scalars()?;
        let mut merkle_openings = Vec::new();
        for _ in 0..self.len()? {
            let mut paths = Vec::new();
            for _ in 0..self.len()? {
                let leaf_index = self.word()?;
                let mut leaf = Vec::new();
                for _ in 0..self.len()? {
                    leaf.push(K(self.word()?));
                }
                let mut siblings = Vec::new();
                for _ in 0..self.len()? {
                    siblings.push(*self.array()?);
                }
                paths.push(MerklePath {
                    leaf_index,
                    leaf,
                    siblings,
                });
            }
            merkle_openings.push(paths);
        }
        AggregateProof::__from_parts(
            point,
            Proof {
                stream,
                merkle_openings,
            },
        )
    }
}
