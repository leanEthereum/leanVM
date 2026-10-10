//! The verifier's side of a transcript.

use crate::Challenger;
use crate::codec::{Encoding, FromNarg, FromUniform};
use crate::duplex::{Blake2sDuplex, DuplexSponge};
use crate::error::TranscriptError;
use crate::pow::ProofOfWork;
use crate::proof::ProofTranscript;
use crate::session::SessionId;

/// The verifier's transcript: a sponge, and cursors into the proof it reads.
///
/// It mirrors the prover call for call.
///
/// A failed read poisons it: every later read returns the same error.
pub struct VerifierState<'a, H: DuplexSponge = Blake2sDuplex> {
    /// The duplex sponge.
    sponge: H,
    /// The messages not yet read.
    narg: &'a [u8],
    /// The hints not yet read.
    hints: &'a [u8],
    /// Messages read so far.
    messages_read: usize,
    /// Hints read so far.
    hints_read: usize,
    /// The first error, once one occurred.
    poison: Option<TranscriptError>,
}

impl<'a> VerifierState<'a> {
    /// A transcript for one session over the BLAKE2s duplex, its first message the instance, reading `proof`.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no bytes, which would bind no statement.
    pub fn new(session: &SessionId, instance: &impl Encoding, proof: &'a ProofTranscript) -> Self {
        Self::with_sponge(session, instance, proof)
    }
}

impl<'a, H: DuplexSponge> VerifierState<'a, H> {
    /// A transcript for one session over the sponge `H`, its first message the instance, reading `proof`.
    ///
    /// Session and instance must be the prover's, or every challenge differs.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no bytes, which would bind no statement.
    pub fn with_sponge(session: &SessionId, instance: &impl Encoding, proof: &'a ProofTranscript) -> Self {
        let mut sponge = H::init(session.0);
        let encoded = instance.encode();
        assert!(!encoded.as_ref().is_empty(), "an instance has bytes");
        sponge.absorb(encoded.as_ref());
        Self {
            sponge,
            narg: &proof.narg,
            hints: &proof.hints,
            messages_read: 0,
            hints_read: 0,
            poison: None,
        }
    }

    /// Record `result`'s error, if any, so that every later read fails with it.
    fn guard<T>(&mut self, result: Result<T, TranscriptError>) -> Result<T, TranscriptError> {
        if let Err(e) = result {
            self.poison.get_or_insert(e);
        }
        result
    }

    /// Absorb a value the verifier knows, as the prover did.
    pub fn public_message(&mut self, value: &impl Encoding) {
        self.sponge.absorb(value.encode().as_ref());
    }

    /// Read the next message off the proof and absorb it.
    ///
    /// # Errors
    ///
    /// Refuses a proof that ends first, bytes that encode no value, or a poisoned transcript.
    pub fn prover_message<T: FromNarg>(&mut self) -> Result<T, TranscriptError> {
        if let Some(e) = self.poison {
            return Err(e);
        }

        // Read with a copy of the cursor, so that a failed read consumes nothing.
        let mut cursor = self.narg;
        let malformed = TranscriptError::Malformed {
            index: self.messages_read,
        };
        let value = T::from_narg(&mut cursor).ok_or(malformed);
        let value = self.guard(value)?;

        // Absorb the bytes the proof holds, which are the value's one encoding.
        let read = &self.narg[..self.narg.len() - cursor.len()];
        self.sponge.absorb(read);
        self.narg = cursor;
        self.messages_read += 1;
        Ok(value)
    }

    /// Read `n` messages, in order.
    ///
    /// # Errors
    ///
    /// Refuses as reading each message does.
    pub fn prover_messages<T: FromNarg>(&mut self, n: usize) -> Result<Vec<T>, TranscriptError> {
        (0..n).map(|_| self.prover_message()).collect()
    }

    /// Read the next hint, which is not absorbed.
    ///
    /// # Errors
    ///
    /// Refuses a missing hint, a length past the proof's end, or a poisoned transcript.
    pub fn prover_hint(&mut self) -> Result<&'a [u8], TranscriptError> {
        if let Some(e) = self.poison {
            return Err(e);
        }

        // A four-byte little-endian length, then that many bytes; the length is untrusted.
        let missing = TranscriptError::MissingHint { index: self.hints_read };
        let hint = (self.hints.split_first_chunk::<4>())
            .and_then(|(len, rest)| rest.split_at_checked(u32::from_le_bytes(*len) as usize))
            .ok_or(missing);
        let (hint, rest) = self.guard(hint)?;
        self.hints = rest;
        self.hints_read += 1;
        Ok(hint)
    }

    /// Read the next hint and decode it, refusing a hint the decoder refuses.
    ///
    /// The decoder is where a hint is authenticated, such as Merkle paths against their root.
    ///
    /// # Errors
    ///
    /// Refuses as reading a hint does, or a hint the decoder returns nothing for.
    pub fn prover_hint_with<T>(&mut self, decode: impl FnOnce(&'a [u8]) -> Option<T>) -> Result<T, TranscriptError> {
        let index = self.hints_read;
        let hint = self.prover_hint()?;
        let decoded = decode(hint).ok_or(TranscriptError::InvalidHint { index });
        self.guard(decoded)
    }

    /// Draw a verifier message from the sponge.
    pub fn verifier_message<T: FromUniform>(&mut self) -> T {
        let mut repr = T::Repr::default();
        self.sponge.squeeze(repr.as_mut());
        T::from_uniform(repr)
    }

    /// Draw `n` verifier messages, in order.
    pub fn verifier_messages<T: FromUniform>(&mut self, n: usize) -> Vec<T> {
        (0..n).map(|_| self.verifier_message()).collect()
    }

    /// Check `bits` of proof of work: draw the challenge, read the nonce, test it.
    ///
    /// Zero bits is no step at all, as on the prover's side.
    ///
    /// # Errors
    ///
    /// Refuses a missing nonce, or one short of the work.
    ///
    /// # Panics
    ///
    /// Panics past the largest difficulty one digest word holds.
    pub fn check_pow(&mut self, bits: u32) -> Result<(), TranscriptError> {
        let pow = ProofOfWork::new(bits);
        if bits == 0 {
            return Ok(());
        }
        let challenge: [u8; 32] = self.verifier_message();
        let nonce: u64 = self.prover_message()?;
        let worked = pow.verify(&challenge, nonce);
        self.guard(worked.then_some(()).ok_or(TranscriptError::PowFailed { bits }))
    }

    /// Check that the whole proof was read.
    ///
    /// # Errors
    ///
    /// Refuses a proof with bytes left, or a poisoned transcript.
    pub const fn check_eof(&self) -> Result<(), TranscriptError> {
        if let Some(e) = self.poison {
            return Err(e);
        }
        if self.narg.is_empty() && self.hints.is_empty() {
            Ok(())
        } else {
            Err(TranscriptError::TrailingBytes {
                narg: self.narg.len(),
                hints: self.hints.len(),
            })
        }
    }
}

impl<H: DuplexSponge> Challenger for VerifierState<'_, H> {
    fn verifier_message<T: FromUniform>(&mut self) -> T {
        Self::verifier_message(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prover::ProverState;
    use primitives::field::F192;

    const INSTANCE: u64 = 7;

    fn session() -> SessionId {
        SessionId::new(b"transcript-test")
    }

    // A prover run touching every operation, returning its proof and the challenges it drew.
    fn prove() -> (ProofTranscript, [F192; 3]) {
        let mut ps = ProverState::new(&session(), &INSTANCE);
        ps.public_message(&F192::new(1, 2, 3));
        ps.prover_message(&[5u8; 32]);
        let a: F192 = ps.verifier_message();
        ps.prover_messages(&[F192::new(4, 0, 0), F192::new(0, 5, 0)]);
        ps.prover_hint(b"opening");
        ps.challenge_pow(8);
        let b: F192 = ps.verifier_message();
        ps.challenge_pow(0);
        let c: F192 = ps.verifier_message();
        (ps.into_proof(), [a, b, c])
    }

    // The verifier's mirror of the run above, failing at the first refused read.
    fn verify(proof: &ProofTranscript) -> Result<[F192; 3], TranscriptError> {
        let mut vs = VerifierState::new(&session(), &INSTANCE, proof);
        vs.public_message(&F192::new(1, 2, 3));
        assert_eq!(vs.prover_message::<[u8; 32]>()?, [5; 32]);
        let a: F192 = vs.verifier_message();
        vs.prover_messages::<F192>(2)?;
        assert_eq!(vs.prover_hint()?, b"opening");
        vs.check_pow(8)?;
        let b: F192 = vs.verifier_message();
        vs.check_pow(0)?;
        let c: F192 = vs.verifier_message();
        vs.check_eof()?;
        Ok([a, b, c])
    }

    #[test]
    fn the_verifier_replays_the_prover() {
        // Same session, instance and proof: the same challenges, and the proof read to its end.
        let (proof, challenges) = prove();
        assert_eq!(verify(&proof), Ok(challenges));

        // The proof's messages are exactly what was absorbed:
        //
        //     32 (digest) + 2 * 24 (elements) + 8 (nonce) = 88 bytes
        assert_eq!(proof.narg.len(), 88);
        assert_eq!(proof.hints, [&7u32.to_le_bytes()[..], b"opening"].concat());
    }

    #[test]
    fn every_message_byte_is_bound() {
        // Flip each message byte in turn: the read value or a later challenge must change.
        //
        // A flip in the nonce fails its work, any other changes the challenges.
        let (proof, challenges) = prove();
        for i in 0..proof.narg.len() {
            let mut forged = proof.clone();
            forged.narg[i] ^= 1;
            let result = std::panic::catch_unwind(|| verify(&forged));
            assert!(!matches!(result, Ok(Ok(c)) if c == challenges), "byte {i} is not bound");
        }
    }

    #[test]
    fn a_short_or_long_proof_is_refused() {
        let (proof, _) = prove();

        // One message byte short: the nonce, the last message, cannot be read.
        let mut short = proof.clone();
        short.narg.pop();
        assert_eq!(verify(&short), Err(TranscriptError::Malformed { index: 3 }));

        // One hint byte short: the hint's length runs past the end.
        let mut short = proof.clone();
        short.hints.pop();
        assert_eq!(verify(&short), Err(TranscriptError::MissingHint { index: 0 }));

        // One byte too many in either stream: left unread.
        let mut long = proof.clone();
        long.narg.push(0);
        assert_eq!(verify(&long), Err(TranscriptError::TrailingBytes { narg: 1, hints: 0 }));
        let mut long = proof;
        long.hints.push(0);
        assert_eq!(verify(&long), Err(TranscriptError::TrailingBytes { narg: 0, hints: 1 }));
    }

    #[test]
    fn a_failed_read_poisons_the_transcript() {
        // An empty proof: the first read fails, and so does every read after it, even of a hint.
        let empty = ProofTranscript::default();
        let mut vs = VerifierState::new(&session(), &INSTANCE, &empty);
        let first = vs.prover_message::<F192>();
        assert_eq!(first, Err(TranscriptError::Malformed { index: 0 }));
        assert_eq!(vs.prover_hint(), Err(TranscriptError::Malformed { index: 0 }));
        assert_eq!(vs.check_eof(), Err(TranscriptError::Malformed { index: 0 }));
    }

    #[test]
    fn a_hint_its_decoder_refuses_poisons_the_transcript() {
        // The decoder authenticates the hint: refusing it is an invalid hint, and no later read succeeds.
        let (proof, _) = prove();
        let mut vs = VerifierState::new(&session(), &INSTANCE, &proof);
        vs.public_message(&F192::new(1, 2, 3));
        vs.prover_message::<[u8; 32]>().unwrap();
        let _: F192 = vs.verifier_message();
        vs.prover_messages::<F192>(2).unwrap();
        let refused = vs.prover_hint_with(|_| None::<()>);
        assert_eq!(refused, Err(TranscriptError::InvalidHint { index: 0 }));
        assert_eq!(vs.check_pow(8), Err(TranscriptError::InvalidHint { index: 0 }));
    }

    #[test]
    fn session_and_instance_seed_every_challenge() {
        // Change the session or the instance: the first challenge changes.
        let first = |session: SessionId, instance: u64| {
            let mut ps = ProverState::new(&session, &instance);
            ps.verifier_message::<F192>()
        };
        let base = first(session(), INSTANCE);
        assert_ne!(base, first(SessionId::new(b"other"), INSTANCE));
        assert_ne!(base, first(session(), INSTANCE + 1));
    }
}
