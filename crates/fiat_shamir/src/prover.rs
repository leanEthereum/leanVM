//! The prover's side of a transcript.

use crate::Challenger;
use crate::codec::{Encoding, FromUniform};
use crate::duplex::{Blake2sDuplex, DuplexSponge};
use crate::pow::ProofOfWork;
use crate::proof::ProofTranscript;
use crate::session::SessionId;

/// The prover's transcript: a sponge, and the proof it writes.
///
/// Every prover message is absorbed in the same call that writes it.
/// So no message can reach the proof unbound, or be bound without being sent.
///
/// It is not `Clone`: a copied prover state would let a prover rewind and re-draw challenges.
pub struct ProverState<H: DuplexSponge = Blake2sDuplex> {
    /// The duplex sponge.
    sponge: H,
    /// The proof written so far.
    proof: ProofTranscript,
}

impl ProverState {
    /// A transcript for one session over the BLAKE2s duplex, its first message the instance.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no bytes, which would bind no statement.
    pub fn new(session: &SessionId, instance: &impl Encoding) -> Self {
        Self::with_sponge(session, instance)
    }
}

impl<H: DuplexSponge> ProverState<H> {
    /// A transcript for one session over the sponge `H`, its first message the instance.
    ///
    /// The instance is public: both sides absorb it, and the proof does not carry it.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no bytes, which would bind no statement.
    pub fn with_sponge(session: &SessionId, instance: &impl Encoding) -> Self {
        let mut state = Self {
            sponge: H::init(session.0),
            proof: ProofTranscript::default(),
        };
        let encoded = instance.encode();
        assert!(!encoded.as_ref().is_empty(), "an instance has bytes");
        state.sponge.absorb(encoded.as_ref());
        state
    }

    /// Absorb a value the verifier already knows, without sending it.
    pub fn public_message(&mut self, value: &impl Encoding) {
        self.sponge.absorb(value.encode().as_ref());
    }

    /// Send a message: absorb it and write it to the proof.
    pub fn prover_message(&mut self, value: &impl Encoding) {
        let encoded = value.encode();
        self.sponge.absorb(encoded.as_ref());
        self.proof.narg.extend_from_slice(encoded.as_ref());
    }

    /// Send messages, one after another.
    pub fn prover_messages<T: Encoding>(&mut self, values: &[T]) {
        for value in values {
            self.prover_message(value);
        }
    }

    /// Send a hint: write it beside the messages, never absorbed.
    ///
    /// Only data that a bound value authenticates may be a hint, such as a Merkle opening against a sent root.
    ///
    /// # Panics
    ///
    /// Panics on a hint of `2^32` bytes or more.
    pub fn prover_hint(&mut self, bytes: &[u8]) {
        let len = u32::try_from(bytes.len()).expect("a hint under 4 GiB");
        self.proof.hints.extend_from_slice(&len.to_le_bytes());
        self.proof.hints.extend_from_slice(bytes);
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

    /// Grind `bits` of proof of work, binding the nonce before the next verifier message.
    ///
    /// Zero bits is no step at all: nothing is drawn or sent.
    ///
    /// # Panics
    ///
    /// Panics past the largest difficulty one digest word holds.
    pub fn challenge_pow(&mut self, bits: u32) {
        let pow = ProofOfWork::new(bits);
        if bits == 0 {
            return;
        }
        let challenge: [u8; 32] = self.verifier_message();
        let nonce = pow.grind(&challenge);
        self.prover_message(&nonce);
    }

    /// The messages written so far.
    #[must_use]
    pub fn narg_string(&self) -> &[u8] {
        &self.proof.narg
    }

    /// The finished proof.
    #[must_use]
    pub fn into_proof(self) -> ProofTranscript {
        self.proof
    }
}

impl<H: DuplexSponge> Challenger for ProverState<H> {
    fn verifier_message<T: FromUniform>(&mut self) -> T {
        Self::verifier_message(self)
    }
}
