//! The prover's side of a transcript.

use crate::arith::RoundWeight;
use crate::codec::{Encoding, FromUniform};
use crate::duplex::Blake2sDuplex;
use crate::pow::ProofOfWork;
use crate::proof::ProofTranscript;
use crate::{Challenger, SessionId};
use primitives::field::F192;

/// The prover's transcript: a sponge, and the proof it writes.
///
/// Every prover message is absorbed in the same call that writes it.
/// So no message can reach the proof unbound, or be bound without being sent.
///
/// It is not `Clone`: a copied prover state would let a prover rewind and re-draw challenges.
///
/// # Hidden messages
///
/// A zero-knowledge prover sends some scalars under a one-time pad.
///
/// - While hiding is on, each message is XORed with the pad's next key, used once.
/// - A key is one element of `E`, so it pads one 24-byte message: in `E`, XOR is addition, and `x` travels as `x + key`.
/// - The sponge absorbs the padded bytes, which are all the proof carries.
pub struct ProverState {
    /// The duplex sponge.
    sponge: Blake2sDuplex,
    /// The proof written so far.
    proof: ProofTranscript,
    /// The one-time pad of a zero-knowledge prover.
    pad: Option<OneTimePad>,
}

/// One-time-pad keys, each used once, in order, while hiding is on.
struct OneTimePad {
    /// Every key, one element of `E` each.
    keys: Vec<F192>,
    /// Keys used so far.
    used: usize,
    /// Whether the next message travels under a key.
    hiding: bool,
}

impl OneTimePad {
    /// XOR `bytes` with the next key's encoding.
    ///
    /// # Panics
    ///
    /// Panics on a message other than one key wide, or when the keys run out.
    fn apply(&mut self, bytes: &mut [u8]) {
        let key = *self.keys.get(self.used).expect("a key for every hidden message");
        let key = key.encode();
        assert_eq!(bytes.len(), key.len(), "a key pads one element of E");
        for (b, k) in bytes.iter_mut().zip(key) {
            *b ^= k;
        }
        self.used += 1;
    }
}

impl ProverState {
    /// A transcript for one session, its first message the instance.
    ///
    /// The instance is public: both sides absorb it, and the proof does not carry it.
    ///
    /// # Panics
    ///
    /// Panics on an instance of no bytes, which would bind no statement.
    pub fn new(session: &SessionId, instance: &impl Encoding) -> Self {
        Self {
            sponge: Blake2sDuplex::transcript(session, instance),
            proof: ProofTranscript::default(),
            pad: None,
        }
    }

    /// Copy the exact logical duplex state without changing the transcript.
    #[must_use]
    pub fn context(&self) -> crate::TranscriptContext<primitives::field::F64, [u8; 32]> {
        self.sponge.context()
    }

    /// Absorb a value the verifier already knows, without sending it.
    pub fn public_message(&mut self, value: &impl Encoding) {
        self.sponge.absorb(value.encode().as_ref());
    }

    /// Send a message: absorb it and write it to the proof.
    ///
    /// While hiding is on, it travels under the pad's next key.
    ///
    /// # Panics
    ///
    /// Panics while hiding on a message other than one element of `E`, or when the keys run out.
    pub fn prover_message(&mut self, value: &impl Encoding) {
        let encoded = value.encode();
        match self.pad.as_mut().filter(|pad| pad.hiding) {
            // A hidden message is padded in a copy of its bytes.
            Some(pad) => {
                let mut bytes = encoded.as_ref().to_vec();
                pad.apply(&mut bytes);
                self.send(&bytes);
            }
            None => self.send(encoded.as_ref()),
        }
    }

    /// Absorb bytes and write them to the proof.
    fn send(&mut self, encoded: &[u8]) {
        self.sponge.absorb(encoded);
        self.proof.narg.extend_from_slice(encoded);
    }

    /// Take the one-time-pad keys of a zero-knowledge proof: the `i`-th message sent hidden is padded by `keys[i]`.
    ///
    /// # Panics
    ///
    /// Panics if keys were already given, which would reuse them.
    pub fn set_keys(&mut self, keys: Vec<F192>) {
        assert!(self.pad.is_none(), "a prover takes its keys once");
        self.pad = Some(OneTimePad {
            keys,
            used: 0,
            hiding: false,
        });
    }

    /// Turn hiding on or off for the messages sent next.
    ///
    /// # Panics
    ///
    /// Panics on turning hiding on without keys: no message may go out in the clear by mistake.
    pub fn set_hidden(&mut self, hidden: bool) {
        match &mut self.pad {
            Some(pad) => pad.hiding = hidden,
            None => assert!(!hidden, "hiding needs keys"),
        }
    }

    /// Whether the messages sent next are hidden.
    #[must_use]
    pub fn is_hidden(&self) -> bool {
        self.pad.as_ref().is_some_and(|pad| pad.hiding)
    }

    /// Keys used so far.
    #[must_use]
    pub fn keys_used(&self) -> usize {
        self.pad.as_ref().map_or(0, |pad| pad.used)
    }

    /// The proof written so far, which a verifier may replay.
    #[must_use]
    pub const fn proof(&self) -> &ProofTranscript {
        &self.proof
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
        self.proof.push_hint(bytes);
    }

    /// Send one sumcheck round's polynomial, its coefficients constant first, but the one its claim fixes.
    ///
    /// The verifier rebuilds that coefficient from the claim, so sending it would bind nothing more.
    ///
    /// # Panics
    ///
    /// Panics on fewer than two coefficients.
    pub fn send_round(&mut self, coeffs: &[F192], weight: RoundWeight) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = weight.fixed_index();
        for (i, c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.prover_message(c);
            }
        }
    }

    /// Draw a verifier message from the sponge.
    pub fn verifier_message<T: FromUniform>(&mut self) -> T {
        self.sponge.draw()
    }

    /// Draw `n` verifier messages, in order.
    pub fn verifier_messages<T: FromUniform>(&mut self, n: usize) -> Vec<T> {
        (0..n).map(|_| self.verifier_message()).collect()
    }

    /// Grind `bits` of proof of work, binding the nonce before the next verifier message.
    ///
    /// Zero bits is no step at all: nothing is drawn or sent.
    ///
    /// The nonce is public, so it travels in the clear even while hiding is on.
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
        self.send(&nonce.encode());
    }

    /// The finished proof.
    #[must_use]
    pub fn into_proof(self) -> ProofTranscript {
        self.proof
    }
}

impl Challenger for ProverState {
    fn verifier_message<T: FromUniform>(&mut self) -> T {
        Self::verifier_message(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::VerifierState;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    const INSTANCE: u64 = 3;

    fn session() -> SessionId {
        SessionId::new(b"hidden-scalars-test")
    }

    #[test]
    fn a_hidden_scalar_travels_padded_and_is_bound_as_sent() {
        // Fixture: two keys, and a run that sends one scalar clear, two hidden, then one clear again.
        //
        //     sent:   a        b + k0    c + k1    d
        //     hidden: no       yes       yes       no
        let keys = [F192::new(10, 20, 30), F192::new(40, 50, 60)];
        let [a, b, c, d] = [1, 2, 3, 4].map(|i| F192::new(i, 0, 0));
        let mut ps = ProverState::new(&session(), &INSTANCE);
        ps.set_keys(keys.to_vec());
        ps.prover_message(&a);
        ps.set_hidden(true);
        ps.prover_message(&b);
        ps.prover_message(&c);
        // A nonce is public: it travels in the clear between the hidden scalars.
        ps.challenge_pow(4);
        ps.set_hidden(false);
        ps.prover_message(&d);
        let challenge: F192 = ps.verifier_message();
        assert_eq!(ps.keys_used(), 2);
        let proof = ps.into_proof();

        // The verifier reads the padded values, and draws the prover's challenge from them.
        let mut vs = VerifierState::new(&session(), &INSTANCE, &proof);
        let read: [F192; 3] = std::array::from_fn(|_| vs.prover_message().unwrap());
        assert_eq!(read, [a, b + keys[0], c + keys[1]]);
        vs.check_pow(4).unwrap();
        assert_eq!(vs.prover_message::<F192>(), Ok(d));
        assert_eq!(vs.verifier_message::<F192>(), challenge);
        vs.check_eof().unwrap();
    }

    #[test]
    fn hiding_refuses_what_it_cannot_pad() {
        let refused = |run: fn(&mut ProverState)| {
            let mut ps = ProverState::new(&session(), &INSTANCE);
            catch_unwind(AssertUnwindSafe(|| run(&mut ps))).is_err()
        };

        // A digest is no scalar of `E`: a root sent while hiding is on would otherwise leak or be mangled.
        assert!(refused(|ps| {
            ps.set_keys(vec![F192::ONE]);
            ps.set_hidden(true);
            ps.prover_message(&[0u8; 32]);
        }));

        // One key, two hidden scalars: the second has no key and must not go out in the clear.
        assert!(refused(|ps| {
            ps.set_keys(vec![F192::ONE]);
            ps.set_hidden(true);
            ps.prover_message(&F192::ONE);
            ps.prover_message(&F192::ONE);
        }));

        // No keys at all: hiding cannot be turned on.
        assert!(refused(|ps| ps.set_hidden(true)));

        // Keys are given once, so no key is ever reused.
        assert!(refused(|ps| {
            ps.set_keys(vec![F192::ONE]);
            ps.set_keys(vec![F192::ONE]);
        }));
    }
}
