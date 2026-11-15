//! Fiat-Shamir proof transport, prover side. `add_scalar` transmits and binds together, which is the only way anything enters the state: a transmitted value needs no separate absorb, a value derived from transmitted ones needs none either, and the statement rides the seed the state starts from. So there is no absorb-only method at all. Merkle hints are authenticated by their trees and are not absorbed separately. The reading side is the `verifier` crate's transcript.

use std::marker::PhantomData;

use crate::merkle::{Hash, MerklePath, hash_to_scalars};
use crate::{FiatShamirState, Proof, Scalar, Search, grinding_bits};

/// Writes scalars into the stream and opening phases to the side, the stream in the verifier's field. A long grind
/// searches on `S`.
pub struct ProverState<F, S> {
    fs: FiatShamirState<F>,
    stream: Vec<verifier::E>,
    merkle: Vec<Vec<MerklePath>>,
    search: PhantomData<S>,
}

impl<F: Scalar, S: Search> ProverState<F, S> {
    /// `iv` and `public_input` seed the Fiat-Shamir state (see [`FiatShamirState::new`]).
    pub fn new(iv: [u64; 4], public_input: [u64; 4]) -> Self {
        Self::from_fs(FiatShamirState::new(iv, public_input))
    }

    /// A protocol with no public input of its own, seeded from `label` alone.
    pub fn from_label(label: &[u8]) -> Self {
        Self::from_fs(FiatShamirState::from_label(label))
    }

    fn from_fs(fs: FiatShamirState<F>) -> Self {
        Self {
            fs,
            stream: Vec::new(),
            merkle: Vec::new(),
            search: PhantomData,
        }
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            merkle_openings: self.merkle,
        }
    }

    pub fn sample(&mut self) -> F {
        self.fs.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F> {
        self.fs.sample_vec(n)
    }

    /// Hand the next opening phase's Merkle data to the verifier. Not absorbed:
    /// its binding is the Merkle structure itself.
    pub fn hint_merkle(&mut self, paths: Vec<MerklePath>) {
        self.merkle.push(paths);
    }

    /// Transmit a scalar into the proof AND bind it into the state (the two are
    /// inseparable: you cannot send without binding).
    #[inline]
    pub fn add_scalar(&mut self, x: F) {
        self.fs.observe(x);
        let [c0, c1] = x.to_limbs();
        self.stream.push(verifier::E::new(c0, c1));
    }

    pub fn add_scalars(&mut self, xs: &[F]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    /// Transmit a root as its two scalars, not as a byte string, so the recursion guest replays
    /// one shape for every digest. Sending it is what binds it: no verifier absorbs a root
    /// separately.
    pub fn add_root(&mut self, root: &Hash) {
        self.add_scalars(&hash_to_scalars(root));
    }

    /// Send one sumcheck round polynomial, as its COEFFICIENTS, constant first.
    ///
    /// The message is every coefficient but one: the running claim fixes the
    /// remaining one, which the verifier derives, so it is neither sent nor
    /// bound. Binding it would add nothing, being a function of the claim and the
    /// coefficients already bound. `eq` says whether the round's eq weight was
    /// factored out, which is what decides WHICH coefficient the claim fixes: a
    /// plain round has `h(0) + h(1) = Σ_{i≥1} c_i = claim`, which fixes `c_1`,
    /// and a round whose `eq` weight `r` was factored out has
    /// `(1 + r)·h(0) + r·h(1) = c_0 + r·Σ_{i≥1} c_i = claim`, which fixes `c_0`.
    ///
    /// Then the round's grind: the round's error is its degree over `|E|`, the degree of the whole round
    /// polynomial, eq factor included.
    pub fn add_round_poly(&mut self, coeffs: &[F], eq: bool) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = usize::from(!eq);
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.add_scalar(c);
            }
        }
        self.grind(grinding_bits((coeffs.len() - 1 + usize::from(eq)) as u128));
    }

    /// Proof-of-work grind of `bits` before the next challenge, which divides that verifier message's
    /// round-by-round error by `2^bits` (the prover must redo the work to re-roll it). Binds the nonce and
    /// transmits it on the stream as raw transport (already bound, so NOT re-absorbed). A grind of zero bits
    /// is nothing: no nonce, no permutation.
    pub fn grind(&mut self, bits: u32) {
        if let Some(nonce) = self.fs.grind::<S>(bits) {
            self.stream.push(verifier::E::new(nonce, 0));
        }
    }
}
