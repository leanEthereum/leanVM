//! Fiat-Shamir proof transport, prover side. `add_scalar` transmits and binds together, which is the only way anything enters the state: a transmitted value needs no separate absorb, a value derived from transmitted ones needs none either, and the statement rides the seed the state starts from. So there is no absorb-only method at all. Merkle hints are authenticated by their trees and are not absorbed separately. The reading side is the `verifier` crate's transcript.

use crate::FiatShamirState;
use crate::merkle::{Hash, PrunedMerklePaths, hash_to_scalars};
use primitives::field::{F64, F192};

/// A scalar stream and its Merkle opening phases.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Proof {
    pub stream: Vec<F192>,
    pub merkle: Vec<PrunedMerklePaths>,
}

/// Writes scalars into the stream and opening phases to the side.
pub struct ProverState {
    fs: FiatShamirState,
    stream: Vec<F192>,
    merkle: Vec<PrunedMerklePaths>,
}

impl ProverState {
    /// `iv` and `public_input` seed the Fiat-Shamir state (see [`FiatShamirState::new`]).
    pub fn new(iv: [F64; 4], public_input: [F64; 4]) -> Self {
        Self::from_fs(FiatShamirState::new(iv, public_input))
    }

    /// A protocol with no public input of its own, seeded from `label` alone.
    pub fn from_label(label: &[u8]) -> Self {
        Self::from_fs(FiatShamirState::from_label(label))
    }

    fn from_fs(fs: FiatShamirState) -> Self {
        Self {
            fs,
            stream: Vec::new(),
            merkle: Vec::new(),
        }
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            merkle: self.merkle,
        }
    }

    pub fn sample(&mut self) -> F192 {
        self.fs.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        self.fs.sample_vec(n)
    }

    /// Hand the next opening phase's Merkle data to the verifier. Not absorbed:
    /// its binding is the Merkle structure itself.
    pub fn hint_merkle(&mut self, paths: PrunedMerklePaths) {
        self.merkle.push(paths);
    }

    /// Transmit a scalar into the proof AND bind it into the state (the two are
    /// inseparable: you cannot send without binding).
    #[inline]
    pub fn add_scalar(&mut self, x: F192) {
        self.fs.observe(x);
        self.stream.push(x);
    }

    pub fn add_scalars(&mut self, xs: &[F192]) {
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
    pub fn add_round_poly(&mut self, coeffs: &[F192], eq: bool) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = usize::from(!eq);
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.add_scalar(c);
            }
        }
    }

    /// Proof-of-work grind of `bits` before the next challenge, raising that
    /// challenge's Schwartz-Zippel soundness by `bits` (the prover must redo
    /// the PoW to re-roll the challenge). Grinds, binds the nonce into the
    /// state, and transmits it on the stream as raw transport (already bound
    /// by the grind, so it is NOT re-absorbed). `bits = 0` is the canonical
    /// no-work nonce `0`.
    pub fn grind(&mut self, bits: u32) {
        let nonce = self.fs.grind_pow(bits);
        self.stream.push(F192::new(nonce, 0, 0));
    }
}
