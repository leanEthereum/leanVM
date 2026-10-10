//! A zero-knowledge prover's randomness: ChaCha20 under a seed drawn from the OS, or given by a test.
//!
//! Nothing it draws ever comes from the transcript: a proof made from the transcript alone would be a deterministic function of the witness, which a verifier could recompute for each guess of the advice.

use primitives::field::{F64, F192};
use rand_chacha::ChaCha20Rng;
use rand_core::{OsRng, RngCore, SeedableRng, TryRngCore};

/// Where a zero-knowledge prover draws its randomness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Randomness {
    /// A fresh seed from the operating system for every proof.
    Os,
    /// One fixed seed, for reproducible tests: two proofs under one seed share their keys, so never reuse one in production.
    #[doc(hidden)]
    Seed([u8; 32]),
}

/// What a stream of the prover's randomness is drawn for, each from its own ChaCha20 stream.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Purpose {
    /// The one-time-pad keys, the outer proof's dummy operands and its mask.
    Keys = 0,
    /// The padding coefficients of the main commitment's lanes.
    Pads = 1,
    /// The main commitment's random lane.
    RandomLane = 2,
    /// The key commitment's mask lane, and the two words past its slots.
    KeyLanes = 3,
    /// The key commitment's lanes' padding.
    KeyPads = 4,
}

/// One proof's randomness: a seed, cut into independent streams by purpose.
pub(crate) struct ZkRng {
    seed: [u8; 32],
}

impl ZkRng {
    /// Words a parallel fill gives each task.
    const CHUNK: usize = 1 << 14;

    /// The randomness of one proof.
    ///
    /// # Panics
    ///
    /// If the operating system gives no randomness.
    pub(crate) fn new(randomness: Randomness) -> Self {
        let seed = match randomness {
            Randomness::Os => {
                let mut seed = [0u8; 32];
                OsRng
                    .try_fill_bytes(&mut seed)
                    .expect("the operating system gives randomness");
                seed
            }
            Randomness::Seed(seed) => seed,
        };
        Self { seed }
    }

    /// The stream drawn for `purpose`.
    pub(crate) fn stream(&self, purpose: Purpose) -> ChaCha20Rng {
        let mut rng = ChaCha20Rng::from_seed(self.seed);
        rng.set_stream(purpose as u64);
        rng
    }

    /// Fill `out` with uniform words of the stream drawn for `purpose`, in parallel: chunk `i` starts at its own position of the stream.
    pub(crate) fn fill_k(&self, purpose: Purpose, out: &mut [F64]) {
        let base = self.stream(purpose);
        parallel::chunks_mut(out, Self::CHUNK, |i, chunk| {
            let mut rng = base.clone();
            // A word is two of ChaCha's 32-bit words.
            rng.set_word_pos((2 * i * Self::CHUNK) as u128);
            for w in chunk {
                *w = F64(rng.next_u64());
            }
        });
    }
}

/// A uniform element of `E`.
pub(crate) fn uniform_e(rng: &mut ChaCha20Rng) -> F192 {
    F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())
}
