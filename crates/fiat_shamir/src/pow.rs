//! Proof of work: a nonce whose hash with a transcript challenge starts with zero bits.
//!
//! The step follows spongefish's grinding:
//!
//! ```text
//!     challenge = squeeze(32)                                  both sides
//!     nonce     = smallest u64 with work(challenge, nonce)     prover
//!     absorb(nonce), written to the proof                      both sides
//! ```
//!
//! The next challenge then depends on the nonce.
//!
//! So re-rolling that challenge costs `2^bits` hashes on average.

use primitives::hash::{BATCH, hash, hash_many};
use std::sync::atomic::{AtomicU64, Ordering};

/// A proof-of-work difficulty: the number of leading zero bits a nonce's hash must have.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofOfWork {
    /// The leading zero bits required.
    bits: u32,
}

/// The hash a nonce is tried with: one BLAKE2s block.
///
/// ```text
///     BLAKE2s-256( challenge (32) | nonce (8) | zeros (16) | tag (8) )
/// ```
///
/// Nonce and tag are little-endian.
fn trial(challenge: &[u8; 32], nonce: u64) -> [u8; 32] {
    hash(&block(challenge, nonce))
}

/// The 64-byte block a nonce is tried in.
fn block(challenge: &[u8; 32], nonce: u64) -> [u8; 64] {
    let mut block = [0; 64];
    block[..32].copy_from_slice(challenge);
    block[32..40].copy_from_slice(&nonce.to_le_bytes());
    block[56..].copy_from_slice(&ProofOfWork::TRIAL_TAG.to_le_bytes());
    block
}

/// Whether a digest clears `bits` of work: its first eight bytes, little-endian, have their top `bits` bits zero.
const fn clears(digest: &[u8; 32], bits: u32) -> bool {
    let (word, _) = digest.split_first_chunk::<8>().expect("a digest holds a word");
    u64::from_le_bytes(*word).leading_zeros() >= bits
}

impl ProofOfWork {
    /// The largest difficulty: the work reads one 64-bit word of the digest.
    pub const MAX_BITS: u32 = 63;

    /// The last word of every trial block, the bytes `FS-POW-1`.
    ///
    /// It keeps a trial apart from a Merkle node, which is also one block from the parameter IV.
    pub const TRIAL_TAG: u64 = u64::from_le_bytes(*b"FS-POW-1");

    /// The difficulty of `bits` leading zero bits.
    ///
    /// # Panics
    ///
    /// Panics past the largest difficulty.
    #[must_use]
    pub const fn new(bits: u32) -> Self {
        assert!(bits <= Self::MAX_BITS, "proof of work past one digest word");
        Self { bits }
    }

    /// The leading zero bits required.
    #[must_use]
    pub const fn bits(self) -> u32 {
        self.bits
    }

    /// Whether `nonce` is this much work on `challenge`.
    #[must_use]
    pub fn verify(self, challenge: &[u8; 32], nonce: u64) -> bool {
        clears(&trial(challenge, nonce), self.bits)
    }

    /// The smallest nonce that is this much work on `challenge`, searched on the thread pool.
    ///
    /// The smallest, so that a proof is a function of its inputs alone.
    ///
    /// # Panics
    ///
    /// Panics if no 64-bit nonce works.
    #[must_use]
    pub fn grind(self, challenge: &[u8; 32]) -> u64 {
        let bits = self.bits;

        // Small difficulties are searched in order on this thread: the pool would cost more than the work.
        const PARALLEL_MIN_TRIALS: u64 = 1 << 13;
        if (1u64 << bits) < PARALLEL_MIN_TRIALS {
            return (0..=u64::MAX)
                .find(|&nonce| self.verify(challenge, nonce))
                .expect("some nonce works");
        }

        // Larger ones hash `BATCH` nonces per vector call, in windows the pool claims in order.
        //
        //     window w: nonces [w * size, (w + 1) * size)
        //     each task hashes one batch, and records the smallest nonce that works
        //     the first window with a success holds the smallest nonce of all
        let template = block(challenge, 0);
        let best = AtomicU64::new(u64::MAX);
        let batch = |first: u64| {
            let mut blocks = [template; BATCH];
            for (i, block) in blocks.iter_mut().enumerate() {
                block[32..40].copy_from_slice(&(first + i as u64).to_le_bytes());
            }
            let mut digests = [[0u8; 32]; BATCH];
            hash_many::<64>(blocks.as_flattened(), digests.as_flattened_mut());

            // Within a batch the first success is the smallest.
            digests.iter().position(|d| clears(d, bits)).is_some_and(|i| {
                best.fetch_min(first + i as u64, Ordering::Relaxed);
                true
            })
        };

        // A window of about twice the expected work keeps the pool busy and rarely runs empty.
        let size = 1u64 << (bits.min(24) + 1);
        let mut start = 0u64;
        loop {
            let tasks = (size / BATCH as u64) as usize;
            if parallel::find_first(tasks, |i| batch(start + (i * BATCH) as u64)).is_some() {
                return best.load(Ordering::Relaxed);
            }
            start = start.checked_add(size).expect("some nonce works");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grinding_finds_the_smallest_nonce() {
        // For each difficulty, every nonce below the one found fails, and that one passes.
        //
        // 14 bits crosses into the parallel search.
        let challenge = [7; 32];
        for bits in [1, 5, 9, 14] {
            let pow = ProofOfWork::new(bits);
            let nonce = pow.grind(&challenge);
            assert!(pow.verify(&challenge, nonce));
            assert!((0..nonce).all(|n| !pow.verify(&challenge, n)), "{bits} bits");
        }
    }

    #[test]
    fn zero_bits_accept_any_nonce() {
        // No bit is required, so every nonce is work, the smallest being zero.
        let free = ProofOfWork::new(0);
        assert_eq!(free.grind(&[1; 32]), 0);
        assert!(free.verify(&[1; 32], u64::MAX));
    }

    #[test]
    fn work_reads_the_top_bits_of_the_first_word() {
        // A digest whose first word is 2^63 has no leading zero.
        //
        //     word = 0x8000_0000_0000_0000 -> 0 bits of work
        //     word = 0x0000_0000_0000_0001 -> 63 bits of work
        let mut digest = [0; 32];
        digest[7] = 0x80;
        assert!(clears(&digest, 0) && !clears(&digest, 1));
        let mut digest = [0; 32];
        digest[0] = 1;
        assert!(clears(&digest, 63));
    }
}
