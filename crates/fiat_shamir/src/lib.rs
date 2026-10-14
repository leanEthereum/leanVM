// CREDIT: the duplex challenger of https://github.com/Plonky3/Plonky3 (`challenger`), MIT OR Apache-2.0.
//! Fiat-Shamir state and proof transport. The state is a duplex sponge over the VM's `SHA3` step,
//! one Keccak-f\[1600\] permutation a step, in overwrite mode.
//!
//! The state is 25 lanes: the rate is lanes `0..16`, the eight message cells a `SHA3` instruction
//! reads, and the capacity lanes `16..25`. Absorbed scalars wait, up to four, and a permutation
//! takes them all: scalar `i` overwrites lanes `4i..4i + 4` with its three limbs and a domain tag,
//! the rate past the last scalar is zeroed, and the capacity carries over. A fifth scalar, or a
//! challenge, permutes what is waiting; every challenge takes a permutation of its own and is the
//! first three lanes of its output. So sending a round's coefficients and drawing its challenge is
//! one permutation, and a guest replays a step as one `SHA3` instruction whose message cells are
//! the scalars and whose capacity cells are the previous output's.

pub mod merkle;
pub mod transcript;

use primitives::field::{F64, F192};
use primitives::hash::STATE_LANES;

/// `f(a, b) = SHA3-256(a‖b)` on two 256-bit halves laid out little-endian into
/// 64 bytes, *exactly* one VM `SHA3` instruction from the zero state: 64 input
/// bytes → 32-byte digest, split back into four field words. The Merkle trees'
/// node hash.
pub fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.as_chunks_mut::<8>().0.iter_mut().zip(a.into_iter().chain(b)) {
        *slot = w.0.to_le_bytes();
    }
    digest_words(&primitives::hash::hash(&input))
}

/// A 32-byte digest as the four little-endian words the chain runs in.
pub fn digest_words(digest: &[u8; 32]) -> [F64; 4] {
    std::array::from_fn(|index| F64(u64::from_le_bytes(digest[8 * index..8 * index + 8].try_into().unwrap())))
}

/// Scalars a permutation absorbs.
pub const RATE_SCALARS: usize = 4;

// Domain tags, the fourth lane of an absorbed scalar. Nonzero, so a scalar never reads as the
// zeroed rate past the last one, and distinct, so a grinding nonce never reads as a sent scalar.
const DS_OBSERVE: u64 = 1;
const DS_POW_NONCE: u64 = 4;

/// The shared Fiat-Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
#[derive(Clone)]
pub struct FiatShamirState {
    /// The sponge state the last permutation left.
    state: [u64; STATE_LANES],
    /// The scalars absorbed since, with their tags.
    pending: [(F192, u64); RATE_SCALARS],
    n_pending: usize,
}

impl FiatShamirState {
    /// Seed from two 256-bit digests: `iv` names everything fixed about the proving
    /// environment (the domain, the circuit, the program), and `public_input` is the
    /// statement. The first permutation takes both, lanes `0..4` and `4..8` from the zero
    /// state, so the whole statement is bound before anything is sampled; there is no
    /// mid-protocol "observe public data" step to get wrong (or forget).
    pub fn new(iv: [F64; 4], public_input: [F64; 4]) -> Self {
        let mut state = [0u64; STATE_LANES];
        for (lane, word) in state.iter_mut().zip(iv.into_iter().chain(public_input)) {
            *lane = word.0;
        }
        Self {
            state: primitives::hash::step(&state),
            pending: [(F192::ZERO, 0); RATE_SCALARS],
            n_pending: 0,
        }
    }

    /// Seed a protocol that has no public input of its own from `label`, whose hash
    /// is all a domain separator has to be.
    pub fn from_label(label: &[u8]) -> Self {
        Self::new(digest_words(&primitives::hash::hash(label)), [F64::ZERO; 4])
    }

    /// Permute, taking the waiting scalars into the rate.
    fn duplex(&mut self) {
        let mut input = self.state;
        input[..16].fill(0);
        for (i, &(x, tag)) in self.pending[..self.n_pending].iter().enumerate() {
            input[4 * i..4 * i + 4].copy_from_slice(&[x.c0, x.c1, x.c2, tag]);
        }
        self.state = primitives::hash::step(&input);
        self.n_pending = 0;
    }

    fn absorb(&mut self, x: F192, tag: u64) {
        if self.n_pending == RATE_SCALARS {
            self.duplex();
        }
        self.pending[self.n_pending] = (x, tag);
        self.n_pending += 1;
    }

    /// The capacity as the five VM cells a permutation reads it from: lane 16 alone, then
    /// lanes 17 to 24 two to a cell. With nothing waiting, it is all a later
    /// permutation keeps, so it is what a guest needs of a seeded state.
    pub fn capacity_cells(&self) -> [F192; 5] {
        assert_eq!(
            self.n_pending, 0,
            "the capacity is the whole state only with nothing waiting"
        );
        std::array::from_fn(|c| match c {
            0 => F192::new(self.state[16], 0, 0),
            _ => F192::new(self.state[15 + 2 * c], self.state[16 + 2 * c], 0),
        })
    }

    /// Absorb one scalar.
    pub fn observe(&mut self, x: F192) {
        self.absorb(x, DS_OBSERVE);
    }

    /// Squeeze a challenge: a permutation of its own, taking whatever waits, whose
    /// output's first three lanes are the challenge. In Fiat-Shamir everything is
    /// public; soundness comes from each challenge being a random-oracle image of
    /// the entire prior transcript.
    pub fn sample(&mut self) -> F192 {
        self.duplex();
        F192::new(self.state[0], self.state[1], self.state[2])
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Whether `nonce` passes a `bits` grind here: absorbed as a nonce, the challenge
    /// drawn next has its low `bits` bits zero. A CONTIGUOUS low-bit window, so a
    /// recursive verifier re-checks it with one bit decomposition of the challenge's
    /// first limb (`grind_check` in `guests/lean_ethereum.py`). `bits` is always `< 64`.
    fn pow_bits_ok(&self, nonce: F192, bits: u32) -> bool {
        debug_assert!(bits < 64, "the grinding window fits the challenge's low limb");
        let mut probe = self.clone();
        probe.absorb(nonce, DS_POW_NONCE);
        probe.sample().c0 & ((1u64 << bits) - 1) == 0
    }

    /// Absorb a grinding nonce and draw the challenge it is checked against, which
    /// nothing else uses (both sides, so they stay in lockstep).
    fn absorb_nonce(&mut self, nonce: F192) {
        self.absorb(nonce, DS_POW_NONCE);
        self.sample();
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce clearing `bits` low zero
    /// bits, then bind it so later challenges depend on it. `bits = 0` is the
    /// canonical no-work nonce `0`. Parallel search for the larger grinds.
    pub fn grind_pow(&mut self, bits: u32) -> u64 {
        const PARALLEL_GRIND_MIN: u64 = 1 << 13;
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN {
            (0..)
                .find(|&n| self.pow_bits_ok(F192::new(n, 0, 0), bits))
                .expect("a nonce exists")
        } else {
            // Many candidates at once through the batched hash. A candidate's permutation
            // is one final 128-byte block absorbed into the zeroed rate: the block's
            // padding puts PAD_FIRST and the end bit in lane 16, where the step puts the
            // end bit alone, so the starting state carries PAD_FIRST to cancel it.
            let mut base = self.clone();
            if base.n_pending == RATE_SCALARS {
                base.duplex();
            }
            let slot = base.n_pending;
            let mut init = base.state;
            init[..16].fill(0);
            init[16] ^= u64::from(primitives::hash::PAD_FIRST);
            let mut rate = [0u64; 16];
            for (i, &(x, tag)) in base.pending[..slot].iter().enumerate() {
                rate[4 * i..4 * i + 4].copy_from_slice(&[x.c0, x.c1, x.c2, tag]);
            }
            rate[4 * slot + 3] = DS_POW_NONCE;
            const BATCH: usize = 2 * primitives::hash::LANES;
            let mut template = [[0u8; 128]; BATCH];
            for block in &mut template {
                for (bytes, lane) in block.as_chunks_mut::<8>().0.iter_mut().zip(rate) {
                    *bytes = lane.to_le_bytes();
                }
            }
            let batch = |first: u64| {
                let mut blocks = template;
                for (i, block) in blocks.iter_mut().enumerate() {
                    block[32 * slot..32 * slot + 8].copy_from_slice(&(first + i as u64).to_le_bytes());
                }
                let mut digests = [[0u8; 32]; BATCH];
                primitives::hash::hash_many_dyn_from_state(
                    blocks.as_flattened(),
                    128,
                    &init,
                    digests.as_flattened_mut(),
                );
                digests
                    .iter()
                    .position(|d| u64::from_le_bytes(d[..8].try_into().unwrap()) & ((1u64 << bits) - 1) == 0)
            };
            // The smallest matching batch and its first match give the smallest nonce.
            let block: u64 = 1 << (bits.min(24) + 1);
            let mut start: u64 = 0;
            loop {
                if let Some(i) =
                    parallel::find_first(block as usize / BATCH, |i| batch(start + (i * BATCH) as u64).is_some())
                {
                    let first = start + (i * BATCH) as u64;
                    break first + batch(first).expect("the batch has a match") as u64;
                }
                start = start.saturating_add(block);
            }
        };
        self.absorb_nonce(F192::new(nonce, 0, 0));
        nonce
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check `nonce` clears the `bits`
    /// PoW against the current state, then bind it regardless (so the state stays
    /// in lockstep with an honest prover; a failed check rejects at the call
    /// site). `bits = 0` accepts only the canonical nonce `0`, which keeps proofs
    /// non-malleable at zero-bit grinding sites. Allowing the complete field
    /// domain does not weaken grinding: each candidate still requires one
    /// permutation and succeeds with probability 2^-bits. Honest provers remain
    /// canonical and search the deterministic u64 subset in [`Self::grind_pow`].
    pub fn verify_pow_field(&mut self, nonce: F192, bits: u32) -> bool {
        let ok = if bits == 0 {
            nonce == F192::ZERO
        } else {
            self.pow_bits_ok(nonce, bits)
        };
        self.absorb_nonce(nonce);
        ok
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F192 {
        F192::new(k, k ^ 0x1234, k.rotate_left(17))
    }

    fn pi(k: u64) -> [F64; 4] {
        std::array::from_fn(|i| F64(k + i as u64))
    }

    #[test]
    fn fs_binds_the_public_input() {
        let iv = digest_words(&primitives::hash::hash(b"t"));
        let mut a = FiatShamirState::new(iv, pi(1));
        let mut b = FiatShamirState::new(iv, pi(2));
        assert_ne!(a.sample(), b.sample());
    }

    #[test]
    fn fs_binds_the_iv() {
        let mut a = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        let mut b = FiatShamirState::new(digest_words(&primitives::hash::hash(b"u")), pi(1));
        assert_ne!(a.sample(), b.sample());
    }

    #[test]
    fn fs_binds_order() {
        let mut a = FiatShamirState::from_label(b"t");
        a.observe(f(1));
        a.observe(f(2));
        let mut b = FiatShamirState::from_label(b"t");
        b.observe(f(2));
        b.observe(f(1));
        assert_ne!(a.sample(), b.sample());
    }

    /// The tags keep a sent zero apart from the zeroed rate, at every fill.
    #[test]
    fn fs_binds_length() {
        for n in 0..9u64 {
            let mut a = FiatShamirState::from_label(b"t");
            let mut b = FiatShamirState::from_label(b"t");
            for k in 0..n {
                a.observe(f(k + 1));
                b.observe(f(k + 1));
            }
            b.observe(F192::ZERO);
            assert_ne!(a.sample(), b.sample(), "{n} scalars");
        }
    }
    #[test]
    fn pow_predicate() {
        let mut sp = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        sp.observe(f(7));
        for bits in [0, 8, 13, 17] {
            let mut clone = sp.clone();
            let good = clone.grind_pow(bits);
            let expected = (0..=good)
                .find(|&n| bits == 0 || sp.pow_bits_ok(F192::new(n, 0, 0), bits))
                .unwrap();
            assert_eq!(good, expected, "smallest nonce at {bits} bits");
            let mut verifier = sp.clone();
            assert!(verifier.verify_pow_field(F192::new(good, 0, 0), bits));
            assert_eq!(clone.sample(), verifier.sample());
        }
    }
    #[test]
    fn pow_accepts_and_binds_full_field_nonce() {
        let mut verifier = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        let nonce = (0..u64::MAX)
            .map(|lo| F192::new(lo, 1, 2))
            .find(|&nonce| verifier.pow_bits_ok(nonce, 8))
            .expect("an 8-bit grind has a solution");
        let mut expected = verifier.clone();
        expected.absorb_nonce(nonce);
        assert!(verifier.verify_pow_field(nonce, 8));
        assert_eq!(verifier.sample(), expected.sample());
        let mut zero_bits = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        assert!(!zero_bits.verify_pow_field(F192::new(0, 1, 0), 0));
    }
}
