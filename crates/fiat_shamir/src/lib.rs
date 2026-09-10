// CREDIT: https://github.com/signalapp/libsignal/blob/main/rust/poksho/src/shosha256.rs, AGPL-3.0-only.
//! Fiat-Shamir state and proof transport. The state is a domain-separated BLAKE2s chain whose 64-byte steps match the VM's hash opcode.

pub mod merkle;
pub mod transcript;

use primitives::field::{F64, F192};

/// `f(a, b) = BLAKE2s(a‖b)` on two 256-bit halves laid out little-endian into
/// 64 bytes, *exactly* the VM's `Blake2s` opcode: 64 input bytes → 32-byte
/// digest, split back into four field words. THE primitive; the chain is a
/// chain of these, so a zkDSL program replays it with one `blake2s(...)` per
/// step.
///
/// A 64-byte input is one compression, so this is `compress(init_state(0), m,
/// t = 64, last = true)` and nothing about the byte-level padding rules can
/// leak into the in-circuit version.
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

// Domain-separation tags. EVERY absorbed block puts its tag in lane 3 and its
// data in lanes 0..=2, so one role is one constant in one place. The tag lane is
// never adversary-controlled, so distinct constants are all it takes to make two
// roles unable to alias. The seeding block ([`FiatShamirState::new`]) is the
// exception: it is fixed at the head of the chain, so its position is its tag.
const DS_OBSERVE: F64 = F64(1);
const DS_SQUEEZE: F64 = F64(2);
const DS_POW_BASE: F64 = F64(3);
const DS_POW_NONCE: F64 = F64(4);

/// `compress(base, (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE))` has its low `bits`
/// bits zero: the grinding predicate over the VM compression. A CONTIGUOUS
/// low-bit window (rather than byte-wise leading zeros) so a recursive verifier
/// re-checks it with a single loop over the bit decomposition of the digest word
/// (`grind_check` in `guests/lean_ethereum.py`). `bits` is always `< 64`.
#[inline]
fn pow_bits_ok(base: [F64; 4], nonce: F192, bits: u32) -> bool {
    debug_assert!(bits < 64, "grinding deficit fits the digest's low word");
    let digest = compress(base, [F64(nonce.c0), F64(nonce.c1), F64(nonce.c2), DS_POW_NONCE])[0];
    digest.0 & ((1u64 << bits) - 1) == 0
}

/// The shared Fiat-Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
#[derive(Clone)]
pub struct FiatShamirState {
    /// The 256-bit chaining value: a Merkle-Damgård hash of the transcript so far.
    cv: [F64; 4],
}

impl FiatShamirState {
    /// Seed from two 256-bit digests: `iv` names everything fixed about the
    /// proving environment (the domain, the circuit, the program) and IS the
    /// starting chaining value, and `public_input` is the one block absorbed
    /// before any challenge. So a transcript opens on a single compression, and
    /// the whole statement is bound before anything is sampled; there is no
    /// mid-protocol "observe public data" step to get wrong (or forget).
    pub fn new(iv: [F64; 4], public_input: [F64; 4]) -> Self {
        Self {
            cv: compress(iv, public_input),
        }
    }

    /// Seed a protocol that has no public input of its own: `BLAKE2s(label)` is
    /// the chaining value, which is all a domain separator has to be.
    pub fn from_label(label: &[u8]) -> Self {
        Self {
            cv: digest_words(&primitives::hash::hash(label)),
        }
    }

    /// Absorb one 24-byte scalar (three little-endian `K` limbs):
    /// `cv ← compress(cv, (c0, c1, c2, DS_OBSERVE))`.
    pub fn observe(&mut self, x: F192) {
        self.cv = compress(self.cv, [F64(x.c0), F64(x.c1), F64(x.c2), DS_OBSERVE]);
    }

    /// Squeeze a challenge and ratchet: the challenge's three limbs are the
    /// first three words of `compress(cv, (0, 0, 0, DS_SQUEEZE))`, whose full output
    /// becomes the new state, domain-separated from absorbs, so a challenge
    /// cannot be confused with a continued absorb. In Fiat-Shamir everything is
    /// public; soundness comes from each challenge being a random-oracle image
    /// of the entire prior transcript.
    pub fn sample(&mut self) -> F192 {
        let out = compress(self.cv, [F64::ZERO, F64::ZERO, F64::ZERO, DS_SQUEEZE]);
        self.cv = out;
        F192::new(out[0].0, out[1].0, out[2].0)
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// The PoW base `compress(cv, (0, 0, 0, DS_POW_BASE))`, read without mutating
    /// the live state (the nonce is bound separately by [`Self::absorb_nonce`]).
    fn pow_base(&self) -> [F64; 4] {
        compress(self.cv, [F64::ZERO, F64::ZERO, F64::ZERO, DS_POW_BASE])
    }

    /// The current 256-bit chaining value.
    pub fn state(&self) -> [F64; 4] {
        self.cv
    }

    /// Bind a grinding nonce into the state (both sides, so they stay in lockstep).
    fn absorb_nonce(&mut self, nonce: F192) {
        self.cv = compress(self.cv, [F64(nonce.c0), F64(nonce.c1), F64(nonce.c2), DS_POW_NONCE]);
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce whose PoW hash clears
    /// `bits` low zero bits, then bind it so later challenges depend on it.
    /// `bits = 0` is the canonical no-work nonce `0`. Parallel search for the
    /// larger grinds.
    pub fn grind_pow(&mut self, bits: u32) -> u64 {
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        let base = self.pow_base();
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
            let mut n: u64 = 0;
            loop {
                if pow_bits_ok(base, F192::new(n, 0, 0), bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        } else {
            const BATCH: usize = 2 * primitives::hash::LANES;
            let mut template = [[0u8; 64]; BATCH];
            for input in &mut template {
                for (slot, word) in input[..32].as_chunks_mut::<8>().0.iter_mut().zip(base) {
                    *slot = word.0.to_le_bytes();
                }
                input[56..].copy_from_slice(&DS_POW_NONCE.0.to_le_bytes());
            }
            let batch = |first: u64| {
                let mut inputs = template;
                for (i, input) in inputs.iter_mut().enumerate() {
                    input[32..40].copy_from_slice(&(first + i as u64).to_le_bytes());
                }
                let mut digests = [[0u8; 32]; BATCH];
                primitives::hash::hash_many::<64>(inputs.as_flattened(), digests.as_flattened_mut());
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
                    break first + batch(first).unwrap() as u64;
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
    /// domain does not weaken grinding: each candidate still requires one hash
    /// and succeeds with probability 2^-bits. Honest provers remain canonical
    /// and search the deterministic u64 subset in [`Self::grind_pow`].
    pub fn verify_pow_field(&mut self, nonce: F192, bits: u32) -> bool {
        let base = self.pow_base();
        let ok = if bits == 0 {
            nonce == F192::ZERO
        } else {
            pow_bits_ok(base, nonce, bits)
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

    #[test]
    fn pow_predicate() {
        let sp = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        let base = sp.pow_base();
        for bits in [0, 8, 13, 17] {
            let mut clone = sp.clone();
            let good = clone.grind_pow(bits);
            let expected = (0..=good)
                .find(|&n| pow_bits_ok(base, F192::new(n, 0, 0), bits))
                .unwrap();
            assert_eq!(good, expected, "smallest nonce at {bits} bits");
            let mut verifier = sp.clone();
            assert!(verifier.verify_pow_field(F192::new(good, 0, 0), bits));
            assert_eq!(clone.state(), verifier.state());
        }
    }

    #[test]
    fn pow_accepts_and_binds_full_field_nonce() {
        let mut verifier = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        let base = verifier.pow_base();
        let nonce = (0..u64::MAX)
            .map(|lo| F192::new(lo, 1, 2))
            .find(|&nonce| pow_bits_ok(base, nonce, 8))
            .expect("an 8-bit grind has a solution");

        let mut expected = verifier.clone();
        expected.absorb_nonce(nonce);
        assert!(verifier.verify_pow_field(nonce, 8));
        assert_eq!(verifier.state(), expected.state());

        let mut zero_bits = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        assert!(!zero_bits.verify_pow_field(F192::new(0, 1, 0), 0));
    }
}
