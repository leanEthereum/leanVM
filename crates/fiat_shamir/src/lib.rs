//! Fiat-Shamir state, proof transport, and the verifier's arithmetic over them. The state is a domain-separated chain of BLAKE2s compressions, each one VM hash opcode: the seed from the parameter IV, then every step keyed by the state.

pub mod arith;
pub mod merkle;
pub mod transcript;

use primitives::{F64, F192};

/// `f(a, b) = BLAKE2s(a‖b)` on two 256-bit halves laid out little-endian into
/// 64 bytes, *exactly* the VM's `Blake2s` opcode from the parameter IV: 64 input bytes → 32-byte
/// digest, split back into four field words. It seeds the chain and checks a proof of work;
/// every later step is [`step`], keyed by the state.
///
/// A 64-byte input is one compression, so this is `compress(PARAM_IV, m,
/// t = 64, last = true)` and nothing about the byte-level padding rules can
/// leak into the in-circuit version.
pub fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.as_chunks_mut::<8>().0.iter_mut().zip(a.into_iter().chain(b)) {
        *slot = w.to_bits().to_le_bytes();
    }
    digest_words(&primitives::hash::hash(&input))
}

/// A 32-byte digest as the four little-endian words the chain runs in.
pub fn digest_words(digest: &[u8; 32]) -> [F64; 4] {
    primitives::hash::digest_words(digest).map(F64::new)
}

// Domain-separation tags. EVERY step's block puts its tag in word 7 and its scalar count in word 3
// ([`step_block`]), so one role is one constant in one place. The tag word is
// never adversary-controlled, so distinct constants are all it takes to make two
// roles unable to alias. The seeding block ([`FiatShamirState::new`]) is the
// exception: it is fixed at the head of the chain, so its position is its tag.
/// The tag of an absorbed scalar.
pub const DS_OBSERVE: F64 = F64::new(1);
/// The tag of a challenge.
pub const DS_SQUEEZE: F64 = F64::new(2);
/// The tag of the proof-of-work base.
pub const DS_POW_BASE: F64 = F64::new(3);
/// The tag of a grinding nonce.
pub const DS_POW_NONCE: F64 = F64::new(4);

/// The most grinding bits a proof of work takes: its window is the digest's low word.
pub const MAX_GRINDING_BITS: u32 = 63;

/// `compress(base, (nonce.coefficients()[0].to_bits(), nonce.coefficients()[1].to_bits(), nonce.coefficients()[2].to_bits(), DS_POW_NONCE))` has its low `bits`
/// bits zero: the grinding predicate over the VM compression. A CONTIGUOUS
/// low-bit window rather than byte-wise leading zeros.
///
/// # Panics
///
/// Panics if the grinding exceeds the digest's low word, whose mask would wrap to accept any nonce.
#[inline]
fn pow_bits_ok(base: [F64; 4], nonce: F192, bits: u32) -> bool {
    assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
    let digest = compress(
        base,
        [
            F64::new(nonce.coefficients()[0].to_bits()),
            F64::new(nonce.coefficients()[1].to_bits()),
            F64::new(nonce.coefficients()[2].to_bits()),
            DS_POW_NONCE,
        ],
    )[0];
    digest.to_bits() & ((1u64 << bits) - 1) == 0
}

/// The most scalars one transcript step absorbs.
pub const MAX_PENDING: usize = 2;

/// The 64-byte block of a transcript step absorbing `scalars` (at most [`MAX_PENDING`]) under `tag`.
///
/// The last scalar fills words 4 to 6, the one before it (if any) words 0 to 2; word 3 is their count and word 7 the tag, so a block names its role and its data alone.
///
/// # Panics
///
/// Panics if more than [`MAX_PENDING`] scalars are given.
pub fn step_block(scalars: &[F192], tag: F64) -> [F64; 8] {
    let (first, last) = match *scalars {
        [a, b] => (a, b),
        [b] => (F192::ZERO, b),
        [] => (F192::ZERO, F192::ZERO),
        _ => panic!("a step absorbs at most {MAX_PENDING} scalars"),
    };
    let count = F64::new(scalars.len() as u64);
    [
        F64::new(first.coefficients()[0].to_bits()),
        F64::new(first.coefficients()[1].to_bits()),
        F64::new(first.coefficients()[2].to_bits()),
        count,
        F64::new(last.coefficients()[0].to_bits()),
        F64::new(last.coefficients()[1].to_bits()),
        F64::new(last.coefficients()[2].to_bits()),
        tag,
    ]
}

/// A transcript step: the BLAKE2s compression of `block` into the chaining value `h`, at byte counter 64 and final, one VM hash opcode.
pub fn step(h: [F64; 4], scalars: &[F192], tag: F64) -> [F64; 4] {
    let halves = |w: [F64; 4]| -> [u32; 8] { std::array::from_fn(|i| (w[i / 2].to_bits() >> (32 * (i % 2))) as u32) };
    let mut state = halves(h);
    let block = step_block(scalars, tag);
    let m: [u32; 16] = std::array::from_fn(|i| (block[i / 2].to_bits() >> (32 * (i % 2))) as u32);
    primitives::hash::compress(&mut state, &m, 64, true);
    std::array::from_fn(|i| F64::new(u64::from(state[2 * i]) | u64::from(state[2 * i + 1]) << 32))
}

/// The shared Fiat-Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
///
/// An absorbed scalar waits for the next step, which takes up to [`MAX_PENDING`] of them: a squeeze absorbs the waiting scalars in its own step, and a third scalar first absorbs the two before it.
#[derive(Clone)]
pub struct FiatShamirState {
    /// The 256-bit chaining value: a Merkle-Damgård hash of the transcript's steps so far.
    cv: [F64; 4],
    /// The scalars absorbed since the last step, the first `n_pending`.
    pending: [F192; MAX_PENDING],
    n_pending: usize,
}

impl FiatShamirState {
    const fn at(cv: [F64; 4]) -> Self {
        Self {
            cv,
            pending: [F192::ZERO; MAX_PENDING],
            n_pending: 0,
        }
    }

    /// Seed from two 256-bit digests: `iv` names everything fixed about the
    /// proving environment (the domain, the circuit, the program) and IS the
    /// starting chaining value, and `public_input` is the one block absorbed
    /// before any challenge. So a transcript opens on a single compression, and
    /// the whole statement is bound before anything is sampled; there is no
    /// mid-protocol "observe public data" step to get wrong (or forget).
    pub fn new(iv: [F64; 4], public_input: [F64; 4]) -> Self {
        Self::at(compress(iv, public_input))
    }

    /// Seed a protocol that has no public input of its own: `BLAKE2s(label)` is
    /// the chaining value, which is all a domain separator has to be.
    pub fn from_label(label: &[u8]) -> Self {
        Self::at(digest_words(&primitives::hash::hash(label)))
    }

    /// The waiting scalars.
    fn pending(&self) -> &[F192] {
        &self.pending[..self.n_pending]
    }

    /// Absorb the waiting scalars, if any, in one `OBSERVE` step.
    fn flush(&mut self) {
        self.cv = self.state();
        self.n_pending = 0;
    }

    /// Absorb one 24-byte scalar (three little-endian `K` limbs). It waits for the next step.
    pub fn observe(&mut self, x: F192) {
        if self.n_pending == MAX_PENDING {
            self.flush();
        }
        self.pending[self.n_pending] = x;
        self.n_pending += 1;
    }

    /// Squeeze a challenge and ratchet: the challenge's three limbs are the
    /// first three words of the `SQUEEZE` step absorbing the waiting scalars, whose full output
    /// becomes the new state, domain-separated from absorbs, so a challenge
    /// cannot be confused with a continued absorb. In Fiat-Shamir everything is
    /// public; soundness comes from each challenge being a random-oracle image
    /// of the entire prior transcript.
    pub fn sample(&mut self) -> F192 {
        let out = step(self.cv, self.pending(), DS_SQUEEZE);
        *self = Self::at(out);
        F192::new([
            F64::new(out[0].to_bits()),
            F64::new(out[1].to_bits()),
            F64::new(out[2].to_bits()),
        ])
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// The PoW base, the `POW_BASE` step from [`Self::state`], read without mutating
    /// the live state (the nonce is bound separately by [`Self::absorb_nonce`]).
    fn pow_base(&self) -> [F64; 4] {
        step(self.state(), &[], DS_POW_BASE)
    }

    /// The 256-bit chaining value once the waiting scalars are absorbed.
    pub fn state(&self) -> [F64; 4] {
        if self.n_pending == 0 {
            self.cv
        } else {
            step(self.cv, self.pending(), DS_OBSERVE)
        }
    }

    /// Bind a grinding nonce into the state (both sides, so they stay in lockstep), after the waiting scalars.
    fn absorb_nonce(&mut self, nonce: F192) {
        self.flush();
        self.cv = step(self.cv, &[nonce], DS_POW_NONCE);
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
                if pow_bits_ok(base, F192::new([F64::new(n), F64::new(0), F64::new(0)]), bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        } else {
            const BATCH: usize = 2 * primitives::hash::LANES;
            let mut template = [[0u8; 64]; BATCH];
            for input in &mut template {
                for (slot, word) in input[..32].as_chunks_mut::<8>().0.iter_mut().zip(base) {
                    *slot = word.to_bits().to_le_bytes();
                }
                input[56..].copy_from_slice(&DS_POW_NONCE.to_bits().to_le_bytes());
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
        self.absorb_nonce(F192::new([F64::new(nonce), F64::new(0), F64::new(0)]));
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

use primitives::PrimeCharacteristicRing;

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F192 {
        F192::new([F64::new(k), F64::new(k ^ 0x1234), F64::new(k.rotate_left(17))])
    }

    fn pi(k: u64) -> [F64; 4] {
        std::array::from_fn(|i| F64::new(k + i as u64))
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
    fn fs_binds_how_many_scalars_a_step_absorbs() {
        // `[x]` and `[0, x]` fill the same scalar words; only the count tells them apart.
        let mut a = FiatShamirState::from_label(b"t");
        a.observe(f(1));
        let mut b = FiatShamirState::from_label(b"t");
        b.observe(F192::ZERO);
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
                .find(|&n| pow_bits_ok(base, F192::new([F64::new(n), F64::new(0), F64::new(0)]), bits))
                .unwrap();
            assert_eq!(good, expected, "smallest nonce at {bits} bits");
            let mut verifier = sp.clone();
            assert!(verifier.verify_pow_field(F192::new([F64::new(good), F64::new(0), F64::new(0)]), bits));
            assert_eq!(clone.state(), verifier.state());
        }
    }

    #[test]
    fn pow_accepts_and_binds_full_field_nonce() {
        let mut verifier = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        let base = verifier.pow_base();
        let nonce = (0..u64::MAX)
            .map(|lo| F192::new([F64::new(lo), F64::new(1), F64::new(2)]))
            .find(|&nonce| pow_bits_ok(base, nonce, 8))
            .expect("an 8-bit grind has a solution");

        let mut expected = verifier.clone();
        expected.absorb_nonce(nonce);
        assert!(verifier.verify_pow_field(nonce, 8));
        assert_eq!(verifier.state(), expected.state());

        let mut zero_bits = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        assert!(!zero_bits.verify_pow_field(F192::new([F64::new(0), F64::new(1), F64::new(0)]), 0));
    }

    #[test]
    #[should_panic(expected = "grinding past the digest's low word")]
    fn grinding_past_the_low_word_is_refused() {
        // A 64-bit mask would wrap to zero and accept any nonce.
        let mut verifier = FiatShamirState::new(digest_words(&primitives::hash::hash(b"t")), pi(1));
        verifier.verify_pow_field(F192::new([F64::new(1), F64::new(0), F64::new(0)]), 64);
    }
}
