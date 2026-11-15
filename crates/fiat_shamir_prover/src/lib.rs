// CREDIT: the duplex challenger of https://github.com/Plonky3/Plonky3 (`challenger`), MIT OR Apache-2.0.
//! The prover's Fiat-Shamir state and proof transport, for both provers. The state is a duplex sponge over
//! Keccak-f\[1600\], in overwrite mode; the verifier's is `verifier`'s transcript, and the proof it writes is a
//! [`verifier::Proof`].
//!
//! The state is 25 lanes: the rate is lanes `0..16` and the capacity lanes `16..25`. Absorbed
//! scalars wait, up to four, and a permutation takes them all: scalar `i` overwrites lanes
//! `4i..4i + 4` with its two limbs, a zero and a domain tag, the rate past the last scalar is zeroed, and
//! the capacity carries over. A fifth scalar, or a challenge, permutes what is waiting; every
//! challenge takes a permutation of its own and is the first two lanes of its output. A grinding
//! nonce waits like a scalar, and the challenge drawn next carries the proof of work in its
//! permutation's third lane, so a grind costs no permutation of its own. So sending
//! a round's coefficients and drawing its challenge is one permutation, and a guest replays it as
//! one `KECCAK` instruction whose rate cells are the scalars and whose capacity cells are the
//! previous output's.

pub mod merkle;
#[cfg(feature = "fuzzing")]
pub mod tamper;
mod transcript;

pub use transcript::ProverState;
pub use verifier::{Proof, RATE_SCALARS, SECURITY_BITS, grinding_bits};

use verifier::Digest;

use keccak256::STATE_LANES;

/// A field element of the challenge field `E`, as its two `K` limbs: what each prover's field implements to run on
/// this transcript.
pub trait Scalar: Copy {
    fn to_limbs(self) -> [u64; 2];
    fn from_limbs(limbs: [u64; 2]) -> Self;
}

impl Scalar for verifier::E {
    fn to_limbs(self) -> [u64; 2] {
        [self.c0, self.c1]
    }

    fn from_limbs([c0, c1]: [u64; 2]) -> Self {
        Self::new(c0, c1)
    }
}

/// Where a long grind searches: the least `i < n` with `f(i)`, if any. Each prover runs it on its own pool.
pub trait Search {
    fn find_first(n: usize, f: &(dyn Fn(usize) -> bool + Sync)) -> Option<usize>;
}

/// A search on the calling thread.
pub struct Sequential;

impl Search for Sequential {
    fn find_first(n: usize, f: &(dyn Fn(usize) -> bool + Sync)) -> Option<usize> {
        (0..n).find(|&i| f(i))
    }
}

/// The rate's lanes, four per scalar.
const RATE_LANES: usize = 4 * RATE_SCALARS;

// Domain tags, the fourth lane of an absorbed scalar (the third is zero). Nonzero, so a scalar never reads as the
// zeroed rate past the last one, and distinct, so a grinding nonce never reads as a sent scalar.
const DS_OBSERVE: u64 = 1;
const DS_POW_NONCE: u64 = 4;

/// The shared Fiat-Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
#[derive(Clone)]
pub struct FiatShamirState<F> {
    /// The next permutation's input: the capacity the last one left, and in the rate the
    /// `n_pending` scalars absorbed since, then zeros.
    state: [u64; STATE_LANES],
    n_pending: usize,
    /// The challenge a grind's permutation drew, which the next [`Self::sample`] returns.
    ground: Option<F>,
}

impl<F: Scalar> FiatShamirState<F> {
    /// Seed from two 256-bit digests, as their words: `iv` names everything fixed about the proving
    /// environment (the domain, the circuit, the program), and `public_input` is the
    /// statement. The first permutation takes both, lanes `0..4` and `4..8` from the zero
    /// state, so the whole statement is bound before anything is sampled; there is no
    /// mid-protocol "observe public data" step to get wrong (or forget).
    pub fn new(iv: [u64; 4], public_input: [u64; 4]) -> Self {
        let mut fs = Self {
            state: [0; STATE_LANES],
            n_pending: 0,
            ground: None,
        };
        fs.state[..8].copy_from_slice([iv, public_input].as_flattened());
        fs.duplex();
        fs
    }

    /// Seed a protocol that has no public input of its own from `label`, whose hash
    /// is all a domain separator has to be.
    pub fn from_label(label: &[u8]) -> Self {
        Self::new(Digest(keccak256::hash(label)).words(), [0; 4])
    }

    /// Permute, taking the waiting scalars, and return the output's first two lanes.
    fn duplex(&mut self) -> F {
        keccak256::keccak_f(&mut self.state);
        let out = F::from_limbs([self.state[0], self.state[1]]);
        self.state[..RATE_LANES].fill(0);
        self.n_pending = 0;
        out
    }

    fn absorb(&mut self, x: F, tag: u64) {
        assert!(self.ground.is_none(), "a grind is followed by a challenge");
        if self.n_pending == RATE_SCALARS {
            self.duplex();
        }
        let i = 4 * self.n_pending;
        let [c0, c1] = x.to_limbs();
        self.state[i..i + 4].copy_from_slice(&[c0, c1, 0, tag]);
        self.n_pending += 1;
    }

    /// The capacity as the five VM cells a permutation reads it from: lane 16 alone, then
    /// lanes 17 to 24 two to a cell. With nothing waiting, it is all a later
    /// permutation keeps, so it is what a guest needs of a seeded state.
    pub fn capacity_cells(&self) -> [F; 5] {
        assert_eq!(
            self.n_pending, 0,
            "the capacity is the whole state only with nothing waiting"
        );
        std::array::from_fn(|c| match c {
            0 => F::from_limbs([self.state[16], 0]),
            _ => F::from_limbs([self.state[15 + 2 * c], self.state[16 + 2 * c]]),
        })
    }

    /// Absorb one scalar.
    pub fn observe(&mut self, x: F) {
        self.absorb(x, DS_OBSERVE);
    }

    /// Squeeze a challenge: a permutation of its own, taking whatever waits, whose
    /// output's first two lanes are the challenge. In Fiat-Shamir everything is
    /// public; soundness comes from each challenge being a random-oracle image of
    /// the entire prior transcript.
    pub fn sample(&mut self) -> F {
        self.ground.take().unwrap_or_else(|| self.duplex())
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce whose permutation, the one drawing the next challenge,
    /// leaves the low `bits` bits of its output's third lane zero; bind it, and keep that challenge for the next
    /// [`Self::sample`]. `bits = 0` is no grind at all. A CONTIGUOUS low-bit window, so a recursive verifier
    /// re-checks it with one bit decomposition (`grind_check` in `guests/lean_ethereum.py`). A long search runs on
    /// `S`.
    pub fn grind<S: Search>(&mut self, bits: u32) -> Option<u64> {
        assert!(bits < 64, "the grinding window fits a lane");
        if bits == 0 {
            return None;
        }
        // Every candidate's input is the state with a zero nonce absorbed, its nonce written into that scalar's
        // first lane.
        let mut base = self.clone();
        base.absorb(F::from_limbs([0, 0]), DS_POW_NONCE);
        let (base, lane) = (base.state, 4 * (base.n_pending - 1));
        // The smallest passing nonce of batch `b`, the nonces `b * BATCH..(b + 1) * BATCH`.
        const BATCH: u64 = 64;
        let batch = |b: u64| {
            let mut states = [base; BATCH as usize];
            for (nonce, state) in (b * BATCH..).zip(&mut states) {
                state[lane] = nonce;
            }
            keccak256::keccak_f_many(&mut states);
            let pass = |(_, state): &(u64, &[u64; STATE_LANES])| state[2] & ((1 << bits) - 1) == 0;
            (b * BATCH..).zip(&states).find(pass).map(|(nonce, _)| nonce)
        };
        // A short search, a few batches, is not worth a dispatch to the pool.
        let nonce = if bits < 10 {
            (0..).find_map(batch)
        } else {
            // Windows of a quarter of the expected search; the first window holding a hit holds the smallest.
            let window = (1u64 << (bits.min(26) - 2)).div_ceil(BATCH);
            (0..).step_by(window as usize).find_map(|w: u64| {
                S::find_first(window as usize, &|i| batch(w + i as u64).is_some()).and_then(|i| batch(w + i as u64))
            })
        };
        let nonce = nonce.expect("a nonce exists");
        self.absorb(F::from_limbs([nonce, 0]), DS_POW_NONCE);
        self.ground = Some(self.duplex());
        Some(nonce)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use verifier::E;

    type State = FiatShamirState<E>;

    fn f(k: u64) -> E {
        E::new(k, k ^ 0x1234)
    }

    fn pi(k: u64) -> [u64; 4] {
        std::array::from_fn(|i| k + i as u64)
    }

    #[test]
    fn fs_binds_the_public_input() {
        let iv = Digest(keccak256::hash(b"t")).words();
        let mut a = State::new(iv, pi(1));
        let mut b = State::new(iv, pi(2));
        assert_ne!(a.sample(), b.sample());
    }

    #[test]
    fn fs_binds_the_iv() {
        let mut a = State::new(Digest(keccak256::hash(b"t")).words(), pi(1));
        let mut b = State::new(Digest(keccak256::hash(b"u")).words(), pi(1));
        assert_ne!(a.sample(), b.sample());
    }

    #[test]
    fn fs_binds_order() {
        let mut a = State::from_label(b"t");
        a.observe(f(1));
        a.observe(f(2));
        let mut b = State::from_label(b"t");
        b.observe(f(2));
        b.observe(f(1));
        assert_ne!(a.sample(), b.sample());
    }

    /// The tags keep a sent zero apart from the zeroed rate, at every fill.
    #[test]
    fn fs_binds_length() {
        for n in 0..9u64 {
            let mut a = State::from_label(b"t");
            let mut b = State::from_label(b"t");
            for k in 0..n {
                a.observe(f(k + 1));
                b.observe(f(k + 1));
            }
            b.observe(E::new(0, 0));
            assert_ne!(a.sample(), b.sample(), "{n} scalars");
        }
    }

    #[test]
    fn grinding_bits_is_the_ceiling_log() {
        assert_eq!(
            [0, 1, 2, 8, 9, 31, 46, 64, 65, 1 << 20].map(grinding_bits),
            [0, 0, 0, 0, 1, 2, 3, 3, 4, 17]
        );
    }

    /// Whether `nonce` passes a `bits` grind from `state`, one permutation at a time.
    fn pow_bits_ok(state: &State, nonce: u64, bits: u32) -> bool {
        let mut probe = state.clone();
        probe.absorb(E::new(nonce, 0), DS_POW_NONCE);
        keccak256::keccak_f(&mut probe.state);
        probe.state[2] & ((1u64 << bits) - 1) == 0
    }

    #[test]
    fn pow_predicate() {
        let mut sp = State::new(Digest(keccak256::hash(b"t")).words(), pi(1));
        sp.observe(f(7));
        for bits in [2, 8, 13, 17] {
            let mut clone = sp.clone();
            let good = clone.grind::<Sequential>(bits).unwrap();
            let expected = (0..=good).find(|&n| pow_bits_ok(&sp, n, bits)).unwrap();
            assert_eq!(good, expected, "smallest nonce at {bits} bits");
            // The grind's own permutation draws the next challenge, and the one after is fresh.
            let mut expected_state = sp.clone();
            expected_state.absorb(E::new(good, 0), DS_POW_NONCE);
            assert_eq!(clone.sample(), expected_state.sample());
            assert_eq!(clone.sample(), expected_state.sample());
        }
    }

    /// A grind of no bits is nothing: no nonce sent, the next challenge unchanged.
    #[test]
    fn a_zero_bit_grind_is_nothing() {
        let mut ground = ProverState::<E, Sequential>::from_label(b"t");
        let mut plain = ProverState::<E, Sequential>::from_label(b"t");
        ground.grind(0);
        assert_eq!(ground.sample(), plain.sample());
        assert!(ground.into_proof().stream.is_empty());
    }
}
