// CREDIT: the duplex challenger of https://github.com/Plonky3/Plonky3 (`challenger`), MIT OR Apache-2.0.
//! The prover's Fiat-Shamir state and proof transport, for both provers. The state is a duplex sponge over
//! Keccak-f\[1600\], in overwrite mode; the verifier's is `verifier`'s transcript, and the proof it writes is a
//! [`verifier::Proof`].
//!
//! The state is 25 lanes: the rate is lanes `0..16` and the capacity lanes `16..25`. Absorbed
//! scalars wait, up to four, and a permutation takes them all: scalar `i` overwrites lanes
//! `4i..4i + 4` with its two limbs, a zero and a domain tag, the rate past the last scalar is zeroed, and
//! the capacity carries over. A fifth scalar, or a challenge, permutes what is waiting; every
//! challenge outside a packed draw takes a permutation of its own and is the first two lanes of its
//! output. A grinding nonce waits like a scalar, and the challenge drawn next carries the proof of work in its
//! permutation's third lane, so a grind costs no permutation of its own. So sending
//! a round's coefficients and drawing its challenge is one permutation, and a guest replays it as
//! one `KECCAK` instruction whose rate cells are the scalars and whose capacity cells are the
//! previous output's.
//!
//! A packed message ([`FiatShamirState::observe_packed`]) takes eight scalars a permutation, two lanes each and no
//! tag, and a packed draw ([`FiatShamirState::sample_packed`]) eight challenges a permutation, its whole rate. Their
//! lengths are fixed by the protocol's schedule and nothing marks them, so a packed message can spell the same
//! permutation input as tagged scalars, or as a nonce and its permutation: what keeps them apart is that the prover
//! and every verifier read one fixed schedule, each message's kind and length set by the protocol and the shape
//! before it, not by the tags.

pub mod merkle;
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
/// The rate as challenges, two lanes to a cell.
const RATE_CELLS: usize = RATE_LANES / 2;

// Domain tags, the fourth lane of an absorbed scalar (the third is zero); a packed message has none (see the module
// docs).
use verifier::{DS_OBSERVE, DS_POW_NONCE};

/// The shared Fiat-Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
#[derive(Clone)]
pub struct FiatShamirState<F> {
    /// The next permutation's input: the capacity the last one left, and in the rate the
    /// `n_pending` scalars absorbed since, then zeros.
    state: [u64; STATE_LANES],
    n_pending: usize,
    /// A grind's permutation's rate but the proof of work's cell: its first is the next [`Self::sample`], all seven
    /// the next [`Self::sample_packed`].
    ground: Option<[F; RATE_CELLS - 1]>,
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

    /// Permute, taking the waiting scalars, and return the output's rate, two lanes to a cell.
    fn permute(&mut self) -> [F; RATE_CELLS] {
        keccak256::keccak_f(&mut self.state);
        let cells = std::array::from_fn(|i| F::from_limbs([self.state[2 * i], self.state[2 * i + 1]]));
        self.state[..RATE_LANES].fill(0);
        self.n_pending = 0;
        cells
    }

    /// Permute, taking the waiting scalars, and return the output's first two lanes.
    fn duplex(&mut self) -> F {
        self.permute()[0]
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

    /// Absorb `xs` eight to a permutation, each over two rate lanes, the last permutation's rate zero past them,
    /// after a permutation taking whatever waits.
    pub fn observe_packed(&mut self, xs: &[F]) {
        assert!(self.ground.is_none(), "a grind is followed by a challenge");
        if self.n_pending > 0 {
            self.duplex();
        }
        for chunk in xs.chunks(RATE_CELLS) {
            for (i, x) in chunk.iter().enumerate() {
                let [c0, c1] = x.to_limbs();
                self.state[2 * i] = c0;
                self.state[2 * i + 1] = c1;
            }
            self.permute();
        }
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
        self.ground.take().map_or_else(|| self.duplex(), |cells| cells[0])
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Squeeze `n` challenges eight to a permutation: each takes whatever waits, and its output's rate, two lanes to
    /// a challenge, gives the next eight. Right after a grind, its permutation gives the first seven: every cell but
    /// the second, which holds the proof of work.
    pub fn sample_packed(&mut self, n: usize) -> Vec<F> {
        let mut out = Vec::with_capacity(n);
        if n > 0
            && let Some(cells) = self.ground.take()
        {
            out.extend(cells.into_iter().take(n));
        }
        while out.len() < n {
            let take = (n - out.len()).min(RATE_CELLS);
            out.extend_from_slice(&self.permute()[..take]);
        }
        out
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce whose permutation, the one drawing the next challenge,
    /// leaves the low `bits` bits of its output's third lane zero; bind it, and keep that challenge for the next
    /// [`Self::sample`]. `bits = 0` is no grind at all. A CONTIGUOUS low-bit window, so a recursive verifier
    /// re-checks it with one bit decomposition (`grind_check` in `guests/lean_ethereum.py`). A long search runs on
    /// `S`.
    pub fn grind<S: Search>(&mut self, bits: u32) -> Option<u64> {
        self.grind_from::<S>(bits, 0)
    }

    /// [`Self::grind`] from the nonce `from` on: the smallest passing nonce at least `from`.
    pub(crate) fn grind_from<S: Search>(&mut self, bits: u32, from: u64) -> Option<u64> {
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
            keccak256::first_nonce(
                &base,
                lane,
                (b * BATCH).max(from)..(b * BATCH).saturating_add(BATCH),
                2,
                (1 << bits) - 1,
            )
        };
        // A short search, a few batches, is not worth a dispatch to the pool.
        let nonce = if bits < 10 {
            (from / BATCH..).find_map(batch)
        } else {
            // Windows of a quarter of the expected search; the first window holding a hit holds the smallest.
            let window = (1u64 << (bits.min(26) - 2)).div_ceil(BATCH);
            (from / BATCH..).step_by(window as usize).find_map(|w: u64| {
                S::find_first(window as usize, &|i| batch(w + i as u64).is_some()).and_then(|i| batch(w + i as u64))
            })
        };
        let nonce = nonce.expect("a nonce exists");
        self.absorb(F::from_limbs([nonce, 0]), DS_POW_NONCE);
        let cells = self.permute();
        self.ground = Some(std::array::from_fn(|i| cells[if i == 0 { 0 } else { i + 1 }]));
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
        for bits in [2, 8, 10, 13, 17] {
            let mut clone = sp.clone();
            let good = clone.grind::<Sequential>(bits).unwrap();
            let expected = (0..=good).find(|&n| pow_bits_ok(&sp, n, bits)).unwrap();
            assert_eq!(good, expected, "smallest nonce at {bits} bits");
            // From inside a batch, as `grind_sample` resumes: the smallest passing nonce at least `from`.
            for from in [good + 1, 63] {
                let next = (from..).find(|&n| pow_bits_ok(&sp, n, bits)).unwrap();
                assert_eq!(
                    sp.clone().grind_from::<Sequential>(bits, from),
                    Some(next),
                    "from {from} at {bits} bits"
                );
            }
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

    /// The prover's and the verifier's transcripts agree on random schedules of sends, packed sends of every length,
    /// draws, packed draws and grinds of every size, each grind then a packed draw of any length but zero (a grind is
    /// followed by a challenge) or a single one: the verifier reads back every scalar and draws every challenge the
    /// prover did.
    #[test]
    fn random_schedules_give_the_verifier_the_provers_challenges() {
        use verifier::__Transcript as Transcript;
        #[derive(Clone, Copy, Debug)]
        enum Op {
            Send(usize),
            SendPacked(usize),
            Sample,
            SamplePacked(usize),
            // Then a packed draw of that many challenges, or a single one.
            Grind(u32, Option<usize>),
        }
        let mut rng = xorshift(0x5eed);
        for schedule in 0..200 {
            let ops: Vec<Op> = (0..40)
                .map(|_| match rng() % 5 {
                    0 => Op::Send((rng() % 10) as usize),
                    1 => Op::SendPacked((rng() % 20) as usize),
                    2 => Op::Sample,
                    3 => Op::SamplePacked((rng() % 20) as usize),
                    _ => Op::Grind((rng() % 7) as u32, (rng() % 2 == 1).then(|| 1 + (rng() % 9) as usize)),
                })
                .collect();
            let (iv, public_input) = (pi(1), pi(5));
            let mut prover = ProverState::<E, Sequential>::new(iv, public_input);
            let (mut sent, mut drawn) = (Vec::new(), Vec::new());
            for &op in &ops {
                match op {
                    Op::Send(n) | Op::SendPacked(n) => {
                        let xs: Vec<E> = (0..n).map(|_| E::new(rng(), rng())).collect();
                        match op {
                            Op::Send(_) => prover.add_scalars(&xs),
                            _ => prover.add_scalars_packed(&xs),
                        }
                        sent.push(xs);
                    }
                    Op::Sample => drawn.push(prover.sample()),
                    Op::SamplePacked(n) => drawn.extend(prover.sample_packed(n)),
                    Op::Grind(bits, packed) => {
                        prover.grind(bits);
                        match packed {
                            Some(n) => drawn.extend(prover.sample_packed(n)),
                            None => drawn.push(prover.sample()),
                        }
                    }
                }
            }
            let proof = prover.into_proof();
            let digest = |words: [u64; 4]| Digest(std::array::from_fn(|i| words[i / 8].to_le_bytes()[i % 8]));
            let mut verifier = Transcript::new(&proof, digest(iv), digest(public_input), true);
            let (mut read, mut redrawn) = (Vec::new(), Vec::new());
            for &op in &ops {
                match op {
                    Op::Send(n) => read.push(verifier.next_scalars(n).unwrap()),
                    Op::SendPacked(n) => read.push(verifier.next_scalars_packed(n).unwrap()),
                    Op::Sample => redrawn.push(verifier.sample()),
                    Op::SamplePacked(n) => redrawn.extend(verifier.samples_packed(n)),
                    Op::Grind(bits, packed) => {
                        verifier.grind_check(bits).unwrap();
                        match packed {
                            Some(n) => redrawn.extend(verifier.samples_packed(n)),
                            None => redrawn.push(verifier.sample()),
                        }
                    }
                }
            }
            verifier.finish().unwrap();
            assert_eq!(read, sent, "schedule {schedule}: {ops:?}");
            assert_eq!(redrawn, drawn, "schedule {schedule}: {ops:?}");
        }
    }

    /// A xorshift generator.
    fn xorshift(seed: u64) -> impl FnMut() -> u64 {
        let mut x = seed;
        move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        }
    }
}
