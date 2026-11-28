//! The transcript (`NativeVm/Model/Transcript.lean`): the duplex sponge, the stream and the
//! openings of the decoded proof with their cursors, the roots read. The model's monad
//! `VM = StateT TState Option` is `&mut TState` and an `Option` result, `None` its rejection.

use crate::field::{EW, ZERO, poly_eval, sum_e};
use crate::input::{Decoded, OPENING_WORDS};
use crate::keccak::{Digest, State, digest_eq, hash_pair, hash_words, keccak_f};

/// `dsObserve`.
const DS_OBSERVE: u64 = 1;
/// `dsPowNonce`.
const DS_POW_NONCE: u64 = 4;
/// `rateScalars`.
const RATE_SCALARS: usize = 4;
/// The most roots: one per phase the decoder accepts (`maxRoots`).
pub const MAX_ROOTS: usize = crate::input::MAX_PHASES;

/// A waiting scalar and its tag.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pending {
    pub x: EW,
    pub tag: u64,
}

/// `SpongeW`: the Keccak state, the waiting scalars with their tags, the ground challenge.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct SpongeW {
    pub state: State,
    pub pending: [Pending; RATE_SCALARS],
    pub n_pending: usize,
    pub ground: Option<EW>,
}

impl SpongeW {
    /// `duplexInput`, in place: the waiting scalars' lanes over the rate, zeros up to lane `16`, the
    /// capacity kept.
    #[inline(never)]
    fn duplex_input(&mut self) {
        for (i, chunk) in self.state[..16].chunks_exact_mut(4).enumerate() {
            let lanes = if i < self.n_pending {
                let Pending { x, tag } = self.pending[i];
                [x.c0, x.c1, 0, tag]
            } else {
                [0; 4]
            };
            for (lane, value) in chunk.iter_mut().zip(lanes) {
                *lane = value;
            }
        }
    }

    /// `duplex`: permute, the queue emptied.
    #[inline(never)]
    fn duplex(&mut self) {
        self.duplex_input();
        keccak_f(&mut self.state);
        self.n_pending = 0;
    }

    /// `absorb`: a full queue is permuted first.
    #[inline(never)]
    fn absorb(&mut self, x: EW, tag: u64) {
        if self.n_pending >= RATE_SCALARS {
            self.duplex();
        }
        if let Some(slot) = self.pending.get_mut(self.n_pending) {
            *slot = Pending { x, tag };
            self.n_pending += 1;
        }
    }

    /// `challengeOf`: a state's first two lanes.
    #[inline(always)]
    fn challenge_of(state: &State) -> EW {
        EW::new(state[0], state[1])
    }

    /// `squeeze`: the ground challenge, or a permutation's first two lanes.
    #[inline(never)]
    fn squeeze(&mut self) -> EW {
        match self.ground.take() {
            Some(c) => c,
            None => {
                self.duplex();
                Self::challenge_of(&self.state)
            }
        }
    }

    /// `absorbNonce`: absorb the nonce with `dsPowNonce` and permute; the third lane, the next
    /// challenge ground.
    #[inline(never)]
    fn absorb_nonce(&mut self, nonce: EW) -> u64 {
        self.absorb(nonce, DS_POW_NONCE);
        self.duplex();
        self.ground = Some(Self::challenge_of(&self.state));
        self.state[2]
    }
}

/// `RootW`: a root read, with its tree's height and leaf width.
#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct RootW {
    pub digest: Digest,
    pub height: u64,
    pub width: u64,
}

/// `TState`: the sponge, the decoded stream and openings with their cursors, the roots read.
#[repr(C)]
pub struct TState<'a> {
    pub sponge: SpongeW,
    pub dec: Decoded<'a>,
    pub cursor: usize,
    pub phase: usize,
    pub roots: [RootW; MAX_ROOTS],
    pub n_roots: usize,
}

/// The leaves a query opened: the phase's openings in the decoded proof, read in place.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Rows<'a> {
    openings: &'a [u64],
    pub count: usize,
    pub width: usize,
}

impl<'a> Rows<'a> {
    /// Row `j`'s words.
    #[inline(never)]
    pub fn row(&self, j: usize) -> &'a [u64] {
        let start = j * OPENING_WORDS + 1;
        self.openings.get(start..start + self.width).unwrap_or(&[])
    }
}

/// `climb`: from `node` at position `q`, each level's low bit choosing the side.
#[inline(never)]
fn climb(node: Digest, q: u64, path: &[u64], height: usize) -> Digest {
    let (mut acc, mut q) = (node, q);
    for level in 0..height {
        let s: Digest = match path.get(4 * level..4 * level + 4) {
            Some(&[a, b, c, d]) => [a, b, c, d],
            _ => [0; 4],
        };
        acc = if q % 2 == 0 { hash_pair(&acc, &s) } else { hash_pair(&s, &acc) };
        q /= 2;
    }
    acc
}

/// `require`.
#[inline(always)]
pub fn require(c: bool) -> Option<()> {
    if c { Some(()) } else { None }
}

/// `grindingBits`.
#[inline(always)]
pub const fn grinding_bits(numerator: u64) -> u32 {
    let log = crate::field::bit_length(numerator.saturating_sub(1)) as u32;
    log.saturating_sub(128 - 125)
}

/// `powOkW`: the low `bits` bits of the proof of work are zero.
#[inline(always)]
fn pow_ok_w(bits: u32, pow: u64) -> bool {
    if bits >= 64 { pow == 0 } else { pow & ((1u64 << bits) - 1) == 0 }
}

/// The largest round polynomial, `2^2 + 1` coefficients.
pub const MAX_COUNT: usize = 5;

impl<'a> TState<'a> {
    /// The start (`verify`'s `start`): the seed, both cursors at `0`, no root.
    #[inline(always)]
    pub fn new(seed: State, dec: Decoded<'a>) -> Self {
        Self {
            sponge: SpongeW { state: seed, pending: [Pending { x: ZERO, tag: 0 }; RATE_SCALARS], n_pending: 0, ground: None },
            dec,
            cursor: 0,
            phase: 0,
            roots: [RootW::default(); MAX_ROOTS],
            n_roots: 0,
        }
    }

    /// `nextScalar`: the next stream element, unobserved, rejecting at the stream's end or while a
    /// grind's challenge waits.
    #[inline(never)]
    fn next_scalar(&mut self) -> Option<EW> {
        if self.sponge.ground.is_some() {
            return None;
        }
        let x = self.dec.stream_element(self.cursor)?;
        self.cursor += 1;
        Some(x)
    }

    /// `readScalar`.
    #[inline(never)]
    pub fn read_scalar(&mut self) -> Option<EW> {
        let x = self.next_scalar()?;
        self.sponge.absorb(x, DS_OBSERVE);
        Some(x)
    }

    /// `readScalars`, as many as `out` holds.
    #[inline(never)]
    pub fn read_scalars(&mut self, out: &mut [EW]) -> Option<()> {
        for slot in out.iter_mut() {
            *slot = self.read_scalar()?;
        }
        Some(())
    }

    /// `sampleChallenge`.
    #[inline(always)]
    pub fn sample_challenge(&mut self) -> EW {
        self.sponge.squeeze()
    }

    /// `sampleChallenges`, as many as `out` holds.
    #[inline(never)]
    pub fn sample_challenges(&mut self, out: &mut [EW]) {
        for slot in out.iter_mut() {
            *slot = self.sample_challenge();
        }
    }

    /// `grind bits`.
    #[inline(never)]
    pub fn grind(&mut self, bits: u32) -> Option<()> {
        if bits == 0 {
            return Some(());
        }
        let nonce = self.next_scalar()?;
        let pow = self.sponge.absorb_nonce(nonce);
        require(pow_ok_w(bits, pow))
    }

    /// `readCommitment height width`: a root as two absorbed scalars.
    #[inline(never)]
    pub fn read_commitment(&mut self, height: u64, width: u64) -> Option<()> {
        let x0 = self.read_scalar()?;
        let x1 = self.read_scalar()?;
        let slot = self.roots.get_mut(self.n_roots)?;
        *slot = RootW { digest: [x0.c0, x0.c1, x1.c0, x1.c1], height, width };
        self.n_roots += 1;
        Some(())
    }

    /// `queryOpenings i positions`: the next phase opened against root `i` (`openPhase`); its
    /// leaves.
    #[inline(never)]
    pub fn query_openings(&mut self, i: usize, positions: &[u64]) -> Option<Rows<'a>> {
        let root = *self.roots.get(..self.n_roots)?.get(i)?;
        let phase = self.dec.phase(self.phase)?;
        let rows = open_phase(&root.digest, root.height, root.width, positions, phase)?;
        self.phase += 1;
        Some(rows)
    }

    /// `sumcheckRoundPoly count claim eq`: the round polynomial into `msg[..count]`, after its
    /// grind.
    #[inline(never)]
    fn sumcheck_round_poly(
        &mut self,
        count: usize,
        claim: EW,
        eq: Option<EW>,
        msg: &mut [EW; MAX_COUNT],
    ) -> Option<()> {
        require((2..=MAX_COUNT).contains(&count))?;
        match eq {
            None => {
                msg[0] = self.read_scalar()?;
                let tail = msg.get_mut(2..count)?;
                self.read_scalars(tail)?;
                let derived = claim + sum_e(tail);
                self.grind(grinding_bits(count as u64 - 1))?;
                msg[1] = derived;
            }
            Some(eq_factor) => {
                let tail = msg.get_mut(1..count)?;
                self.read_scalars(tail)?;
                let derived = claim + eq_factor * sum_e(tail);
                self.grind(grinding_bits(count as u64 - 1 + 1))?;
                msg[0] = derived;
            }
        }
        Some(())
    }

    /// `sumcheck claim count equalities`: a round per entry of `out`, round `i`'s equality factor
    /// `equality(i)`; the challenges into `out`, and the final claim.
    #[inline(never)]
    pub fn sumcheck(
        &mut self,
        claim: EW,
        count: usize,
        equality: impl Fn(usize) -> Option<EW>,
        out: &mut [EW],
    ) -> Option<EW> {
        let mut claim = claim;
        let mut msg = [ZERO; MAX_COUNT];
        for (i, slot) in out.iter_mut().enumerate() {
            self.sumcheck_round_poly(count, claim, equality(i), &mut msg)?;
            let challenge = self.sample_challenge();
            *slot = challenge;
            claim = poly_eval(msg.get(..count)?, challenge);
        }
        Some(claim)
    }

    /// `sumcheckPlain claim count rounds`, `rounds` the length of `out`.
    #[inline(always)]
    pub fn sumcheck_plain(&mut self, claim: EW, count: usize, out: &mut [EW]) -> Option<EW> {
        self.sumcheck(claim, count, |_| None, out)
    }
}

/// `openPhase`: every opening of `width` leaf words and `height` siblings, the positions the
/// queried ones in order, each path climbing from its hashed leaf to `root`; the leaves.
#[inline(never)]
fn open_phase<'a>(root: &Digest, height: u64, width: u64, positions: &[u64], phase: &'a [u64]) -> Option<Rows<'a>> {
    let (&count, &h, &w) = match phase {
        [count, h, w, ..] => (count, h, w),
        _ => return None,
    };
    let openings = phase.get(3..)?;
    let count = usize::try_from(count).ok()?;
    let shape = count == 0 || (w == width && h == height);
    if !(shape && count == positions.len()) {
        return None;
    }
    let (h, w) = (usize::try_from(h).ok()?, usize::try_from(w).ok()?);
    for (j, &position) in positions.iter().enumerate() {
        let opening = openings.get(j * OPENING_WORDS..(j + 1) * OPENING_WORDS)?;
        if opening[0] != position {
            return None;
        }
    }
    for j in 0..count {
        let opening = openings.get(j * OPENING_WORDS..(j + 1) * OPENING_WORDS)?;
        let leaf = opening.get(1..1 + w)?;
        let path = opening.get(1 + crate::input::MAX_LEAF_WORDS..)?;
        if !digest_eq(&climb(hash_words(leaf), opening[0], path, h), root) {
            return None;
        }
    }
    Some(Rows { openings, count, width: w })
}
