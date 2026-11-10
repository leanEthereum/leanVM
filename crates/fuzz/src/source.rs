//! Where a case's choices come from: a byte string, read front to back.
//!
//! A case is a `prefix` (a corpus entry, possibly mutated, or libFuzzer's input) followed by an endless tail drawn
//! from a PRNG seed. Every draw reads bytes, so the same `(prefix, tail seed)` replays the same case, and the bytes a
//! case consumed are a corpus entry that replays it with no seed at all. Bulk data (blobs, long messages) is
//! expanded from one drawn word rather than drawn byte by byte, so it neither bloats the recording nor dilutes a
//! mutator's edits.

use primitives::field::{F64, F192, g_pow};

/// The most tail bytes a case records. A case that draws more replays from its seed, not from its recording.
const RECORD_CAP: usize = 1 << 20;

/// xoshiro256**, seeded by splitmix64.
#[derive(Clone, Debug)]
pub struct Rng([u64; 4]);

impl Rng {
    pub fn new(seed: u64) -> Self {
        let mut z = seed;
        let mut next = || {
            z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            x ^ (x >> 31)
        };
        Self([next(), next(), next(), next()])
    }

    pub fn next_u64(&mut self) -> u64 {
        let s = &mut self.0;
        let result = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        result
    }

    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next_u64() % n }
    }

    pub fn fill(&mut self, out: &mut [u8]) {
        for chunk in out.chunks_mut(8) {
            let bytes = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&bytes[..chunk.len()]);
        }
    }
}

/// A case's input.
#[derive(Clone, Debug)]
pub struct Source {
    prefix: Vec<u8>,
    pos: usize,
    /// `None` reads zeros past the prefix: libFuzzer's convention, where the input is all there is.
    tail: Option<Rng>,
    recorded: Vec<u8>,
}

impl Source {
    pub fn new(prefix: Vec<u8>, tail_seed: Option<u64>) -> Self {
        Self {
            prefix,
            pos: 0,
            tail: tail_seed.map(Rng::new),
            recorded: Vec::new(),
        }
    }

    /// A fresh case: all tail.
    pub fn from_seed(seed: u64) -> Self {
        Self::new(Vec::new(), Some(seed))
    }

    /// Exactly `bytes`, then zeros.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self::new(bytes.to_vec(), None)
    }

    /// The bytes this case consumed: replayed by [`Self::from_bytes`] when the case drew less than the cap.
    pub fn consumed(&self) -> Vec<u8> {
        let mut out = self.prefix[..self.pos.min(self.prefix.len())].to_vec();
        out.extend(&self.recorded);
        out
    }

    pub fn consumed_len(&self) -> usize {
        self.pos
    }

    fn byte(&mut self) -> u8 {
        let b = if self.pos < self.prefix.len() {
            self.prefix[self.pos]
        } else {
            match &mut self.tail {
                Some(rng) => {
                    let b = rng.next_u64() as u8;
                    if self.recorded.len() < RECORD_CAP {
                        self.recorded.push(b);
                    }
                    b
                }
                None => 0,
            }
        };
        self.pos += 1;
        b
    }

    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.byte()).collect()
    }

    pub fn array<const N: usize>(&mut self) -> [u8; N] {
        std::array::from_fn(|_| self.byte())
    }

    pub fn u8(&mut self) -> u8 {
        self.byte()
    }

    pub fn u16(&mut self) -> u16 {
        u16::from_le_bytes(self.array())
    }

    pub fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.array())
    }

    pub fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.array())
    }

    pub fn bool(&mut self) -> bool {
        self.byte() & 1 == 1
    }

    /// True with probability about `num / den`.
    pub fn chance(&mut self, num: u32, den: u32) -> bool {
        (self.u16() as u32 % den.max(1)) < num
    }

    /// Uniform-ish in `0..n`; `0` when `n` is zero. Reads as few bytes as `n` needs, so small choices stay
    /// cheap for a mutator to flip.
    pub fn below(&mut self, n: usize) -> usize {
        match n {
            0 | 1 => 0,
            2..=256 => self.byte() as usize % n,
            257..=65536 => self.u16() as usize % n,
            _ => (self.u64() % n as u64) as usize,
        }
    }

    /// In `lo..=hi`.
    pub fn range(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + self.below(hi - lo + 1)
    }

    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }

    /// Index `i` with probability proportional to `weights[i]`.
    pub fn weighted(&mut self, weights: &[u32]) -> usize {
        let total: u64 = weights.iter().map(|&w| w as u64).sum();
        let mut r = self.u32() as u64 % total.max(1);
        for (i, &w) in weights.iter().enumerate() {
            if r < w as u64 {
                return i;
            }
            r -= w as u64;
        }
        weights.len() - 1
    }

    /// A small size, skewed small: a length, a count, a depth.
    pub fn size(&mut self, max: usize) -> usize {
        match self.byte() % 4 {
            0 => self.below(max.min(4) + 1),
            1 | 2 => self.below(max.min(16) + 1),
            _ => self.below(max + 1),
        }
    }

    /// A word that is often on an edge: zero, one, a power of two and its neighbours, all ones, a sign bit.
    pub fn edgy_u64(&mut self) -> u64 {
        match self.byte() % 12 {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            3 => 1u64 << self.below(64),
            4 => (1u64 << self.below(64)).wrapping_sub(1),
            5 => (1u64 << self.below(64)).wrapping_add(1),
            6 => i64::MAX as u64 + self.below(2) as u64,
            7 => self.below(256) as u64,
            8 => u32::MAX as u64 + self.below(3) as u64 - 1,
            _ => self.u64(),
        }
    }

    /// An edge-biased `usize` no larger than `max`.
    pub fn edgy_usize(&mut self, max: usize) -> usize {
        let v = self.edgy_u64();
        if max == usize::MAX {
            v as usize
        } else {
            (v % (max as u64 + 1)) as usize
        }
    }

    /// A field element of `K = GF(2^64)`, often a special one: zero, one, a small g-power (an address, a pc), its
    /// inverse direction, a single bit.
    pub fn f64(&mut self) -> F64 {
        match self.byte() % 8 {
            0 => F64(0),
            1 => F64(1),
            2 => g_pow(self.below(1 << 20)),
            3 => F64(self.edgy_u64()),
            _ => F64(self.u64()),
        }
    }

    /// A machine word, often degenerate: in `K`, 128-bit, top limb only, or edge limbs.
    pub fn f192(&mut self) -> F192 {
        match self.byte() % 8 {
            0 => F192::ZERO,
            1 => F192::ONE,
            2 => F192::from(self.f64()),
            3 => F192::new(self.edgy_u64(), self.edgy_u64(), 0),
            4 => F192::new(self.edgy_u64(), self.edgy_u64(), self.edgy_u64()),
            5 => F192::new(0, 0, self.edgy_u64()),
            _ => F192::new(self.u64(), self.u64(), self.u64()),
        }
    }

    /// `len` bytes expanded from one drawn word: bulk data that costs the recording eight bytes.
    pub fn bulk(&mut self, len: usize) -> Vec<u8> {
        let mut out = vec![0; len];
        let seed = self.u64();
        match seed % 8 {
            0 => {}                                                          // all zero
            1 => out.fill(0xff),                                             // all ones
            2 => out.iter_mut().enumerate().for_each(|(i, b)| *b = i as u8), // a ramp
            _ => Rng::new(seed).fill(&mut out),
        }
        out
    }

    /// `n` words expanded like [`Self::bulk`].
    pub fn bulk_u64(&mut self, n: usize) -> Vec<u64> {
        self.bulk(8 * n)
            .as_chunks::<8>()
            .0
            .iter()
            .map(|c| u64::from_le_bytes(*c))
            .collect()
    }

    /// A PRNG seeded from the input, for a target's own bulk randomness.
    pub fn rng(&mut self) -> Rng {
        Rng::new(self.u64())
    }
}

/// Byte-level edits of a corpus entry, AFL's havoc: what turns one interesting case into its neighbours.
pub fn mutate(input: &[u8], rng: &mut Rng, other: Option<&[u8]>) -> Vec<u8> {
    let mut out = input.to_vec();
    let edits = 1 + rng.below(8) as usize;
    for _ in 0..edits {
        let len = out.len();
        match rng.below(11) {
            0 if len > 0 => {
                let i = rng.below(len as u64) as usize;
                out[i] ^= 1 << rng.below(8);
            }
            1 if len > 0 => {
                let i = rng.below(len as u64) as usize;
                out[i] = rng.next_u64() as u8;
            }
            2 if len > 0 => {
                let i = rng.below(len as u64) as usize;
                out[i] = [0, 1, 0x7f, 0x80, 0xff][rng.below(5) as usize];
            }
            3 if len > 1 => {
                // Delete a run.
                let i = rng.below(len as u64) as usize;
                let n = 1 + rng.below((len - i).min(32) as u64) as usize;
                out.drain(i..(i + n).min(len));
            }
            4 => {
                // Insert random bytes.
                let i = rng.below(len as u64 + 1) as usize;
                let n = 1 + rng.below(16) as usize;
                let bytes: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
                out.splice(i..i, bytes);
            }
            5 if len > 1 => {
                // Duplicate a run.
                let i = rng.below(len as u64) as usize;
                let n = 1 + rng.below((len - i).min(32) as u64) as usize;
                let run: Vec<u8> = out[i..(i + n).min(len)].to_vec();
                let j = rng.below(out.len() as u64 + 1) as usize;
                out.splice(j..j, run);
            }
            6 if len >= 8 => {
                // An interesting word.
                let i = rng.below(len as u64 - 7) as usize;
                let word: u64 = [0, 1, u64::MAX, 1 << 63, u32::MAX as u64, rng.next_u64()][rng.below(6) as usize];
                out[i..i + 8].copy_from_slice(&word.to_le_bytes());
            }
            7 if len > 0 => {
                // Truncate: the tail seed takes over from here.
                out.truncate(rng.below(len as u64) as usize);
            }
            8 if len > 0 => {
                // Small arithmetic on one byte.
                let i = rng.below(len as u64) as usize;
                out[i] = out[i].wrapping_add((rng.below(17) as u8).wrapping_sub(8));
            }
            9 => {
                if let Some(other) = other.filter(|o| !o.is_empty()) {
                    // Splice in a run of another entry.
                    let i = rng.below(other.len() as u64) as usize;
                    let n = 1 + rng.below((other.len() - i).min(256) as u64) as usize;
                    let j = rng.below(out.len() as u64 + 1) as usize;
                    let end = (j + n).min(out.len());
                    out.splice(j..end, other[i..i + n].iter().copied());
                }
            }
            _ if len > 1 => {
                // Swap two bytes.
                let i = rng.below(len as u64) as usize;
                let j = rng.below(len as u64) as usize;
                out.swap(i, j);
            }
            _ => {}
        }
    }
    out
}
