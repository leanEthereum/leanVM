//! One-hot pointers: the chunk layout every Hotwire pointer of a proof shares.
//!
//! A pointer is an index `σ < 2^W`. Its `W` bits split, least significant first, into `d` chunks of widths `w_i`
//! ([`verifier::Chunks`]), and chunk `i` is committed as the `2^{w_i}` indicator bits `[σ_i = v]`, starting at bit
//! `Σ_{i' < i} 2^{w_{i'}}` of one `K` word. Chunk 0 is the low `min(WINDOW_BITS, W)` bits, the pointer's window.
//!
//! A chunk at a point `r_i ∈ E^{w_i}` is the linear functional `D_i(r_i) = Σ_v eq(r_i, v)·e_v` of its bits, so a
//! pointer at `r = (r_0, …, r_{d-1})` is `Φ(r) = Π_i D_i(r_i) = eq(r, σ)` when every chunk is one-hot. Read `s` cells
//! further inside its window, it is `T_s(e_0)·Π_{i ≥ 1} D_i(r_i)` for chunk 0's table `T_s(v) = eq(r_0, v + s)` where
//! `v + s < 2^{w_0}` ([`Shifts`]): `eq(r, σ + s)`, or zero past the window.

use primitives::field::F128;
use primitives::multilinear::eq_table;

pub use verifier::{MAX_POINTER_WIDTH as MAX_WIDTH, WINDOW_BITS};

/// The chunk layout of `W`-bit pointers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chunks {
    pub width: usize,
    pub widths: Vec<usize>,
    /// Where chunk `i`'s digit starts in an index, and its indicator bits in a word.
    index_shifts: Vec<usize>,
    word_shifts: Vec<usize>,
}

impl Chunks {
    /// The verifier's layout of `width`-bit pointers.
    pub fn new(width: usize) -> Self {
        let verifier::Chunks {
            width,
            widths,
            index_shifts,
            word_shifts,
        } = verifier::Chunks::new(width)
            .unwrap_or_else(|_| panic!("Hotwire: a {width}-bit pointer does not fit one word"));
        Self {
            width,
            widths,
            index_shifts,
            word_shifts,
        }
    }

    pub fn d(&self) -> usize {
        self.widths.len()
    }

    /// The word of index `sigma`.
    pub fn encode(&self, sigma: usize) -> u64 {
        assert!(sigma >> self.width == 0, "index {sigma} past 2^{}", self.width);
        (0..self.d()).fold(0, |word, i| word | 1 << (self.word_shifts[i] + self.digit(sigma, i)))
    }

    /// The indicator bits of chunk `i` of `word`, at bit 0.
    #[inline]
    pub fn bits(&self, word: u64, i: usize) -> u64 {
        (word >> self.word_shifts[i]) & (u64::MAX >> (64 - (1 << self.widths[i])))
    }

    /// Chunk `i`'s value in the index `sigma`.
    #[inline]
    pub fn digit(&self, sigma: usize, i: usize) -> usize {
        (sigma >> self.index_shifts[i]) & ((1 << self.widths[i]) - 1)
    }

    /// Where chunk `i`'s digit starts in an index.
    pub fn index_shift(&self, i: usize) -> usize {
        self.index_shifts[i]
    }

    /// The index `s` cells past `sigma`, `None` past its window.
    #[inline]
    pub fn shifted(&self, sigma: usize, s: usize) -> Option<usize> {
        let window = 1 << self.widths[0];
        (sigma % window + s < window).then_some(sigma + s)
    }

    /// The index of a word whose chunks are all one-hot.
    pub fn decode(&self, word: u64) -> Option<usize> {
        let mut sigma = 0;
        for i in 0..self.d() {
            let b = self.bits(word, i);
            if !b.is_power_of_two() {
                return None;
            }
            sigma |= (b.trailing_zeros() as usize) << self.index_shifts[i];
        }
        Some(sigma)
    }

    /// Every index of a word: one per choice of a set bit in each chunk, so none when a chunk has no bit set.
    pub fn indices(&self, word: u64, f: &mut impl FnMut(usize)) {
        fn walk(chunks: &Chunks, word: u64, i: usize, sigma: usize, f: &mut impl FnMut(usize)) {
            if i == chunks.d() {
                return f(sigma);
            }
            let mut b = chunks.bits(word, i);
            while b != 0 {
                let v = b.trailing_zeros() as usize;
                walk(chunks, word, i + 1, sigma | v << chunks.index_shifts[i], f);
                b &= b - 1;
            }
        }
        walk(self, word, 0, 0, f);
    }

    /// Where chunk `i`'s indicator bits start in a word.
    pub fn word_shift(&self, i: usize) -> usize {
        self.word_shifts[i]
    }

    /// Chunk `i`'s coordinates of a `W`-point.
    pub fn part<'a>(&self, point: &'a [F128], i: usize) -> &'a [F128] {
        &point[self.index_shifts[i]..self.index_shifts[i] + self.widths[i]]
    }
}

/// `T_s(v) = eq(e, v + s)` where `v + s < 2^{w_0}`, zero elsewhere, from chunk 0's eq table `e`.
pub fn window_shift(e: &[F128], s: usize) -> Vec<F128> {
    (0..e.len())
        .map(|v| e.get(v + s).copied().unwrap_or(F128::ZERO))
        .collect()
}

/// Chunk 0's [`window_shift`] tables at a `W`-point, per shift `s ≤ max_shift`: `tables[0]` is `D_0` itself.
#[derive(Clone, Debug)]
pub struct Shifts {
    pub max_shift: usize,
    pub tables: Vec<Vec<F128>>,
}

impl Shifts {
    pub fn new(eq: &ChunkEq, max_shift: usize) -> Self {
        Self {
            max_shift,
            tables: (0..=max_shift).map(|s| window_shift(&eq.tables[0], s)).collect(),
        }
    }

    /// Chunk 0's table for `Σ_s μ_s·T_s` over `weights = [(s, μ_s)]`.
    pub fn combined(&self, weights: &[(usize, F128)]) -> Vec<F128> {
        let mut t = vec![F128::ZERO; self.tables[0].len()];
        for &(s, mu) in weights {
            for (o, &e) in t.iter_mut().zip(&self.tables[s]) {
                *o += mu * e;
            }
        }
        t
    }
}

/// A functional of chunk `i` with table `table` at a word: the sum of the table over the chunk's set bits, which is
/// one lookup when the chunk is one-hot.
pub fn eval_chunk(chunks: &Chunks, table: &[F128], word: u64, i: usize) -> F128 {
    let mut bits = chunks.bits(word, i);
    let mut sum = F128::ZERO;
    while bits != 0 {
        sum += table[bits.trailing_zeros() as usize];
        bits &= bits - 1;
    }
    sum
}

/// A functional of chunk `i` with table `table` from a word's 64 bit-slices: the functional is linear in the bits.
pub fn from_slices(chunks: &Chunks, table: &[F128], slices: &[F128], i: usize) -> F128 {
    let start = chunks.word_shift(i);
    table.iter().zip(&slices[start..]).map(|(&e, &s)| e * s).sum()
}

/// `Π_h r_h·(1 + r_h)`: what `D(r)·D(1 + r)` is for every one-hot chunk (the mirror test of Emile Wambsgans).
pub fn mirror(point: &[F128]) -> F128 {
    point.iter().map(|&x| x * (F128::ONE + x)).product()
}

/// One eq table per chunk: the functionals `D_i` at one point.
#[derive(Clone, Debug)]
pub struct ChunkEq {
    pub tables: Vec<Vec<F128>>,
}

impl ChunkEq {
    /// At a `W`-point, chunk `i` at its own coordinates.
    pub fn at(chunks: &Chunks, point: &[F128]) -> Self {
        assert_eq!(point.len(), chunks.width);
        Self {
            tables: (0..chunks.d()).map(|i| eq_table(chunks.part(point, i))).collect(),
        }
    }

    /// At `1 + point`: each table of [`Self::at`] read with its value's bits flipped.
    pub fn mirrored(chunks: &Chunks, point: &[F128]) -> Self {
        let eq = Self::at(chunks, point);
        Self {
            tables: eq.tables.iter().map(|t| t.iter().rev().copied().collect()).collect(),
        }
    }

    /// `D_i` of a word.
    pub fn eval(&self, chunks: &Chunks, word: u64, i: usize) -> F128 {
        eval_chunk(chunks, &self.tables[i], word, i)
    }

    /// `D_i` from a word's 64 bit-slices.
    pub fn from_slices(&self, chunks: &Chunks, slices: &[F128], i: usize) -> F128 {
        from_slices(chunks, &self.tables[i], slices, i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::eq_eval;
    use primitives::test_rng::Rng;

    /// `σ`'s bits as a point.
    fn bits(sigma: usize, w: usize) -> Vec<F128> {
        (0..w).map(|h| F128::new(((sigma >> h) & 1) as u64, 0)).collect()
    }

    #[test]
    fn decoding_finds_the_index_of_exactly_the_one_hot_words() {
        let mut rng = Rng::new(0xdec);
        for w in 1..=MAX_WIDTH {
            let chunks = Chunks::new(w);
            for k in 0..500 {
                let sigma = rng.next_u64() as usize & ((1 << w) - 1);
                let word = match k % 4 {
                    0 => chunks.encode(sigma),
                    1 => chunks.encode(sigma) ^ 1 << (rng.next_u64() % 64),
                    2 => chunks.encode(sigma) | chunks.encode(rng.next_u64() as usize & ((1 << w) - 1)),
                    _ => rng.next_u64(),
                };
                let mut all = Vec::new();
                chunks.indices(word, &mut |s| all.push(s));
                let one_hot = (0..chunks.d()).all(|i| chunks.bits(word, i).count_ones() == 1);
                assert_eq!(chunks.decode(word).is_some(), one_hot, "width {w}, word {word:#x}");
                if let Some(s) = chunks.decode(word) {
                    assert_eq!(all, vec![s]);
                    // The bits past the chunks are no part of the pointer.
                    let used: u32 = chunks.widths.iter().map(|&w| 1 << w).sum();
                    assert_eq!(chunks.encode(s), word & (u64::MAX >> (64 - used)));
                }
                if k % 4 == 0 {
                    assert_eq!(chunks.decode(word), Some(sigma));
                }
                // Every index of a word sets one bit in each chunk, and the word holds each such bit.
                for &s in &all {
                    assert!((0..chunks.d()).all(|i| chunks.bits(word, i) >> chunks.digit(s, i) & 1 == 1));
                }
                let expected: usize = (0..chunks.d())
                    .map(|i| chunks.bits(word, i).count_ones() as usize)
                    .product();
                assert_eq!(all.len(), expected);
            }
        }
    }

    #[test]
    fn the_certificate_at_the_index_point_holds_for_exactly_the_one_hot_chunks() {
        let mut rng = Rng::new(11);
        for w in 1..=4 {
            let chunks = Chunks::new(w);
            let r = rng.ext_vec(w);
            let (eq, bar) = (ChunkEq::at(&chunks, &r), ChunkEq::mirrored(&chunks, &r));
            let target = mirror(&r);
            for word in 0u64..1 << (1 << w) {
                let product = eq.eval(&chunks, word, 0) * bar.eval(&chunks, word, 0);
                assert_eq!(product == target, word.count_ones() == 1, "width {w}, bits {word:#x}");
            }
        }
    }

    #[test]
    fn a_word_at_a_point_is_eq_of_its_index() {
        let mut rng = Rng::new(7);
        for w in [2, 5, 7, 13, 21, 22, 23, 24] {
            let chunks = Chunks::new(w);
            let r = rng.ext_vec(w);
            let eqs = ChunkEq::at(&chunks, &r);
            let dbar = ChunkEq::mirrored(&chunks, &r);
            let shifts = Shifts::new(&eqs, 12);
            let at = |t: Option<usize>| t.map_or(F128::ZERO, |t| eq_eval(&r, &bits(t, w)));
            for k in 0..40 {
                let sigma = match k {
                    0 => (1 << w) - 1,
                    1 => (1 << chunks.widths[0]) - 1,
                    _ => rng.next_u64() as usize & ((1 << w) - 1),
                };
                let word = chunks.encode(sigma);
                let phi: F128 = (0..chunks.d()).map(|i| eqs.eval(&chunks, word, i)).product();
                assert_eq!(phi, eq_eval(&r, &bits(sigma, w)));
                // The functionals from the word's bit-slices, the bits as field elements.
                let slices: Vec<F128> = (0..64).map(|b| F128::new(word >> b & 1, 0)).collect();
                for i in 0..chunks.d() {
                    assert_eq!(eqs.from_slices(&chunks, &slices, i), eqs.eval(&chunks, word, i));
                }
                let rest: F128 = (1..chunks.d()).map(|i| eqs.eval(&chunks, word, i)).product();
                for s in 1..=12 {
                    let value = eval_chunk(&chunks, &shifts.tables[s], word, 0) * rest;
                    let next = chunks.shifted(sigma, s);
                    assert_eq!(next.is_some(), sigma % 16 + s < 16 && (w > 3 || sigma + s < 1 << w));
                    assert_eq!(value, at(next), "sigma + {s}");
                    let mu = rng.ext();
                    let combined = shifts.combined(&[(s, mu), (1, F128::ONE)]);
                    assert_eq!(
                        eval_chunk(&chunks, &combined, word, 0) * rest,
                        mu * at(next) + at(chunks.shifted(sigma, 1))
                    );
                }
                for i in 0..chunks.d() {
                    let product = eqs.eval(&chunks, word, i) * dbar.eval(&chunks, word, i);
                    assert_eq!(product, mirror(chunks.part(&r, i)));
                }
            }
        }
    }
}
