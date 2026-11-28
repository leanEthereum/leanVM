//! One-hot pointers: the chunk layout every Hotwire pointer of a proof shares.
//!
//! A pointer is an index `σ < 2^W`. Its `W` bits split, least significant first, into `d` chunks of widths
//! `w_i`, and chunk `i` is committed as the `2^{w_i}` indicator bits `[σ_i = v]`, starting at bit
//! `Σ_{i' < i} 2^{w_{i'}}` of one `K` word. Chunk 0 is the low `min(WINDOW_BITS, W)` bits, the pointer's window; the
//! rest are the fewest chunks whose indicator bits fit what is left of 64, wider chunks first: `W = 22` gives
//! `(4, 3, 3, 3, 3, 3, 3)`.
//!
//! A chunk at a point `r_i ∈ E^{w_i}` is the linear functional `D_i(r_i) = Σ_v eq(r_i, v)·e_v` of its bits, so a
//! pointer at `r = (r_0, …, r_{d-1})` is `Φ(r) = Π_i D_i(r_i) = eq(r, σ)` when every chunk is one-hot. Read `s` cells
//! further inside its window, it is `T_s(e_0)·Π_{i ≥ 1} D_i(r_i)` for chunk 0's table `T_s(v) = eq(r_0, v + s)` where
//! `v + s < 2^{w_0}` ([`Shifts`]): `eq(r, σ + s)`, or zero past the window.

use primitives::field::F128;
use primitives::multilinear::eq_table;
use std::mem::MaybeUninit;

// The widest pointer one `K` word holds, and chunk 0's bits: a shifted read stays in the window of
// `2^WINDOW_BITS` cells its pointer is in.
pub use verifier::{MAX_POINTER_WIDTH as MAX_WIDTH, WINDOW_BITS};

/// No index: a word some chunk of which is not one-hot.
pub const NO_INDEX: u32 = u32::MAX;

/// The chunk layout of `W`-bit pointers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chunks {
    pub width: usize,
    pub widths: Vec<usize>,
    index_shifts: Vec<usize>,
    word_shifts: Vec<usize>,
    /// Per byte of a word and value of that byte, its set bits' digits at their index shifts plus a count per chunk
    /// above [`Self::count_shift`], chunk `i`'s in `w_i + 1` bits: see [`Self::decode`].
    bytes: Vec<u64>,
    count_shift: usize,
    one_each: u64,
    /// Per chunk, its digit's shift and mask in an index; zero past the last chunk.
    digit_shifts: [u32; 16],
    digit_masks: [u32; 16],
    /// The words of an index's low `split` bits and of its high bits, which cover whole chunks each: a word is one of
    /// each, ORed.
    split: usize,
    low_words: Vec<u64>,
    high_words: Vec<u64>,
    /// [`Self::varying`] of the low `split` bits of a difference and of its high bits.
    low_varying: Vec<u16>,
    high_varying: Vec<u16>,
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
        let prefix = |f: &dyn Fn(usize) -> usize| {
            widths
                .iter()
                .scan(0, |at, &w| {
                    let start = *at;
                    *at += f(w);
                    Some(start)
                })
                .collect()
        };
        // Every bit's digit summed bounds the index field; chunk `i`'s count field holds up to its `2^{w_i}` bits.
        let total: usize = (0..widths.len())
            .map(|i| ((1 << widths[i]) * ((1 << widths[i]) - 1) / 2) << index_shifts[i])
            .sum();
        let count_shift = (usize::BITS - total.leading_zeros()) as usize;
        let count_shifts: Vec<usize> = prefix(&|w| w + 1);
        assert!(
            count_shift + width + widths.len() <= 64,
            "the counts fit above the index"
        );
        let bytes = {
            let mut table = vec![0u64; 8 * 256];
            for (b, entries) in table.chunks_mut(256).enumerate() {
                for (byte, e) in entries.iter_mut().enumerate() {
                    for bit in (0..8).filter(|&bit| byte >> bit & 1 == 1) {
                        let p = 8 * b + bit;
                        if let Some(i) = (0..widths.len())
                            .find(|&i| (word_shifts[i]..word_shifts[i] + (1 << widths[i])).contains(&p))
                        {
                            *e += (((p - word_shifts[i]) << index_shifts[i]) as u64)
                                + (1u64 << (count_shift + count_shifts[i]));
                        }
                    }
                }
            }
            table
        };
        let one_each = count_shifts.iter().map(|&at| 1u64 << at).sum();
        let (mut digit_shifts, mut digit_masks) = ([0; 16], [0; 16]);
        for i in 0..widths.len() {
            digit_shifts[i] = index_shifts[i] as u32;
            digit_masks[i] = (1 << widths[i]) - 1;
        }
        // The chunk boundary nearest the middle of the index.
        let split = *index_shifts
            .iter()
            .min_by_key(|&&at| at.abs_diff(width / 2))
            .expect("a pointer has a chunk");
        let mut chunks = Self {
            digit_shifts,
            digit_masks,
            width,
            index_shifts,
            word_shifts,
            widths,
            bytes,
            count_shift,
            one_each,
            split,
            low_words: Vec::new(),
            high_words: Vec::new(),
            low_varying: Vec::new(),
            high_varying: Vec::new(),
        };
        let low_chunks = chunks.index_shifts.iter().filter(|&&at| at < split).count();
        let words = |chunks: &Self, range: std::ops::Range<usize>, sigma: usize| {
            range.fold(0, |word, i| {
                let v = (sigma >> chunks.index_shifts[i]) & ((1 << chunks.widths[i]) - 1);
                word | 1 << (chunks.word_shifts[i] + v)
            })
        };
        let d = chunks.d();
        chunks.low_words = (0..1usize << split).map(|s| words(&chunks, 0..low_chunks, s)).collect();
        chunks.high_words = (0..1usize << (width - split))
            .map(|s| words(&chunks, low_chunks..d, s << split))
            .collect();
        let varying =
            |chunks: &Self, diff: usize| (0..d).fold(0u16, |out, i| out | u16::from(chunks.digit(diff, i) != 0) << i);
        chunks.low_varying = (0..1usize << split).map(|s| varying(&chunks, s)).collect();
        chunks.high_varying = (0..1usize << (width - split))
            .map(|s| varying(&chunks, s << split))
            .collect();
        chunks
    }

    pub fn d(&self) -> usize {
        self.widths.len()
    }

    /// The word of index `sigma`.
    #[inline]
    pub fn encode(&self, sigma: usize) -> u64 {
        debug_assert!(sigma >> self.width == 0, "index {sigma} past 2^{}", self.width);
        self.low_words[sigma & ((1 << self.split) - 1)] | self.high_words[sigma >> self.split]
    }

    /// The indicator bits of chunk `i` of `word`, at bit 0.
    #[inline(always)]
    pub fn bits(&self, word: u64, i: usize) -> u64 {
        (word >> self.word_shifts[i]) & (u64::MAX >> (64 - (1 << self.widths[i])))
    }

    /// Chunk `i`'s value in the index `sigma`.
    #[inline(always)]
    pub fn digit(&self, sigma: usize, i: usize) -> usize {
        ((sigma as u32 >> self.digit_shifts[i & 15]) & self.digit_masks[i & 15]) as usize
    }

    /// The index `s` cells past `sigma`, `None` past its window.
    #[inline(always)]
    pub fn shifted(&self, sigma: usize, s: usize) -> Option<usize> {
        let window = 1 << self.widths[0];
        (sigma % window + s < window).then_some(sigma + s)
    }

    /// The shift of chunk `i`'s digit in an index.
    pub fn digit_shift(&self, i: usize) -> usize {
        self.index_shifts[i]
    }

    /// Bit `i` set for each chunk `i` whose digit in `diff` is nonzero: the chunks two indices differ in, for `diff`
    /// their XOR.
    #[inline(always)]
    pub fn varying(&self, diff: u32) -> u32 {
        let diff = diff as usize;
        debug_assert!(diff >> self.width == 0);
        u32::from(self.low_varying[diff & ((1 << self.split) - 1)] | self.high_varying[diff >> self.split])
    }

    /// The index of a word whose chunks are all one-hot.
    #[inline(always)]
    pub fn decode(&self, word: u64) -> Option<usize> {
        // A byte's entry adds each set bit's digit to the index and one to its chunk's count, so a word is one-hot
        // exactly when every count is one, and then the index field is its index.
        let sum: u64 = (0..8)
            .map(|b| self.bytes[256 * b + (word >> (8 * b) & 0xff) as usize])
            .sum();
        (sum >> self.count_shift == self.one_each).then_some((sum & ((1 << self.count_shift) - 1)) as usize)
    }

    /// Each word's index ([`Self::decode`]), or [`NO_INDEX`], in parallel.
    pub fn decode_all(&self, words: &[u64]) -> Vec<u32> {
        self.decode_many(&[words]).pop().expect("one column")
    }

    /// [`Self::decode_all`] of several columns of words, in one dispatch.
    pub fn decode_many(&self, columns: &[&[u64]]) -> Vec<Vec<u32>> {
        const TASK: usize = 1 << 12;
        let mut out: Vec<Vec<MaybeUninit<u32>>> = columns.iter().map(|c| primitives::uninit_vec(c.len())).collect();
        let ptrs: Vec<_> = out.iter_mut().map(|v| parallel::SendPtr(v.as_mut_ptr())).collect();
        let mut first = vec![0];
        for c in columns {
            first.push(first.last().unwrap() + c.len().div_ceil(TASK));
        }
        parallel::for_each(*first.last().unwrap(), |task| {
            let c = first.partition_point(|&f| f <= task) - 1;
            let start = (task - first[c]) * TASK;
            let words = &columns[c][start..columns[c].len().min(start + TASK)];
            // SAFETY: the task's entries are its own, inside column `c`.
            let index = unsafe { std::slice::from_raw_parts_mut(ptrs[c].0.add(start), words.len()) };
            // A table's rows often repeat a pointer: its index is decoded once per run.
            let (mut last, mut sigma) = (0u64, NO_INDEX);
            for (o, &w) in index.iter_mut().zip(words) {
                if w != last {
                    (last, sigma) = (w, self.decode(w).map_or(NO_INDEX, |sigma| sigma as u32));
                }
                o.write(sigma);
            }
        });
        // SAFETY: the tasks cover every entry of every column once, and each task writes its entries.
        out.into_iter()
            .map(|v| unsafe { primitives::assume_init_vec(v) })
            .collect()
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

/// Chunk 0's tables at a `W`-point per shift `s ≤ max_shift`, `T_s(v) = eq(r_0, v + s)` where `v + s < 2^{w_0}` and
/// zero elsewhere: `tables[0]` is `D_0` itself.
#[derive(Clone, Debug)]
pub struct Shifts {
    pub max_shift: usize,
    pub tables: Vec<Vec<F128>>,
}

impl Shifts {
    pub fn new(eq: &ChunkEq, max_shift: usize) -> Self {
        let e = &eq.tables[0];
        let shifted = |s: usize| {
            (0..e.len())
                .map(|v| e.get(v + s).copied().unwrap_or(F128::ZERO))
                .collect()
        };
        Self {
            max_shift,
            tables: (0..=max_shift).map(shifted).collect(),
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

/// `eq(r, σ)` at a `W`-point `r` as two tables, over the low `lo_bits` bits of `σ`, which hold its window, and over
/// the rest, so a pointer whose chunks are one-hot is one product at `r` rather than one factor per chunk.
#[derive(Clone, Debug)]
pub struct SplitEq {
    lo_bits: usize,
    window: usize,
    lo: Vec<F128>,
    hi: Vec<F128>,
}

impl SplitEq {
    pub fn new(r: &[F128], window_bits: usize) -> Self {
        let lo_bits = r.len().div_ceil(2).max(window_bits);
        Self {
            lo_bits,
            window: 1 << window_bits,
            lo: eq_table(&r[..lo_bits]),
            hi: eq_table(&r[lo_bits..]),
        }
    }

    /// `eq(r, σ)`.
    #[inline(always)]
    pub fn at(&self, sigma: usize) -> F128 {
        self.lo[sigma & (self.lo.len() - 1)] * self.hi[sigma >> self.lo_bits]
    }

    /// The low table of `Σ_s μ_s·eq(r, σ + s)` over `weights = [(s, μ_s)]`, each term zero past `σ`'s window.
    pub fn shifted_table(&self, weights: &[(usize, F128)]) -> Vec<F128> {
        let mut table = vec![F128::ZERO; self.lo.len()];
        for &(s, mu) in weights {
            for (v, t) in table.iter_mut().enumerate() {
                if v % self.window + s < self.window {
                    *t += mu * self.lo[v + s];
                }
            }
        }
        table
    }

    /// `Σ_s μ_s·eq(r, σ + s)` from [`Self::shifted_table`].
    #[inline(always)]
    pub fn at_shifted(&self, table: &[F128], sigma: usize) -> F128 {
        table[sigma & (self.lo.len() - 1)] * self.hi[sigma >> self.lo_bits]
    }
}

/// A functional of chunk `i` with table `table` at a word: a lookup when the chunk is one-hot, the sum over its set
/// bits otherwise.
#[inline(always)]
pub fn eval_chunk(chunks: &Chunks, table: &[F128], word: u64, i: usize) -> F128 {
    let bits = chunks.bits(word, i);
    if bits & bits.wrapping_sub(1) == 0 {
        if bits == 0 {
            F128::ZERO
        } else {
            table[bits.trailing_zeros() as usize]
        }
    } else {
        let mut sum = F128::ZERO;
        let mut rest = bits;
        while rest != 0 {
            sum += table[rest.trailing_zeros() as usize];
            rest &= rest - 1;
        }
        sum
    }
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

    /// At `1 + point`, chunk `i` at its own coordinates: each table of [`Self::at`] read with its value's bits
    /// flipped.
    pub fn mirrored(chunks: &Chunks, point: &[F128]) -> Self {
        let eq = Self::at(chunks, point);
        Self {
            tables: eq.tables.iter().map(|t| t.iter().rev().copied().collect()).collect(),
        }
    }

    /// `D_i` of a word.
    #[inline(always)]
    pub fn eval(&self, chunks: &Chunks, word: u64, i: usize) -> F128 {
        eval_chunk(chunks, &self.tables[i], word, i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::eq_eval;
    use primitives::test_rng::Rng;

    #[test]
    fn decoding_finds_the_index_of_exactly_the_one_hot_words() {
        let mut rng = Rng::new(0xdec);
        for w in 1..=MAX_WIDTH {
            let chunks = Chunks::new(w);
            let by_chunk = |word: u64| {
                (0..chunks.d())
                    .map(|i| {
                        let b = chunks.bits(word, i);
                        b.is_power_of_two()
                            .then(|| (b.trailing_zeros() as usize) << chunks.index_shifts[i])
                    })
                    .sum::<Option<usize>>()
            };
            for k in 0..2000 {
                let sigma = rng.next_u64() as usize & ((1 << w) - 1);
                let word = match k % 4 {
                    0 => chunks.encode(sigma),
                    1 => chunks.encode(sigma) ^ 1 << (rng.next_u64() % 64),
                    2 => chunks.encode(sigma) | chunks.encode(rng.next_u64() as usize & ((1 << w) - 1)),
                    _ => rng.next_u64(),
                };
                assert_eq!(chunks.decode(word), by_chunk(word), "width {w}, word {word:#x}");
                if k % 4 == 0 {
                    assert_eq!(chunks.decode(word), Some(sigma));
                }
            }
        }
    }

    /// Every index's word decodes to it, at every width: exhaustively up to 16 bits, then each digit at its extremes
    /// and random indices.
    #[test]
    fn every_index_round_trips() {
        let mut rng = Rng::new(0x707);
        for w in 1..=MAX_WIDTH {
            let chunks = Chunks::new(w);
            let mask = (1usize << w) - 1;
            let sigmas: Vec<usize> = if w <= 16 {
                (0..=mask).collect()
            } else {
                let extremes = (0..1usize << chunks.d()).map(|set| {
                    (0..chunks.d())
                        .filter(|&i| set >> i & 1 == 1)
                        .fold(0, |s, i| s | ((1 << chunks.widths[i]) - 1) << chunks.index_shifts[i])
                });
                extremes
                    .chain((0..1 << 16).map(|_| rng.next_u64() as usize & mask))
                    .collect()
            };
            for sigma in sigmas {
                assert_eq!(
                    chunks.decode(chunks.encode(sigma)),
                    Some(sigma),
                    "width {w}, index {sigma}"
                );
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
            for bits in 0u64..1 << (1 << w) {
                let at = |t: &ChunkEq| {
                    (0..1 << w)
                        .filter(|v| bits >> v & 1 == 1)
                        .map(|v| t.tables[0][v])
                        .sum::<F128>()
                };
                assert_eq!(
                    at(&eq) * at(&bar) == target,
                    bits.count_ones() == 1,
                    "width {w}, bits {bits:#x}"
                );
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
            for k in 0..40 {
                let sigma = match k {
                    0 => (1 << w) - 1,
                    1 => (1 << chunks.widths[0]) - 1,
                    _ => rng.next_u64() as usize & ((1 << w) - 1),
                };
                let word = chunks.encode(sigma);
                let bits: Vec<F128> = (0..w).map(|h| F128::new(((sigma >> h) & 1) as u64, 0)).collect();
                let phi: F128 = (0..chunks.d()).map(|i| eqs.eval(&chunks, word, i)).product();
                assert_eq!(phi, eq_eval(&r, &bits));
                let dbar = ChunkEq::mirrored(&chunks, &r);
                let shifts = Shifts::new(&eqs, 12);
                let split = SplitEq::new(&r, chunks.widths[0]);
                assert_eq!(split.at(sigma), phi);
                let rest: F128 = (1..chunks.d()).map(|i| eqs.eval(&chunks, word, i)).product();
                let at = |t: Option<usize>| {
                    t.map_or(F128::ZERO, |t| {
                        let bits: Vec<F128> = (0..w).map(|h| F128::new(((t >> h) & 1) as u64, 0)).collect();
                        eq_eval(&r, &bits)
                    })
                };
                for s in 1..=12 {
                    let value = eval_chunk(&chunks, &shifts.tables[s], word, 0) * rest;
                    let next = chunks.shifted(sigma, s);
                    assert_eq!(next.is_some(), sigma % 16 + s < 16 && (w > 3 || sigma + s < 1 << w));
                    assert_eq!(value, at(next), "sigma + {s}");
                    let mu = rng.ext();
                    let table = split.shifted_table(&[(s, mu), (1, F128::ONE)]);
                    assert_eq!(
                        split.at_shifted(&table, sigma),
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

    /// At every width, an index's word decodes to it and to it alone, each chunk's bits are its digit's one-hot, the
    /// split tables of `varying` give the chunks two indices differ in, and `shifted` stays inside the window: every
    /// index up to `2^12`, then random ones and the edges.
    #[test]
    fn indices_words_and_digits_agree_at_every_width() {
        let mut rng = Rng::new(0x1d5);
        for w in 1..=MAX_WIDTH {
            let chunks = Chunks::new(w);
            let top = (1usize << w) - 1;
            let window = 1usize << chunks.widths[0];
            let sigmas: Vec<usize> = if w <= 12 {
                (0..=top).collect()
            } else {
                [0, top, window - 1, window, top - window + 1]
                    .into_iter()
                    .chain((0..4096).map(|_| rng.next_u64() as usize & top))
                    .collect()
            };
            for sigma in sigmas {
                let word = chunks.encode(sigma);
                assert_eq!(chunks.decode(word), Some(sigma), "w {w}, sigma {sigma}");
                let mut all = Vec::new();
                chunks.indices(word, &mut |j| all.push(j));
                assert_eq!(all, [sigma], "w {w}, sigma {sigma}");
                for i in 0..chunks.d() {
                    assert_eq!(
                        chunks.bits(word, i),
                        1 << chunks.digit(sigma, i),
                        "w {w}, sigma {sigma}"
                    );
                }
                let diff = sigma ^ (rng.next_u64() as usize & top);
                let varying = (0..chunks.d()).fold(0, |v, i| v | u32::from(chunks.digit(diff, i) != 0) << i);
                assert_eq!(chunks.varying(diff as u32), varying, "w {w}, diff {diff:#x}");
                for s in 0..=16 {
                    let inside = sigma / window == (sigma + s) / window && sigma + s <= top;
                    assert_eq!(
                        chunks.shifted(sigma, s),
                        inside.then_some(sigma + s),
                        "w {w}, sigma {sigma}, s {s}"
                    );
                }
            }
        }
    }
}
