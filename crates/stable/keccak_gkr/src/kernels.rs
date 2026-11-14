//! The bit-level kernels of the layer prover, over one block position at a time: the 32 packs of
//! one bit position of one block.

use primitives::field::lanes::{
    ByteMap, Wide8, map_bytes, map_fields, transpose_bits, transpose_bytes, transpose_words,
};
use primitives::field::{F128, clmul8_low};

use crate::keccak::{BITS, row_positions};
use crate::rmfe::{PROD_BITS, RMFE};
use crate::witness::BLOCK_WORDS;

/// Packs in a block position.
pub(crate) const PACKS: usize = 32;
/// Packs the first rounds fold together: half a block.
pub const GROUP: usize = 16;
/// Variables indexing the packs of a group.
pub(crate) const SKIP: usize = 4;

/// The 32 packs of a run of eight positions from `j`, embedded: pack `q` of position `j + i` is lane `i` of `out[q]`.
pub fn embed_run(block: &[u64], j: usize) -> [Run; PACKS] {
    let positions = block[j * BLOCK_WORDS..][..8 * BLOCK_WORDS].as_chunks::<BLOCK_WORDS>().0;
    let words = transpose_words(positions.try_into().expect("eight positions"));
    let mut out = [[0; 8]; PACKS];
    for (out, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&words) {
        *out = map_fields(&RMFE.embedding, *word);
    }
    out
}

/// The unprojected `chi` of eight packs: `ones * (a + c) + b * c`.
pub fn products(a: Run, b: Run, c: Run) -> Run {
    xor(clmul8_low([RMFE.ones as u64; 8], xor(a, c)), clmul8_low(b, c))
}

/// Bytes of a product of two embeddings.
pub(crate) const PROD_BYTES: usize = PROD_BITS.div_ceil(8);
/// A block's product bits, eight to a byte, as many words: per pack, a word per byte of its products.
const COLUMN_WORDS: usize = PACKS * PROD_BYTES;
/// The weighted bit sums of a block: per pack, one per bit of its products.
pub(crate) const COLUMNS: usize = 8 * COLUMN_WORDS;
/// Bytes of a weight.
const WEIGHT_BYTES: usize = 16;
/// The bytes of the sums [`ProductBlock::run`] holds at once.
const HELD: usize = 8;

/// The position weights as byte maps: per run of eight positions and byte `b` of a weight, the map sending bit `k`
/// to byte `b` of the weight of the run's position `k`.
pub(crate) struct ProductMaps(Vec<[ByteMap; WEIGHT_BYTES]>);

impl ProductMaps {
    pub fn new(weights: &[F128]) -> Self {
        let runs = weights.as_chunks::<8>().0.iter().map(|w| {
            let bytes = w.map(|w| u128::from(w).to_le_bytes());
            std::array::from_fn(|b| ByteMap::new(std::array::from_fn(|k| bytes[k][b])))
        });
        Self(runs.collect())
    }
}

/// The product polynomial's bit sums over a block: per pack `q` and coefficient `c`, entry `8 PROD_BYTES q + c` of
/// [`ProductBlock::run`]'s output is `sum over positions j of weights[j] * coefficient c of product(q, j)`.
///
/// Each run of eight positions' products are transposed to bytes, bit `k` of one a bit of the product at position
/// `k` ([`transpose_bits`]), so a weight byte's map takes it to that byte of the sum of the weights of the
/// positions whose bit is set: the sums are those maps' images, summed over the runs, as bytes ([`map_bytes`]).
pub(crate) struct ProductBlock {
    /// Per run, its products' bits: word `PROD_BYTES q + m` holds byte `m` of pack `q`'s.
    columns: Vec<[u64; COLUMN_WORDS]>,
}

impl ProductBlock {
    pub fn new() -> Self {
        Self {
            columns: vec![[0; COLUMN_WORDS]; BITS / 8],
        }
    }

    pub fn run(&mut self, maps: &ProductMaps, block: &[u64], out: &mut [u128; COLUMNS]) {
        for r in 0..5 {
            for z in (0..64).step_by(8) {
                let js = row_positions(r, z);
                let e = js.map(|j| embed_run(block, j));
                for x in 0..5 {
                    let columns = self.columns[js[x] / 8].as_chunks_mut::<PROD_BYTES>().0;
                    for (q, columns) in columns.iter_mut().enumerate() {
                        let bits = transpose_bits(products(e[x][q], e[(x + 1) % 5][q], e[(x + 2) % 5][q]));
                        *columns = bits[..PROD_BYTES].try_into().expect("a product's bytes");
                    }
                }
            }
        }
        for (v, out) in out.as_chunks_mut::<64>().0.iter_mut().enumerate() {
            let mut sums = [[0u64; 8]; WEIGHT_BYTES];
            for (o, sums) in sums.as_chunks_mut::<HELD>().0.iter_mut().enumerate() {
                for (columns, maps) in self.columns.iter().zip(&maps.0) {
                    let bits: Run = columns[8 * v..][..8].try_into().expect("eight words");
                    for (sum, map) in sums.iter_mut().zip(&maps[HELD * o..]) {
                        *sum = xor(*sum, map_bytes(map, bits));
                    }
                }
            }
            *out = transpose_bytes(&sums);
        }
    }
}

/// The sum of every subset of eight weights, indexed by the byte whose bits pick it.
pub fn byte_sums(weights: &[F128; 8]) -> [F128; 256] {
    let mut t = [F128::ZERO; 256];
    for (bit, &w) in weights.iter().enumerate() {
        for byte in 1usize << bit..2 << bit {
            t[byte] = t[byte - (1 << bit)] + w;
        }
    }
    t
}

/// Points of `{0, 1, infinity}^SKIP`, infinity as digit 2, variable `k` the `k`-th digit; and
/// those with a digit at infinity.
pub(crate) const TERNARY: usize = 3usize.pow(SKIP as u32);
pub(crate) const MIXED: usize = TERNARY - GROUP;
/// The products of a block position the skip sums: each group's mixed points.
pub const SLOTS: usize = 2 * MIXED;

/// The point of `{0, 1, infinity}^SKIP` of a pack of a group.
pub(crate) const fn ternary(q: usize) -> usize {
    (q & 1) + 3 * (q >> 1 & 1) + 9 * (q >> 2 & 1) + 27 * (q >> 3 & 1)
}

/// The mixed points in increasing order, each with the points at `0` and `1` along its lowest
/// digit at infinity, whose values sum to its own.
pub(crate) const MIXED_POINTS: [[usize; 3]; MIXED] = {
    let mut out = [[0; 3]; MIXED];
    let (mut i, mut t) = (0, 0);
    while t < TERNARY {
        let (mut k, mut step) = (0, 1);
        while k < SKIP && t / step % 3 != 2 {
            k += 1;
            step *= 3;
        }
        if k < SKIP {
            out[i] = [t, t - 2 * step, t - step];
            i += 1;
        }
        t += 1;
    }
    out
};

/// Eight values, one per position of a run of eight along `z`.
pub type Run = [u64; 8];

fn xor(a: Run, b: Run) -> Run {
    std::array::from_fn(|i| a[i] ^ b[i])
}

/// The packs of a run of positions at every mixed point of `{0, 1, infinity}^SKIP` of each group, at
/// their slots: along a variable, the value at infinity is the sum of the two others.
fn extend(packs: &[Run; PACKS], out: &mut [Run; SLOTS]) {
    // Both groups at once, group `half` in bits `32 * half ..` of each value.
    let mut values = [[0u64; 8]; TERNARY];
    for q in 0..GROUP {
        values[ternary(q)] = std::array::from_fn(|i| packs[q][i] | packs[GROUP + q][i] << 32);
    }
    for &[t, zero, one] in &MIXED_POINTS {
        values[t] = xor(values[zero], values[one]);
    }
    for half in 0..2 {
        for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
            out[MIXED * half + i] = values[t].map(|v| v >> (32 * half) & 0xffff_ffff);
        }
    }
}

/// The skip's sums over a block: per slot, the sum over positions of the position's weight times
/// its product. A weight is a polynomial in `s` ([`AtS::poly`]), whose two words each meet the
/// product in a carry-less product: the two partial products of its words. A mixed point keeps
/// only `u[j + 1] * u[j + 2]` of the unprojected `chi`, the rest being linear, so of degree one in
/// a variable at infinity. The packs themselves, the binary points, are the product polynomial's.
///
/// Lane `i` of a slot's sums is position `z + i` of every run along `z`: a row of five positions,
/// which `chi` mixes, is five runs, and their weights are eight consecutive ones.
///
/// [`AtS::poly`]: crate::poly::AtS::poly
pub(crate) struct SkipBlock {
    acc: Vec<[Wide8; 2]>,
    extended: Vec<[Run; SLOTS]>,
}

impl SkipBlock {
    pub fn new() -> Self {
        Self {
            acc: vec![[Wide8::ZERO; 2]; SLOTS],
            extended: vec![[[0; 8]; SLOTS]; 5],
        }
    }

    /// Sum a block, word `k` of each position's weight at `weights[k][j]`.
    pub fn run(&mut self, block: &[u64], weights: &[Vec<u64>; 2]) {
        self.acc.fill([Wide8::ZERO; 2]);
        for r in 0..5 {
            for z in (0..64).step_by(8) {
                let js = row_positions(r, z);
                for (extended, &j) in self.extended.iter_mut().zip(&js) {
                    extend(&embed_run(block, j), extended);
                }
                let w: [[Run; 2]; 5] = js.map(|j| weights.each_ref().map(|w| w[j..][..8].try_into().expect("a run")));
                let e = &self.extended;
                for (p, acc) in self.acc.iter_mut().enumerate() {
                    let mut sum = [Wide8::ZERO; 2];
                    for (x, w) in w.iter().enumerate() {
                        let product = clmul8_low(e[(x + 1) % 5][p], e[(x + 2) % 5][p]);
                        sum[0] += Wide8::mul(product, w[0]);
                        sum[1] += Wide8::mul(product, w[1]);
                    }
                    acc[0] += sum[0];
                    acc[1] += sum[1];
                }
            }
        }
    }

    /// The two partial products of slot `p`: the sums of the products times each word of their
    /// weights.
    pub fn get(&self, p: usize) -> [u128; 2] {
        self.acc[p].map(Wide8::sum)
    }
}
