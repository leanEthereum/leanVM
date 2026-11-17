//! The four bit-level rounds' sums over a block, by carry-less products on registers of
//! [`Vector`] lanes (PCLMULQDQ at any width, where AVX-512 and GFNI are not, or PMULL): per
//! [`slot`], the polynomial [`skip_row`](crate::kernels::skip_row) sums over the block.
//!
//! A register holds one value of [`L`] slices, a word each, so the extension is a sum of
//! registers and a slot's products are a register's lanes, at `L` positions' weights at once.
//!
//! A row's sum `sum over x of w[x] e[x + 1] e[x + 2]` is taken as
//! `e[2] (w[0] e[1] + w[1] e[3]) + e[4] (w[2] e[3] + w[3] e[0]) + w[4] (e[0] e[1])`: the two
//! cofactors are linear in the values, so they are multiplied out on the group's packs and
//! extended like them, [`WORDS`] words each. A slice then takes nine carry-less products a slot
//! where the five terms take fifteen, and eight a pack.

use primitives::hash::positions::row_positions;
use verifier::keccak::{BITS, EMBED_BITS};

use crate::basis::carry;
use crate::clmul::{V, Vector};
use crate::kernels::{GROUP, MIXED, PACKS, embed, slot};
use crate::witness::words;

/// Slices to a register, a word each.
const L: usize = 2 * V::N;
/// Words of a cofactor, a weight of two words times an embedding.
const WORDS: usize = 3;
const _: () = assert!(
    2 * (EMBED_BITS - 1) <= 64,
    "a cofactor's top word times an embedding is more than a word"
);

#[inline(always)]
fn load(words: &[u64; L]) -> V {
    // SAFETY: the module is compiled only where `V`'s features are, and `L` words are `2 * N`.
    unsafe { V::load(words.as_ptr()) }
}

/// [`extend_group`](crate::kernels::extend_group) on registers, for `F` groups at once:
/// `output(i, values)` takes output `i` of every group. The nine vectors of four are made one at a
/// time and passed straight to `output`, so nothing is stored.
#[inline(always)]
fn extend<const F: usize>(v: [&[V; GROUP]; F], mut output: impl FnMut(usize, [V; F])) {
    for k in 0..9 {
        // Vector `k` of each group: one of its four, or a sum of them.
        let w: [[V; 4]; F] = std::array::from_fn(|f| {
            std::array::from_fn(|l| {
                let q = |k: usize| v[f][4 * k + l];
                match k {
                    0..4 => q(k),
                    4 => q(0).xor(q(1)),
                    5 => q(2).xor(q(3)),
                    6 => q(0).xor(q(2)),
                    7 => q(1).xor(q(3)),
                    _ => q(0).xor(q(1)).xor(q(2).xor(q(3))),
                }
            })
        });
        if k >= 4 {
            for l in 0..4 {
                output(4 * (k - 4) + l, w.map(|w| w[l]));
            }
        }
        let low = w.map(|w| [w[0].xor(w[1]), w[2].xor(w[3]), w[0].xor(w[2]), w[1].xor(w[3])]);
        for l in 0..4 {
            output(20 + 4 * k + l, low.map(|low| low[l]));
        }
        output(56 + k, low.map(|low| low[0].xor(low[1])));
    }
}

/// A cofactor `wa * a + wb * b` on `L` slices' values, a register per word.
#[inline(always)]
fn cofactor(a: V, wa: &[V; 2], b: V, wb: &[V; 2]) -> [V; WORDS] {
    // Per weight word, the even and the odd slices' products.
    let parts: [[V; 2]; 2] = std::array::from_fn(|k| {
        [
            a.clmul::<0x00>(wa[k]).xor(b.clmul::<0x00>(wb[k])),
            a.clmul::<0x11>(wa[k]).xor(b.clmul::<0x11>(wb[k])),
        ]
    });
    let low = |k: usize| parts[k][0].unpacklo(parts[k][1]);
    let high = |k: usize| parts[k][0].high().unpacklo(parts[k][1].high());
    [low(0), high(0).xor(low(1)), high(1)]
}

/// [`skip_row`](crate::kernels::skip_row) over every row and slice of a block, [`L`] slices at a
/// time.
pub struct SkipBlock {
    /// Per slot and word offset, the sum of the products there.
    acc: [[V; WORDS]; 2 * MIXED],
    /// Per position of a row, its packs on `L` slices.
    packs: [[[u64; L]; PACKS]; 5],
    /// Per cofactor and word, its values on the group's packs.
    cofactors: [[[V; GROUP]; WORDS]; 2],
    /// Per output of the extension, the cofactors' factors `e[2]` and `e[4]`.
    factors: [[V; 2]; MIXED],
    /// The weights by word: word `k` of position `j` at `weights[k][j]`.
    weights: [Vec<u64>; 2],
}

impl SkipBlock {
    /// For blocks summed at the position weights `weights`, as polynomials.
    pub fn new(weights: &[[u64; 2]]) -> Box<Self> {
        Box::new(Self {
            acc: [[V::zero(); WORDS]; 2 * MIXED],
            packs: [[[0; L]; PACKS]; 5],
            cofactors: [[[V::zero(); GROUP]; WORDS]; 2],
            factors: [[V::zero(); 2]; MIXED],
            weights: [0, 1].map(|k| weights[..BITS].iter().map(|w| w[k]).collect()),
        })
    }

    /// Sum a block.
    pub fn run(&mut self, block: &[u64]) {
        self.acc = [[V::zero(); WORDS]; 2 * MIXED];
        for r in 0..5 {
            for z in (0..64).step_by(L) {
                let js = row_positions(r, z);
                // `L` positions from each `j`, transposed: a pack's slices side by side.
                for (packs, j) in self.packs.iter_mut().zip(js) {
                    for s in 0..L {
                        for (pack, e) in packs.iter_mut().zip(embed(words(block, j + s))) {
                            pack[s] = e.into();
                        }
                    }
                }
                let w = js.map(|j| [0, 1].map(|k| load(self.weights[k][j..].first_chunk().unwrap())));
                for half in 0..2 {
                    self.run_group(half, &w);
                }
            }
        }
    }

    /// Adds group `half` of the packs [`Self::run`] staged, at the row's weights `w`.
    #[inline(always)]
    fn run_group(&mut self, half: usize, w: &[[V; 2]; 5]) {
        let Self {
            acc,
            packs,
            cofactors,
            factors,
            ..
        } = self;
        let e: [[V; GROUP]; 5] = std::array::from_fn(|x| std::array::from_fn(|q| load(&packs[x][GROUP * half + q])));
        for q in 0..GROUP {
            let values = [
                cofactor(e[1][q], &w[0], e[3][q], &w[1]),
                cofactor(e[3][q], &w[2], e[0][q], &w[3]),
            ];
            for (cofactor, values) in cofactors.iter_mut().zip(values) {
                for (word, value) in cofactor.iter_mut().zip(values) {
                    word[q] = value;
                }
            }
        }
        // The values' walk keeps the cofactors' factors and sums the last term, of two words.
        extend([&e[0], &e[1], &e[2], &e[4]], |i, [e0, e1, e2, e4]| {
            factors[i] = [e2, e4];
            let products = e0.clmul::<0x00>(e1).unpacklo(e0.clmul::<0x11>(e1));
            for (acc, &w) in acc[slot(half, i)].iter_mut().zip(&w[4]) {
                *acc = acc.xor(products.clmul::<0x00>(w)).xor(products.clmul::<0x11>(w));
            }
        });
        for k in 0..WORDS {
            extend([&cofactors[0][k], &cofactors[1][k]], |i, [a, b]| {
                let [e2, e4] = factors[i];
                let acc = &mut acc[slot(half, i)][k];
                *acc = acc
                    .xor(e2.clmul::<0x00>(a).xor(e2.clmul::<0x11>(a)))
                    .xor(e4.clmul::<0x00>(b).xor(e4.clmul::<0x11>(b)));
            });
        }
    }

    /// The sum at slot `i`. Its sum at the last word offset is under a word, so three words hold it.
    pub fn get(&self, i: usize) -> [u64; 3] {
        let [sum @ .., _] = carry::<WORDS, { WORDS + 1 }>(&self.acc[i].map(V::sum));
        sum
    }
}
