//! The four bit-level rounds' sums over a block with carry-less products (x86 without GFNI): per
//! [`slot`], the polynomial [`skip_row`](crate::kernels::skip_row) sums over the block.
//!
//! A row's sum `sum over x of w[x] e[x + 1] e[x + 2]` is taken as `e[2] A + e[4] B + e[0] C`, with
//! the cofactors `A = w[0] e[1] + w[1] e[3]`, `B = w[2] e[3] + w[3] e[0]` and `C = w[4] e[1]`.
//! They are linear in the values, so they are multiplied out on the row's packs and extended like
//! them: a cofactor has three words, and a slot takes nine products of an embedding and a word
//! where [`skip_row`](crate::kernels::skip_row) takes fifteen of an embedding, a product and a
//! weight's word.

use primitives::hash::positions::row_positions;

use crate::clmul::{V, Vector};
use crate::kernels::{GROUP, MIXED, PACKS, embed};
use crate::witness::words;

cfg_select! {
    target_feature = "vpclmulqdq" => {
        use core::arch::x86_64::*;

        /// Groups a register holds, a lane each.
        const GROUPS: usize = 2;

        /// Packs `q` and `q + 1` of every group, a lane each.
        #[inline(always)]
        fn load_packs(e: &[u32; PACKS], q: usize) -> V {
            // SAFETY: AVX2 is enabled at compile time (the module's cfg), and each load is of two
            // packs of `e`.
            unsafe {
                let [low, high] = [0, 1].map(|g| _mm_loadl_epi64(e[GROUP * g + q..][..2].as_ptr().cast()));
                _mm256_cvtepu32_epi64(_mm_unpacklo_epi64(low, high))
            }
        }

        /// Where a sum's lanes hold output `i` of group `half`: a register's lanes are the
        /// groups' outputs `i`.
        const fn at(half: usize, i: usize) -> usize {
            GROUPS * i + half
        }
    }
    _ => {
        /// Groups a register holds, a lane each.
        const GROUPS: usize = 1;

        /// Packs `q` and `q + 1`.
        #[inline(always)]
        fn load_packs(e: &[u32; PACKS], q: usize) -> V {
            // SAFETY: two packs of `e`.
            unsafe { V::load_packs(e[q..][..2].as_ptr()) }
        }

        /// Where a sum's lanes hold output `i` of group `half`: a group's outputs, then the
        /// other's.
        const fn at(half: usize, i: usize) -> usize {
            MIXED * half + i
        }
    }
}
const _: () = assert!(GROUPS == V::N);

/// The lanes of two words a slot's products read: `[e[2], e[4]]`, `[A0, B0]`, `[A1, B1]`,
/// `[A2, B2]`, `[C0, C1]` and `[C2, e[0]]`, word `k` of a cofactor its coefficients from `64 k`.
const FIELDS: usize = 6;

/// Per word of the cofactors, a block's sums of the products of the word, at [`at`] each output
/// of [`extend_group`](crate::kernels::extend_group) of each group.
type Acc = [[[u64; 2]; 2 * MIXED]; 3];

/// The pairs of lanes of a vector of four whose sums are its low mixed points, in the order of
/// [`extend_group`](crate::kernels::extend_group).
const LOW_MIXED: [(usize, usize); 4] = [(0, 1), (2, 3), (0, 2), (1, 3)];

/// [`skip_row`](crate::kernels::skip_row) over every row and slice of a block, a row at a time.
pub struct SkipBlock<'a> {
    weights: &'a [[u64; 2]],
    /// The embeddings of a row's positions.
    e: [[u32; PACKS]; 5],
    /// Per field, the nine vectors of four of [`extend_group`](crate::kernels::extend_group) of
    /// [`GROUPS`] groups, a register each lane: the packs, then their sums.
    vectors: [[[V; 4]; 9]; FIELDS],
    /// The block's sums.
    acc: Acc,
}

impl<'a> SkipBlock<'a> {
    /// For blocks summed at the position weights `weights`, as polynomials.
    pub fn new(weights: &'a [[u64; 2]]) -> Box<Self> {
        Box::new(Self {
            weights,
            e: [[0; PACKS]; 5],
            vectors: [[[V::zero(); 4]; 9]; FIELDS],
            acc: [[[0; 2]; 2 * MIXED]; 3],
        })
    }

    /// Sum a block.
    pub fn run(&mut self, block: &[u64]) {
        self.acc = [[[0; 2]; 2 * MIXED]; 3];
        for r in 0..5 {
            for z in 0..64 {
                let js = row_positions(r, z);
                for (e, &j) in self.e.iter_mut().zip(&js) {
                    *e = embed(words(block, j));
                }
                // Each lane a weight's two words.
                let w = js.map(|j| {
                    let [low, high] = self.weights[j];
                    V::splat(low).unpacklo(V::splat(high))
                });
                for pass in (0..2).step_by(GROUPS) {
                    self.cofactors(pass, w);
                    self.products(pass);
                }
            }
        }
    }

    /// The [`FIELDS`] of the packs of the groups from `pass`, at the row's weights `w`, and the
    /// vectors their sums make.
    #[inline(always)]
    fn cofactors(&mut self, pass: usize, w: [V; 5]) {
        for q in (0..GROUP).step_by(2) {
            let e: [V; 5] = self.e.each_ref().map(|e| load_packs(e, GROUP * pass + q));
            // An embedding times a weight: per pack of the pair, the products of its words.
            let product = |e: V, w: V| {
                [
                    [e.clmul::<0x00>(w), e.clmul::<0x10>(w)],
                    [e.clmul::<0x01>(w), e.clmul::<0x11>(w)],
                ]
            };
            let sum = |a: [[V; 2]; 2], b: [[V; 2]; 2]| -> [[V; 2]; 2] {
                std::array::from_fn(|h| std::array::from_fn(|k| a[h][k].xor(b[h][k])))
            };
            let a = sum(product(e[1], w[0]), product(e[3], w[1]));
            let b = sum(product(e[3], w[2]), product(e[0], w[3]));
            let c = product(e[1], w[4]);
            for h in 0..2 {
                // Pack `q + h`'s embeddings in the low word.
                let e = e.map(|e| if h == 0 { e } else { e.high() });
                let ([a0, a1], [b0, b1], [c0, c1]) = (a[h], b[h], c[h]);
                let fields = [
                    e[2].unpacklo(e[4]),
                    a0.unpacklo(b0),
                    a0.high().xor(a1).unpacklo(b0.high().xor(b1)),
                    a1.high().unpacklo(b1.high()),
                    c0.unpacklo(c0.high().xor(c1)),
                    c1.high().unpacklo(e[0]),
                ];
                for (vectors, field) in self.vectors.iter_mut().zip(fields) {
                    vectors[(q + h) / 4][(q + h) % 4] = field;
                }
            }
        }
        for v in &mut self.vectors {
            for l in 0..4 {
                let (v4, v5) = (v[0][l].xor(v[1][l]), v[2][l].xor(v[3][l]));
                [v[4][l], v[5][l], v[6][l], v[7][l], v[8][l]] =
                    [v4, v5, v[0][l].xor(v[2][l]), v[1][l].xor(v[3][l]), v4.xor(v5)];
            }
        }
    }

    /// Adds the products of the groups from `pass` to their sums, the extension's low points
    /// summed as the products read them.
    #[inline(always)]
    fn products(&mut self, pass: usize) {
        let Self { vectors, acc, .. } = self;
        for k in 0..9 {
            let v = |l: usize| vectors.each_ref().map(|v| v[k][l]);
            if k >= 4 {
                for l in 0..4 {
                    accumulate(acc, pass, 4 * (k - 4) + l, v(l));
                }
            }
            for (j, (a, b)) in LOW_MIXED.into_iter().enumerate() {
                let (a, b) = (v(a), v(b));
                accumulate(acc, pass, 20 + 4 * k + j, std::array::from_fn(|f| a[f].xor(b[f])));
            }
            let all = vectors
                .each_ref()
                .map(|v| v[k][0].xor(v[k][1]).xor(v[k][2].xor(v[k][3])));
            accumulate(acc, pass, 56 + k, all);
        }
    }

    /// The sum at slot `i`: the products of word `k` of the cofactors from coefficient `64 k`.
    pub fn get(&self, slot: usize) -> [u64; 3] {
        let (half, i) = if slot < 128 {
            (slot / 64, slot % 64)
        } else {
            (slot - 128, 64)
        };
        let [s0, s1, s2] = self.acc.each_ref().map(|acc| acc[at(half, i)]);
        [s0[0], s0[1] ^ s1[0], s1[1] ^ s2[0]]
    }
}

/// Adds the products of the [`FIELDS`] at output `i` of the groups from `pass` to their sums.
#[inline(always)]
fn accumulate(acc: &mut Acc, pass: usize, i: usize, [e, w0, w1, w2, wc, wd]: [V; FIELDS]) {
    let sums = [
        e.clmul::<0x00>(w0).xor(e.clmul::<0x11>(w0)).xor(wd.clmul::<0x01>(wc)),
        e.clmul::<0x00>(w1).xor(e.clmul::<0x11>(w1)).xor(wd.clmul::<0x11>(wc)),
        e.clmul::<0x00>(w2).xor(e.clmul::<0x11>(w2)).xor(wd.clmul::<0x01>(wd)),
    ];
    for (acc, sum) in acc.iter_mut().zip(sums) {
        // Lane `g` is group `pass + g`.
        let acc = acc[at(pass, i)..].as_mut_ptr().cast::<u64>();
        // SAFETY: `GROUPS` lanes of `acc`.
        unsafe { V::store(acc, V::load(acc).xor(sum)) };
    }
}
