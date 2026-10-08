//! One radix-four layer of the product tree, as its sumcheck prover folds it.
//!
//! A layer is a level of the tree read as rows of four children.
//! Its sumcheck binds the row index one bit at a time, lowest first.
//!
//! The prover handles the rounds two at a time.
//! Four rows sharing all but their two lowest bits form a block.
//! Each child of a block is a bilinear polynomial in those two bits:
//!
//! ```text
//!     V_c(Y1, Y2) = v_00 + Y1 (v_00 + v_10) + Y2 (v_00 + v_01) + Y1 Y2 (v_00 + v_10 + v_01 + v_11)
//! ```
//!
//! One pass sums `eq(q) * prod_c V_c(Y1, Y2)` over the blocks `q`.
//! That bivariate polynomial gives the first round's message, then the second's once `Y1` is bound.
//! The next pass folds four rows into one and sums the next two rounds' polynomial on the way.
//! Memory is therefore read once every two rounds.

use super::lanes::{Lane, Lanes, Polynomial, Xor};
use crate::PAR_THRESHOLD;
use parallel::SendPtr;
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::SplitEq;
use primitives::stream::{Stream, prefetch};
use std::mem::MaybeUninit;

/// Elements of the level one task of a pass reads.
///
/// That is 64 blocks, whose fold is a 6 KiB stage in L1.
const TASK: usize = 1024;

/// Elements in one block: four rows of four children.
const BLOCK: usize = 16;

/// Blocks between the one a pass reads and the one it prefetches.
///
/// That is a few groups of products ahead, longer than a fetch from memory takes.
const AHEAD: usize = 16;

/// Most low variables of the split eq table.
///
/// 2^12 entries of `E` is 96 KiB, which every task reads from L2.
pub(super) const EQ_LOW_VARS: usize = 12;

/// The sums of a block product's Karatsuba terms, in `Y2` then `Y1`, unreduced.
type Sums = [[F192Unreduced; 6]; 6];

/// A level of the product tree, as the rows its sumcheck folds.
pub(super) struct Layer {
    /// The stored rows, four children each, in order.
    ///
    /// Every row past them is all ones, the product tree's identity padding.
    values: Vec<F192>,
    /// The buffer a fold writes, then swaps with the values.
    spare: Vec<F192>,
}

impl Layer {
    pub(super) fn new(mut values: Vec<F192>) -> Self {
        // Complete the last row with ones; the rows after it stay implicit.
        values.resize(values.len().max(1).next_multiple_of(4), F192::ONE);
        Self {
            values,
            spare: Vec::new(),
        }
    }

    /// The polynomial of the next two rounds, block `q` weighed by `eq(q)`.
    pub(super) fn grid(&self, eq: &SplitEq) -> Grid {
        let values = &self.values;
        Grid::sum(values.len(), |task| {
            let start = TASK * task;
            let mut sums = BlockSums::<Lane>::new();
            sums.add(&values[start..(start + TASK).min(values.len())], start / BLOCK, eq);
            sums.finish()
        })
    }

    /// Binds the next two variables to `r`.
    ///
    /// Given `eq`, it also returns the polynomial of the two rounds after, from the rows it writes.
    pub(super) fn fold(&mut self, r: [F192; 2], eq: Option<&SplitEq>) -> Option<Grid> {
        let source = &self.values;
        let len = 4 * (source.len() / 4).div_ceil(4);
        self.spare.clear();
        self.spare.reserve(len);
        let destination = SendPtr(self.spare.spare_capacity_mut().as_mut_ptr());
        let fold = Fold::<Lane>::new(r);

        let grid = Grid::sum(source.len(), |task| {
            // Every source block becomes one row, so a task's output is a quarter of its input.
            let (start, end) = (TASK * task, (TASK * (task + 1)).min(source.len()));
            let rows = 4 * (end - start).div_ceil(BLOCK);

            // Fold into a stage that stays in L1, so the sums below read no memory.
            let mut stage = [MaybeUninit::uninit(); TASK / 4];
            fold.apply(&source[start..end], &mut stage[..rows]);
            // SAFETY: the fold wrote every slot of the stage it was given.
            let stage = unsafe { stage[..rows].assume_init_ref() };

            let mut sums = BlockSums::<Lane>::new();
            if let Some(eq) = eq {
                sums.add(stage, start / 4 / BLOCK, eq);
            }

            // The next pass reads the output long after this one evicts it.
            // Streaming stores save the fetch an ordinary store makes of each line it overwrites.
            //
            // SAFETY: tasks write disjoint windows of the reserved capacity, which together cover it.
            Stream::new().write(unsafe { destination.slice(start / 4, rows) }, stage);
            sums.finish()
        });

        // SAFETY: the tasks wrote every row.
        unsafe { self.spare.set_len(len) };
        std::mem::swap(&mut self.values, &mut self.spare);
        eq.map(|_| grid)
    }

    /// The message of a round with one variable left: two rows, so one pair of lines per child.
    ///
    /// Returns the coefficients of `X^1` through `X^4`.
    pub(super) fn last_round(&self) -> [F192; 4] {
        let [low, high] = self.last_rows();

        // Child `c` is the line from its value in the low row to its value in the high row.
        let line = |c: usize| [low[c], low[c] + high[c]];
        let mul = |u: F192, w: F192| u * w;
        let left = line(0).product(line(1), mul);
        let right = line(2).product(line(3), mul);
        let [_, c1, c2, c3, c4] = left.product(right, mul);
        [c1, c2, c3, c4]
    }

    /// Binds the last variable to `r`.
    pub(super) fn fold_last(&mut self, r: F192) {
        let [low, high] = self.last_rows();
        self.values = std::array::from_fn::<_, 4, _>(|c| low[c] + r * (low[c] + high[c])).to_vec();
    }

    /// The four children of the one row left once every variable is bound.
    pub(super) fn children(&self) -> [F192; 4] {
        *self.values.as_array().expect("every variable is bound")
    }

    /// The two rows of a layer with one variable left, the second all ones when implicit.
    fn last_rows(&self) -> [[F192; 4]; 2] {
        debug_assert!(self.values.len() <= 8, "one variable is left");
        let row = |r: usize| {
            self.values
                .get(4 * r..4 * r + 4)
                .map_or([F192::ONE; 4], |row| *row.as_array().unwrap())
        };
        [row(0), row(1)]
    }
}

/// The polynomial `P(Y1, Y2) = sum_q eq(q) prod_c V_c(Y1, Y2)` of two consecutive rounds.
///
/// Its coefficients are indexed `[Y2 power][Y1 power]`, and `Y1` is bound first.
pub(super) struct Grid([[F192; 5]; 5]);

impl Grid {
    /// The sum of `task`'s sums over the tasks covering `len` elements, in parallel when the level is large.
    fn sum(len: usize, task: impl Fn(usize) -> Sums + Sync) -> Self {
        let tasks = len.div_ceil(TASK);
        let zero = [[F192Unreduced::ZERO; 6]; 6];
        let sums = if len / 4 >= PAR_THRESHOLD {
            parallel::map_reduce(tasks, || zero, task, Xor::xor)
        } else {
            (0..tasks).map(task).fold(zero, Xor::xor)
        };

        // The terms combine in `Y1`, then in `Y2`.
        let in_y1 = sums.map(|terms| <[F192; 3]>::combine(terms.map(F192Unreduced::reduce)));
        Self(<[[F192; 3]; 3]>::combine(in_y1))
    }

    /// The first round's message, its rows weighed by `eq(p, Y2)`.
    ///
    /// In characteristic two that weight is `1 + p` at `Y2 = 0` and `p` at `Y2 = 1`, so:
    ///
    /// ```text
    ///     [X^k] = P_{0,k} + p * sum_{m >= 1} P_{m,k}
    /// ```
    ///
    /// Returns the coefficients of `X^1` through `X^4`.
    pub(super) fn first_round(&self, p: F192) -> [F192; 4] {
        let [low, upper @ ..] = &self.0;
        std::array::from_fn(|i| {
            let k = i + 1;
            low[k] + p * upper.iter().fold(F192::ZERO, |sum, row| sum + row[k])
        })
    }

    /// The second round's message, once `Y1` is bound to `r`.
    ///
    /// Returns the coefficients of `X^1` through `X^4`, each `sum_k r^k P_{m,k}`.
    pub(super) fn second_round(&self, r: F192) -> [F192; 4] {
        std::array::from_fn(|i| self.0[i + 1].iter().rev().fold(F192::ZERO, |sum, &c| sum * r + c))
    }
}

/// The running sums of block products over a range of blocks, `L::WIDTH` blocks at a time.
///
/// It sums each product's Karatsuba terms, which combine into its coefficients only once, after the sum.
struct BlockSums<L: Lanes>([[L::Wide; 6]; 6]);

impl<L: Lanes> BlockSums<L> {
    fn new() -> Self {
        Self(std::array::from_fn(|_| std::array::from_fn(|_| L::zero_wide())))
    }

    /// Adds the blocks of `rows`, the first being block `first` of the layer.
    ///
    /// The last block may be short: its missing rows are ones.
    #[inline(always)]
    fn add(&mut self, rows: &[F192], first: usize, eq: &SplitEq) {
        let (blocks, _) = rows.as_chunks::<BLOCK>();
        let groups = blocks.len() / L::WIDTH;
        for g in 0..groups {
            let start = L::WIDTH * g;

            // A group's products take long enough that the hardware's prefetch falls behind.
            if let Some(ahead) = blocks.get(start + AHEAD..start + AHEAD + L::WIDTH) {
                prefetch(ahead);
            }

            // A group's blocks share a high weight, since the low table is a whole number of groups.
            let q = first + start;
            let low = L::load(&eq.low[q & (eq.low.len() - 1)..]);
            self.add_group(
                blocks[start..start + L::WIDTH].as_flattened(),
                low * L::splat(eq.high[q >> eq.low_log()]),
            );
        }
        let q = first + L::WIDTH * groups;

        // The blocks short of a whole group, the last one possibly short of rows.
        let tail = &rows[BLOCK * (q - first)..];
        if !tail.is_empty() {
            // Missing rows are ones, and missing blocks weigh zero.
            let mut padded = [F192::ONE; BLOCK * 4];
            padded[..tail.len()].copy_from_slice(tail);
            let mut weights = [F192::ZERO; 4];
            for (block, weight) in weights[..tail.len().div_ceil(BLOCK)].iter_mut().enumerate() {
                *weight = eq.at(q + block);
            }
            self.add_group(&padded, L::load(&weights));
        }
    }

    /// Adds `L::WIDTH` whole blocks, block `l` in lane `l`, each scaled by its lane of `weight`.
    #[inline(always)]
    fn add_group(&mut self, blocks: &[F192], weight: L) {
        // Row `r` of each block: `r = 2 b2 + b1`, its two bits being `Y1` and `Y2`.
        let [v00, v10, v01, v11] = std::array::from_fn(|r| L::gather(&blocks[4 * r..], BLOCK));

        // Child `c` as `[[1, Y1], [Y2, Y1 Y2]]` coefficients.
        let child = |c: usize| {
            let y1 = v00[c] + v10[c];
            [[v00[c], y1], [v00[c] + v01[c], y1 + v01[c] + v11[c]]]
        };

        // The weight scales one factor, so the product carries it.
        let [[a, b], [c, d]] = child(0);
        let first = [[a * weight, b * weight], [c * weight, d * weight]];

        // Two pairs of bilinear factors make two biquadratics.
        let (left, right) = (
            Self::biquadratic(first, child(1)),
            Self::biquadratic(child(2), child(3)),
        );

        // Their product's terms, each multiplied into its own sum.
        // The terms' operand pairs come first, so no product waits in memory for its sum.
        for (sums, (u, w)) in self.0.iter_mut().zip(left.terms(right, |u, w| (u, w))) {
            for (sum, (x, y)) in sums.iter_mut().zip(u.terms(w, |x, y| (x, y))) {
                *sum = sum.xor(x.mul_wide(y));
            }
        }
    }

    /// The product of two bilinear polynomials, nine products.
    #[inline(always)]
    fn biquadratic(a: [[L; 2]; 2], b: [[L; 2]; 2]) -> [[L; 3]; 3] {
        a.product(b, |u, w| u.product(w, |x, y| x * y))
    }

    fn finish(self) -> Sums {
        self.0.map(|row| row.map(L::sum))
    }
}

/// The fold of two variables at a pair of challenges.
struct Fold<L> {
    r: [L; 2],
}

impl<L: Lanes> Fold<L> {
    fn new(r: [F192; 2]) -> Self {
        Self { r: r.map(L::splat) }
    }

    /// Folds each block of `source` into one row of `out`.
    ///
    /// The last block may be short: its missing rows are ones.
    #[inline(always)]
    fn apply(&self, source: &[F192], out: &mut [MaybeUninit<F192>]) {
        let (blocks, short) = source.as_chunks::<BLOCK>();
        let (rows, _) = out.as_chunks_mut::<4>();
        for (b, (block, row)) in blocks.iter().zip(&mut *rows).enumerate() {
            if let Some(ahead) = blocks.get(b + AHEAD) {
                prefetch(ahead);
            }
            self.block(block, row);
        }
        if !short.is_empty() {
            let mut padded = [F192::ONE; BLOCK];
            padded[..short.len()].copy_from_slice(short);
            self.block(&padded, &mut rows[blocks.len()]);
        }
    }

    /// One block's children at `Y1 = r_0` then `Y2 = r_1`, `L::WIDTH` children at a time.
    #[inline(always)]
    fn block(&self, block: &[F192; BLOCK], out: &mut [MaybeUninit<F192>; 4]) {
        let [r0, r1] = self.r;
        for c in (0..4).step_by(L::WIDTH) {
            let row = |r: usize| L::load(&block[4 * r + c..]);
            let low = row(0) + r0 * (row(0) + row(1));
            let high = row(2) + r0 * (row(2) + row(3));
            (low + r1 * (low + high)).store(&mut out[c..]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::interp;

    /// The level with `len` stored elements, distinct and nonzero.
    fn level(len: usize) -> Vec<F192> {
        (0..len)
            .map(|i| F192::new((17 * i + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
            .collect()
    }

    /// Row `r` of a level of `rows` logical rows, ones past the stored ones.
    fn row(values: &[F192], r: usize) -> [F192; 4] {
        std::array::from_fn(|c| values.get(4 * r + c).copied().unwrap_or(F192::ONE))
    }

    #[test]
    fn grid_is_the_two_rounds_of_the_dense_sumcheck() {
        // Invariant: the grid's two messages are the two quartics a round-by-round prover sends.
        //
        // Fixture state: 2^v blocks of four rows, stored as a prefix of every length shape.
        //
        //     round 1:  s1(X) = sum_{b2, q} eq(p, b2) eq(q) prod_c V_c(X, b2, q)
        //     round 2:  s2(X) = sum_q eq(q) prod_c V_c(r, X, q)
        for vars in 0..6 {
            let blocks = 1usize << vars;
            for len in [1, 4, 12, 16, 20, 4 * blocks * 4 - 4, 16 * blocks] {
                if len > 16 * blocks {
                    continue;
                }
                let values = level(len);
                let layer = Layer::new(values.clone());
                let point: Vec<F192> = (0..vars).map(|i| F192::new(31 + i as u64, 7, 11)).collect();
                let eq = SplitEq::with_low_vars(&point, 2);
                let grid = layer.grid(&eq);
                let (p, r) = (F192::new(5, 6, 7), F192::new(9, 10, 11));

                // The dense quartic at `x`, from the rows' children at the two variables' values.
                let dense = |y1: F192, y2: Option<F192>| {
                    (0..blocks).fold(F192::ZERO, |sum, q| {
                        let at = |b: usize, y: F192| {
                            let [low, high] = [row(&values, 4 * q + b), row(&values, 4 * q + b + 1)];
                            std::array::from_fn::<_, 4, _>(|c| interp(low[c], high[c], y))
                        };
                        let value = |b2: F192| {
                            let [low, high] = [at(0, y1), at(2, y1)];
                            (0..4).fold(F192::ONE, |prod, c| prod * interp(low[c], high[c], b2))
                        };
                        let weighed =
                            y2.map_or_else(|| (F192::ONE + p) * value(F192::ZERO) + p * value(F192::ONE), value);
                        sum + eq.at(q) * weighed
                    })
                };
                let first = |x: F192| dense(x, None);
                let second = |x: F192| dense(r, Some(x));

                // A message holds `X^1..X^4`; the constant is the value at zero.
                let eval = |c: [F192; 4], c0: F192, x: F192| c.iter().rev().fold(F192::ZERO, |s, &k| (s + k) * x) + c0;
                for x in [F192::ONE, F192::Y, F192::Y.square(), F192::new(3, 1, 4)] {
                    assert_eq!(eval(grid.first_round(p), first(F192::ZERO), x), first(x), "len={len}");
                    assert_eq!(
                        eval(grid.second_round(r), second(F192::ZERO), x),
                        second(x),
                        "len={len}"
                    );
                }
            }
        }
    }

    #[test]
    fn fold_binds_the_two_lowest_bits() {
        // Invariant: row q after the fold is block q's children at (r0, r1), ones where implicit.
        //
        // Fixture state: lengths around the lane width and the task size, so every tail path runs.
        let r = [F192::new(2, 3, 4), F192::new(5, 6, 7)];
        for len in [4, 8, 12, 16, 20, 60, 64, 68, 1020, 1024, 1028, 4096 + 36, 1 << 15] {
            let values = level(len);
            let mut layer = Layer::new(values.clone());
            layer.fold(r, None);
            let rows = (len / 4).div_ceil(4);
            assert_eq!(layer.values.len(), 4 * rows, "len={len}");
            for q in 0..rows {
                let at = |b: usize| row(&values, 4 * q + b);
                let want: [F192; 4] = std::array::from_fn(|c| {
                    interp(interp(at(0)[c], at(1)[c], r[0]), interp(at(2)[c], at(3)[c], r[0]), r[1])
                });
                assert_eq!(row(&layer.values, q), want, "len={len}, q={q}");
            }
        }
    }

    #[test]
    fn fused_fold_sums_what_a_fresh_pass_sums() {
        // Invariant: the grid summed from the fold's stage is the grid of the folded level.
        //
        // Fixture state: a level large enough to run in parallel, and short ones in sequence.
        for len in [64, 200, 4 * PAR_THRESHOLD * 4 + 52] {
            let rows = (len / 4).next_power_of_two().max(16);
            let vars = rows.ilog2() as usize - 4;
            let point: Vec<F192> = (0..vars).map(|i| F192::new(3 + i as u64, 1, 2)).collect();
            let eq = SplitEq::with_low_vars(&point, EQ_LOW_VARS);
            let mut layer = Layer::new(level(len));
            let fused = layer
                .fold([F192::Y, F192::new(8, 9, 10)], Some(&eq))
                .expect("a weight was given");
            assert_eq!(fused.0, layer.grid(&eq).0, "len={len}");
        }
    }

    #[test]
    fn lanes_match_the_portable_element() {
        // Invariant: the target's lanes compute the same sums and folds as the portable element.
        let values = level(16 * 4 * 3 + 36);
        let point: Vec<F192> = (0..4).map(|i| F192::new(9 + i as u64, 2, 5)).collect();
        let eq = SplitEq::with_low_vars(&point, 2);
        let sums = |wide: bool| {
            if wide {
                let mut sums = BlockSums::<Lane>::new();
                sums.add(&values, 0, &eq);
                sums.finish()
            } else {
                let mut sums = BlockSums::<F192>::new();
                sums.add(&values, 0, &eq);
                sums.finish()
            }
        };
        assert_eq!(sums(true), sums(false));

        let r = [F192::new(1, 2, 3), F192::Y];
        let rows = (values.len() / 4).div_ceil(4);
        let mut wide = vec![MaybeUninit::uninit(); 4 * rows];
        let mut narrow = wide.clone();
        Fold::<Lane>::new(r).apply(&values, &mut wide);
        Fold::<F192>::new(r).apply(&values, &mut narrow);
        // SAFETY: both folds wrote every slot.
        let (wide, narrow) = unsafe { (wide.assume_init_ref(), narrow.assume_init_ref()) };
        assert_eq!(wide, narrow);
    }
}
