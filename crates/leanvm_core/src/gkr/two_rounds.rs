//! A tall layer's sumcheck rounds two per pass, on AVX-512.
//!
//! Four rows sharing all but their two lowest index bits form a block.
//! Each child of a block is bilinear in those two bits, `Y1` the lowest:
//!
//! ```text
//!     V_c(Y1, Y2) = v_0 + Y1 (v_0 + v_1) + Y2 (v_0 + v_2) + Y1 Y2 (v_0 + v_1 + v_2 + v_3)
//! ```
//!
//! One pass sums `P(Y1, Y2) = sum_q eq(q) prod_c V_c(Y1, Y2)` over the blocks `q`, of degree four in each variable.
//! It gives the first round's message, and the second's once the first challenge is drawn.
//! The next pass folds each block into one row at both challenges, and sums the next pair's polynomial from the folded rows while they are in L1.
//! A layer is therefore read once every two rounds rather than once a round.
//!
//! A block's product is Karatsuba's for each pair of children, nine products each.
//! The two halves are multiplied at the 25 points of a grid, `{0, 1, t, t + 1, inf}` in each variable, with `t = y`.
//! Those products are summed over the blocks unreduced, and interpolated to coefficients once per pass.
//! The eight lanes hold eight blocks.

use super::vertical::covered;
use super::{SplitEq, coarsen};
use parallel::SendPtr;
use primitives::field::F192;
use primitives::field::x8::{F192x8, Sum8};
use primitives::stream::Stream;
use std::ops::Range;
use std::sync::LazyLock;

/// Elements in a group: eight blocks of four rows of four children.
const GROUP: usize = 128;

/// Elements of a layer one task reads: sixteen groups, whose fold is four groups of a 12 KiB stage.
const TASK: usize = 16 * GROUP;

/// Elements of the stage a fold writes for one task.
const STAGE: usize = TASK / 4;

/// A block's product at the grid's points, `[Y1 point][Y2 point]`, summed over blocks.
type Values = [[F192; 5]; 5];

/// The same, unreduced and summed over the lanes.
type Sums = [[Sum8; 5]; 5];

/// The polynomial `P(Y1, Y2)` of two consecutive rounds, as coefficients `[Y2 power][Y1 power]`.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct Grid([[F192; 5]; 5]);

impl Grid {
    /// The polynomial whose values at the grid's points are `values`.
    fn interpolate(values: Values) -> Self {
        let in_y2 = values.map(coefficients);
        Self(std::array::from_fn(|m| {
            coefficients(std::array::from_fn(|i| in_y2[i][m]))
        }))
    }

    /// The first round's message, its pairs weighed by `eq(p, Y2)`.
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

    /// The second round's message, once `Y1` is bound to `r`: the coefficients of `X^1` through `X^4`, each `sum_k r^k P_{m,k}`.
    pub(super) fn second_round(&self, r: F192) -> [F192; 4] {
        std::array::from_fn(|i| self.0[i + 1].iter().rev().fold(F192::ZERO, |sum, &c| sum * r + c))
    }
}

/// The inverse of `[x, x^2, x^3]` over the finite points `1, t, t + 1`: what recovers the middle coefficients.
static MIDDLE: LazyLock<[[F192; 3]; 3]> = LazyLock::new(|| {
    let rows = [F192::ONE, F192::Y, F192::Y + F192::ONE].map(|x| [x, x * x, x * x * x]);
    let m = |i: usize, j: usize| rows[i][j];
    let cofactor = |i: usize, j: usize| {
        let (r0, r1) = ((i + 1) % 3, (i + 2) % 3);
        let (c0, c1) = ((j + 1) % 3, (j + 2) % 3);
        m(r0, c0) * m(r1, c1) + m(r0, c1) * m(r1, c0)
    };
    let det = (0..3).fold(F192::ZERO, |sum, j| sum + m(0, j) * cofactor(0, j));
    let inv = det.inv();
    std::array::from_fn(|i| std::array::from_fn(|j| cofactor(j, i) * inv))
});

/// The coefficients of a quartic from its values at `0, 1, t, t + 1, inf`, the last being its leading coefficient.
fn coefficients([at0, at1, at_t, at_t1, lead]: [F192; 5]) -> [F192; 5] {
    let fourth = |x: F192| x.square().square();
    let (t, t1) = (F192::Y, F192::Y + F192::ONE);
    let residual = [
        at1 + at0 + lead,
        at_t + at0 + lead * fourth(t),
        at_t1 + at0 + lead * fourth(t1),
    ];
    let [c1, c2, c3] = MIDDLE.map(|row| (0..3).fold(F192::ZERO, |sum, j| sum + row[j] * residual[j]));
    [at0, c1, c2, c3, lead]
}

/// A quadratic `[a_0, a_1, a_2]` at `0, 1, t, t + 1, inf`.
#[inline(always)]
fn at_points([a0, a1, a2]: [F192x8; 3]) -> [F192x8; 5] {
    let high = a1 + a2;
    let at_t = a0 + (a1 + a2.mul_y()).mul_y();
    [a0, a0 + high, at_t, at_t + high, a2]
}

/// The product of two lines, three products.
#[inline(always)]
fn line_product([u0, u1]: [F192x8; 2], [w0, w1]: [F192x8; 2]) -> [F192x8; 3] {
    let (low, high) = (u0 * w0, u1 * w1);
    [low, (u0 + u1) * (w0 + w1) + low + high, high]
}

/// The product of two bilinear polynomials `[Y2 power][Y1 power]`, nine products.
#[inline(always)]
fn biquadratic([a0, a1]: [[F192x8; 2]; 2], [b0, b1]: [[F192x8; 2]; 2]) -> [[F192x8; 3]; 3] {
    let sum = |[u0, u1]: [F192x8; 2], [w0, w1]: [F192x8; 2]| [u0 + w0, u1 + w1];
    let (low, high) = (line_product(a0, b0), line_product(a1, b1));
    let cross = line_product(sum(a0, a1), sum(b0, b1));
    [low, std::array::from_fn(|k| cross[k] + low[k] + high[k]), high]
}

/// A biquadratic at the grid's points, `[Y1 point][Y2 point]`.
#[inline(always)]
fn on_grid(poly: [[F192x8; 3]; 3]) -> [[F192x8; 5]; 5] {
    let in_y1 = poly.map(at_points);
    std::array::from_fn(|i| at_points([in_y1[0][i], in_y1[1][i], in_y1[2][i]]))
}

/// Adds eight blocks to `sums`, block `l` in lane `l` scaled by its lane of `weight`.
///
/// `v[4 r + c]` is child `c` of row `r` of each block, `r = 2 b2 + b1`.
#[inline(always)]
fn add_group(v: &[F192x8; 16], weight: F192x8, sums: &mut Sums) {
    let bilinear = |v0: F192x8, v1: F192x8, v2: F192x8, v3: F192x8| {
        let y1 = v0 + v1;
        [[v0, y1], [v0 + v2, y1 + v2 + v3]]
    };
    let child = |c: usize| bilinear(v[c], v[4 + c], v[8 + c], v[12 + c]);
    // The weight scales one child, so the product carries it.
    let weighted = bilinear(v[0] * weight, v[4] * weight, v[8] * weight, v[12] * weight);
    let left = on_grid(biquadratic(weighted, child(1)));
    let right = on_grid(biquadratic(child(2), child(3)));
    for ((sums, left), right) in sums.iter_mut().zip(&left).zip(&right) {
        for ((sum, &u), &w) in sums.iter_mut().zip(left).zip(right) {
            *sum ^= u.mul_sum(w);
        }
    }
}

/// The weights of group `g`: `eq(q)` of its eight blocks.
#[inline(always)]
fn weights(eq: &SplitEq, g: usize) -> F192x8 {
    debug_assert!(eq.lo_bits >= 3, "a group spans eight blocks of the low table");
    let shift = eq.lo_bits - 3;
    eq.lo8[g & ((1 << shift) - 1)] * F192x8::splat(eq.hi[g >> shift])
}

/// Group `g` of a row table into `out`, transposed, ones past its end.
#[inline(always)]
fn load(values: &[F192], g: usize, out: &mut [F192x8; 16]) {
    match values.get(GROUP * g..GROUP * (g + 1)) {
        Some(run) => F192x8::load_blocks(run.try_into().expect("a group"), out),
        None => {
            let mut padded = [F192::ONE; GROUP];
            let tail = &values[(GROUP * g).min(values.len())..];
            padded[..tail.len()].copy_from_slice(tail);
            F192x8::load_blocks(&padded, out);
        }
    }
}

/// Two blocks folded at `r0` then `r1`, one row each: register `h` holds row `h` of the first block, then of the second.
#[inline(always)]
fn fold_pair(pair: &[F192; 32], r0: F192x8, r1: F192x8) -> F192x8 {
    let rows = |at: usize| {
        let load = |b: usize| F192x8::load(pair[at + 16 * b..at + 16 * b + 8].try_into().expect("two rows"));
        F192x8::halves(load(0), load(1))
    };
    let (low, high) = rows(0);
    let low = low + r0 * (low + high);
    let (high_low, high_high) = rows(8);
    let high = high_low + r0 * (high_low + high_high);
    low + r1 * (low + high)
}

/// Adds the groups `groups` of `values` to `sums`, skipping those `ones` covers, group `g` being `first + g` of the layer.
#[inline(always)]
fn add_groups(
    values: &[F192],
    ones: &[Range<usize>],
    groups: Range<usize>,
    first: usize,
    eq: &SplitEq,
    sums: &mut Sums,
) {
    let mut group = [F192x8::splat(F192::ZERO); 16];
    for g in groups {
        let rows = 32 * (first + g);
        if !covered(ones, rows..rows + 32) {
            load(values, g, &mut group);
            add_group(&group, weights(eq, first + g), sums);
        }
    }
}

fn reduce(sums: Sums) -> Values {
    sums.map(|row| row.map(Sum8::reduce))
}

fn add(a: [Values; 3], b: [Values; 3]) -> [Values; 3] {
    std::array::from_fn(|t| std::array::from_fn(|j| std::array::from_fn(|i| a[t][j][i] + b[t][j][i])))
}

/// `sum_i f(i)` over `0..tasks`, in parallel when there are several.
fn sum_tasks(tasks: usize, f: impl Fn(usize) -> [Values; 3] + Sync) -> [Values; 3] {
    let zero = [[[F192::ZERO; 5]; 5]; 3];
    if tasks > 1 {
        parallel::map_reduce(tasks, || zero, f, add)
    } else {
        (0..tasks).map(f).fold(zero, add)
    }
}

/// The tasks of a pass over the three layers: the tree and the task's index in it.
fn tasks(layers: &[(&[F192], &[Range<usize>]); 3]) -> Vec<(usize, usize)> {
    (0..3)
        .flat_map(|t| (0..layers[t].0.len().div_ceil(TASK)).map(move |k| (t, k)))
        .collect()
}

/// The polynomials of the next two rounds of the three layers, from their stored rows and runs of identity rows.
pub(super) fn grids(layers: [(&[F192], &[Range<usize>]); 3], eq: &SplitEq) -> [Grid; 3] {
    let tasks = tasks(&layers);
    let values = sum_tasks(tasks.len(), |i| {
        let (t, k) = tasks[i];
        let (values, ones) = layers[t];
        let groups = (TASK / GROUP) * k..(TASK * (k + 1)).min(values.len()).div_ceil(GROUP);
        let mut sums = [[Sum8::ZERO; 5]; 5];
        add_groups(values, ones, groups, 0, eq, &mut sums);
        let mut out = [[[F192::ZERO; 5]; 5]; 3];
        out[t] = reduce(sums);
        out
    });
    values.map(Grid::interpolate)
}

/// Binds the next two variables of the three layers to `r`, returning the folded rows and, given `eq`, the polynomials of the two rounds after.
///
/// A folded layer has a row for every stored block, the last one completed with ones.
pub(super) fn fold(
    layers: [(&[F192], &[Range<usize>]); 3],
    r: [F192; 2],
    eq: Option<&SplitEq>,
) -> ([Vec<F192>; 3], Option<[Grid; 3]>) {
    let lens = layers.map(|(values, _)| 4 * values.len().div_ceil(16));
    // SAFETY: the tasks below write every row before anything reads it.
    let mut outs: [Vec<F192>; 3] = lens.map(|len| unsafe { primitives::uninit_vec(len) });
    let dst = outs.each_mut().map(|out| SendPtr(out.as_mut_ptr()));
    let folded_ones = layers.map(|(_, ones)| coarsen(ones, 2));
    let [r0, r1] = r.map(F192x8::splat);

    let tasks = tasks(&layers);
    let values = sum_tasks(tasks.len(), |i| {
        let (t, k) = tasks[i];
        let (values, ones) = layers[t];
        let source = &values[TASK * k..(TASK * (k + 1)).min(values.len())];
        let rows = source.len().div_ceil(16);
        let mut stage = [F192::ONE; STAGE];

        let identity = |p: usize| {
            let first = TASK / 4 * k + 8 * p;
            covered(ones, first..first + 8)
        };
        let (pairs, tail) = source.as_chunks::<32>();
        for (p, (pair, out)) in pairs.iter().zip(stage.as_chunks_mut::<8>().0).enumerate() {
            if !identity(p) {
                fold_pair(pair, r0, r1).store(out);
            }
        }
        if !tail.is_empty() && !identity(pairs.len()) {
            let mut padded = [F192::ONE; 32];
            padded[..tail.len()].copy_from_slice(tail);
            let folded = fold_pair(&padded, r0, r1).to_array();
            let at = 8 * pairs.len();
            stage[at..4 * rows].copy_from_slice(&folded[..4 * rows - at]);
        }

        let mut sums = [[Sum8::ZERO; 5]; 5];
        if let Some(eq) = eq {
            let first = STAGE / GROUP * k;
            add_groups(
                &stage[..4 * rows],
                &folded_ones[t],
                0..rows.div_ceil(32),
                first,
                eq,
                &mut sums,
            );
        }

        // The next pass reads the output long after this one evicts it.
        debug_assert!(
            TASK / 4 * k + 4 * rows <= lens[t],
            "a task's window lies inside its tree's output"
        );
        // SAFETY: task (t, k) writes the window `TASK / 4 * k .. + 4 * rows` of tree t's output, which lies
        // inside its `lens[t]` elements because TASK is a multiple of 16; the (t, k) windows are disjoint and
        // together cover the output, and `outs` outlives the dispatch.
        unsafe { Stream::new().copy_uninit(dst[t].add(TASK / 4 * k), &stage[..4 * rows]) };
        let mut out = [[[F192::ZERO; 5]; 5]; 3];
        out[t] = reduce(sums);
        out
    });
    (outs, eq.map(|_| values.map(Grid::interpolate)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coefficients_invert_the_grid_points() {
        let poly = [3, 5, 7, 11, 13].map(|i| F192::new(i, 2 * i + 1, i * i));
        let at = |x: F192| poly.iter().rev().fold(F192::ZERO, |sum, &c| sum * x + c);
        let [a, b, c, d] = [F192::ZERO, F192::ONE, F192::Y, F192::Y + F192::ONE].map(at);
        assert_eq!(coefficients([a, b, c, d, poly[4]]), poly);
    }
}
