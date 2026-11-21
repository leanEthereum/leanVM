//! Two sumcheck rounds per pass. Four rows make bilinear children in the next two
//! variables; their product's bivariate coefficient grid gives both messages.
//! Folds retain eight blocks in transposed form, using four-lane halves on AVX2.

use super::vertical::{F128x8, covered};
use super::{N_BUS_TREES, SplitEq, coarsen};
use primitives::field::F128;
use primitives::stream::Stream;
use std::ops::Range;

cfg_select! {
    target_feature = "avx512f" => {
        use primitives::field::x8::{F128x8 as Lane, Sum8 as Sum};
    }
    _ => {
        use primitives::field::x4::{F128x4 as Lane, Sum4 as Sum};
    }
}

/// `q[4b + c]` lane `p` is child `c` of row `4p + b`.
pub(super) type Quad = [F128x8; 16];
const TASK: usize = 32;
const PARALLEL: usize = 64;

#[inline(always)]
fn load_quad(values: &[F128], i: usize) -> Quad {
    match values.get(128 * i..128 * i + 128) {
        Some(run) => F128x8::load_blocks(run.try_into().unwrap()),
        None => {
            let mut padded = [F128::ONE; 128];
            let tail = &values[(128 * i).min(values.len())..];
            padded[..tail.len()].copy_from_slice(tail);
            F128x8::load_blocks(&padded)
        }
    }
}

#[inline(always)]
fn fold_quad(q: &Quad, r: [F128x8; 2]) -> [F128x8; 4] {
    std::array::from_fn(|c| {
        let low = q[c] + r[0] * (q[c] + q[4 + c]);
        let high = q[8 + c] + r[0] * (q[8 + c] + q[12 + c]);
        low + r[1] * (low + high)
    })
}

#[inline(always)]
fn regroup(rows: [[F128x8; 4]; 4]) -> Quad {
    let mut q = [F128x8::splat(F128::ZERO); 16];
    for c in 0..4 {
        let (even01, odd01) = F128x8::even_odd(rows[0][c], rows[1][c]);
        let (even23, odd23) = F128x8::even_odd(rows[2][c], rows[3][c]);
        (q[c], q[8 + c]) = F128x8::even_odd(even01, even23);
        (q[4 + c], q[12 + c]) = F128x8::even_odd(odd01, odd23);
    }
    q
}

trait Xor: Copy {
    fn xor(self, rhs: Self) -> Self;
}

impl Xor for F128 {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Xor for Lane {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl<T: Xor, const N: usize> Xor for [T; N] {
    #[inline(always)]
    fn xor(self, rhs: Self) -> Self {
        std::array::from_fn(|i| self[i].xor(rhs[i]))
    }
}

#[inline(always)]
fn product2<T: Xor, P: Xor>([u0, u1]: [T; 2], [w0, w1]: [T; 2], mul: impl Fn(T, T) -> P) -> [P; 3] {
    let (low, high, sum) = (mul(u0, w0), mul(u1, w1), mul(u0.xor(u1), w0.xor(w1)));
    [low, sum.xor(low).xor(high), high]
}

/// Six Karatsuba products; their linear recombination is deferred until after summing.
#[inline(always)]
fn terms3<T: Xor, P>(u: [T; 3], w: [T; 3], mul: impl Fn(T, T) -> P) -> [P; 6] {
    let sum = |i: usize, j: usize| mul(u[i].xor(u[j]), w[i].xor(w[j]));
    [
        mul(u[0], w[0]),
        mul(u[1], w[1]),
        mul(u[2], w[2]),
        sum(0, 1),
        sum(0, 2),
        sum(1, 2),
    ]
}

fn combine3<P: Xor>([z0, z1, z2, s01, s02, s12]: [P; 6]) -> [P; 5] {
    [
        z0,
        s01.xor(z0).xor(z1),
        s02.xor(z0).xor(z2).xor(z1),
        s12.xor(z1).xor(z2),
        z2,
    ]
}

type Sums = [[Sum; 6]; 6];

#[inline(always)]
fn add_lanes(sums: &mut Sums, q: [Lane; 16], weight: Lane) {
    // Child c's coefficients: [[1, Y1], [Y2, Y1 Y2]].
    let child = |c: usize| {
        let y1 = q[c] + q[4 + c];
        [[q[c], y1], [q[c] + q[8 + c], y1 + q[8 + c] + q[12 + c]]]
    };
    let [[a, b], [c, d]] = child(0);
    let first = [[a * weight, b * weight], [c * weight, d * weight]];
    let biquadratic = |a, b| product2(a, b, |u, w| product2(u, w, |x: Lane, y| x * y));
    let (left, right) = (biquadratic(first, child(1)), biquadratic(child(2), child(3)));
    for (sums, (u, w)) in sums.iter_mut().zip(terms3(left, right, |u, w| (u, w))) {
        for (sum, (x, y)) in sums.iter_mut().zip(terms3(u, w, |x, y| (x, y))) {
            *sum ^= x.mul_sum(y);
        }
    }
}

#[inline(always)]
fn add_quad(sums: &mut Sums, q: Quad, eq: &SplitEq, i: usize) {
    let shift = eq.lo_bits - 3;
    let weight = eq.lo8[i & ((1 << shift) - 1)] * F128x8::splat(eq.hi[i >> shift]);
    cfg_select! {
        target_feature = "avx512f" => add_lanes(sums, q, weight),
        _ => {
            let (q, weight) = (q.map(F128x8::halves), weight.halves());
            add_lanes(sums, q.map(|lanes| lanes[0]), weight[0]);
            add_lanes(sums, q.map(|lanes| lanes[1]), weight[1]);
        }
    }
}

/// Coefficients indexed [Y2 power][Y1 power], with Y1 bound first.
pub(super) struct Grid([[F128; 5]; 5]);

impl Grid {
    fn new(sums: [[F128; 6]; 6]) -> Self {
        Self(combine3(sums.map(combine3)))
    }

    pub(super) fn first_round(&self, p: F128) -> [F128; 4] {
        let [low, upper @ ..] = &self.0;
        std::array::from_fn(|i| low[i + 1] + p * upper.iter().fold(F128::ZERO, |sum, row| sum + row[i + 1]))
    }

    pub(super) fn second_round(&self, r: F128) -> [F128; 4] {
        std::array::from_fn(|i| self.0[i + 1].iter().rev().fold(F128::ZERO, |sum, &c| sum * r + c))
    }
}

pub(super) enum Data<'a> {
    Rows(&'a [F128]),
    Quads(&'a [Quad]),
}

pub(super) struct Input<'a> {
    pub(super) data: Data<'a>,
    pub(super) ones: &'a [Range<usize>],
}

impl Input<'_> {
    fn len(&self) -> usize {
        match self.data {
            Data::Rows(values) => values.len().div_ceil(128),
            Data::Quads(quads) => quads.len(),
        }
    }

    #[inline(always)]
    fn get(&self, i: usize) -> Option<Quad> {
        if i >= self.len() || covered(self.ones, 32 * i..32 * i + 32) {
            return None;
        }
        Some(match self.data {
            Data::Rows(values) => load_quad(values, i),
            Data::Quads(quads) => quads[i],
        })
    }
}

fn grids(
    lens: [usize; N_BUS_TREES],
    task: impl Fn(usize, Range<usize>) -> [[F128; 6]; 6] + Sync,
) -> [Grid; N_BUS_TREES] {
    let tasks: Vec<(usize, usize)> = (0..N_BUS_TREES)
        .flat_map(|t| (0..lens[t]).step_by(TASK).map(move |first| (t, first)))
        .collect();
    let zero = [[[F128::ZERO; 6]; 6]; N_BUS_TREES];
    let run = |i: usize| {
        let (t, first) = tasks[i];
        let mut sums = zero;
        sums[t] = task(t, first..(first + TASK).min(lens[t]));
        sums
    };
    let add = |a: [[[F128; 6]; 6]; N_BUS_TREES], b| a.xor(b);
    let sums = if lens.iter().sum::<usize>() > PARALLEL {
        parallel::map_reduce(tasks.len(), || zero, run, add)
    } else {
        (0..tasks.len()).map(run).fold(zero, add)
    };
    sums.map(Grid::new)
}

pub(super) fn grid(inputs: [Input; N_BUS_TREES], eq: &SplitEq) -> [Grid; N_BUS_TREES] {
    grids(inputs.each_ref().map(Input::len), |t, quads| {
        let mut sums = [[Sum::ZERO; 6]; 6];
        for i in quads {
            if let Some(q) = inputs[t].get(i) {
                add_quad(&mut sums, q, eq, i);
            }
        }
        sums.map(|row| row.map(Sum::reduce))
    })
}

pub(super) fn fold(
    inputs: [Input; N_BUS_TREES],
    r: [F128; 2],
    eq: Option<&SplitEq>,
    outs: [&mut Vec<Quad>; N_BUS_TREES],
) -> Option<[Grid; N_BUS_TREES]> {
    let n_out = inputs.each_ref().map(|input| input.len().div_ceil(4));
    let mut outs = outs;
    let dst: [parallel::SendPtr<Quad>; N_BUS_TREES] = std::array::from_fn(|t| {
        let out = &mut *outs[t];
        if out.capacity() < n_out[t] {
            *out = Vec::new();
            // SAFETY: each non-identity quad is written before it is read; identity quads are never read.
            *out = unsafe { primitives::uninit_vec(n_out[t]) };
        } else {
            // SAFETY: same invariant; Quad is plain data.
            unsafe { out.set_len(n_out[t]) };
        }
        parallel::SendPtr(out.as_mut_ptr())
    });
    let r = r.map(F128x8::splat);
    let ones = inputs.each_ref().map(|input| coarsen(input.ones, 2));
    let identity = [F128x8::splat(F128::ONE); 4];
    let grids = grids(n_out, |t, quads| {
        let stream = Stream::new();
        let mut sums = [[Sum::ZERO; 6]; 6];
        for o in quads {
            // Identity blocks affect only the constant term, which neither message reads.
            if covered(&ones[t], 32 * o..32 * o + 32) {
                continue;
            }
            let rows = std::array::from_fn(|k| inputs[t].get(4 * o + k).map_or(identity, |q| fold_quad(&q, r)));
            let quad = regroup(rows);
            if let Some(eq) = eq {
                add_quad(&mut sums, quad, eq, o);
            }
            // SAFETY: tasks own disjoint quads, read only by the next pass.
            unsafe { stream.copy(dst[t].slice(o, 1), std::slice::from_ref(&quad)) };
        }
        sums.map(|row| row.map(Sum::reduce))
    });
    eq.map(|_| grids)
}

pub(super) fn to_rows(quads: &[Quad], ones: &[Range<usize>], rows: usize) -> Vec<F128> {
    let mut values = vec![F128::ONE; 128 * quads.len()];
    for (i, (quad, out)) in quads.iter().zip(values.as_chunks_mut::<128>().0).enumerate() {
        if covered(ones, 32 * i..32 * i + 32) {
            continue;
        }
        for (j, lanes) in quad.iter().enumerate() {
            for (p, e) in lanes.to_array().into_iter().enumerate() {
                out[16 * p + j] = e;
            }
        }
    }
    values.truncate(4 * rows);
    values
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::{QuaternaryLayerState, fold_pair, tests::element};

    #[test]
    fn paired_rounds_match_single_rounds() {
        let c1 = |[sum, c2, c3, c4]: [F128; 4]| [sum + c2 + c3 + c4, c2, c3, c4];
        for width in [1usize << 10, 1 << 13] {
            let ones = [3..9, 64..200, 256..width - 24];
            let tree = |n: usize| {
                let mut values: Vec<F128> = (0..n).map(|i| element(i, n)).collect();
                for row in ones.iter().flat_map(Clone::clone).filter(|&row| 4 * row < n) {
                    values[4 * row..(4 * row + 4).min(n)].fill(F128::ONE);
                }
                let mut tree = QuaternaryLayerState::new(values, width);
                tree.ones = ones.to_vec();
                tree
            };
            for lens in [[4 * width, 4 * width - 5, 4 * width / 3 + 7], [33, 4 * width - 1, 1000]] {
                let mut reference = lens.map(tree);
                let mut paired = lens.map(tree);
                let point: Vec<F128> = (0..width.ilog2()).map(|i| F128::new(3 + u64::from(i), 2)).collect();
                let eq = |from: usize| SplitEq::new(&point[from..]);
                let mut messages = reference.each_ref().map(|tree| tree.round_message_scalar(&eq(1)));
                let inputs = paired.each_ref().map(QuaternaryLayerState::paired_input);
                let mut grids = Some(grid(inputs, &eq(2)));
                let mut j = 0;
                while let Some(grid) = grids {
                    let r = [F128::new(j as u64 + 5, 19), F128::new(j as u64 + 7, 1)];
                    for (g, &m) in grid.iter().zip(&messages) {
                        assert_eq!(
                            g.first_round(point[j + 1]),
                            c1(m),
                            "width={width}, lens={lens:?}, j={j}"
                        );
                    }
                    messages = reference
                        .each_mut()
                        .map(|tree| tree.fold_and_message_scalar(r[0], &eq(j + 2)));
                    for (g, &m) in grid.iter().zip(&messages) {
                        assert_eq!(g.second_round(r[0]), c1(m), "width={width}, lens={lens:?}, j={j}");
                    }
                    messages = reference
                        .each_mut()
                        .map(|tree| tree.fold_and_message_scalar(r[1], &eq(j + 3)));
                    let next = (width >> (j + 2) >= 32).then(|| eq(j + 4));
                    grids = fold_pair(&mut paired, r, next.as_ref());
                    j += 2;
                }
                for (p, r) in paired.iter_mut().zip(&mut reference) {
                    p.leave_quads();
                    assert_eq!(p.round_message_scalar(&eq(j + 1)), r.round_message_scalar(&eq(j + 1)));
                    while r.logical_rows > 1 {
                        let challenge = F128::new(r.logical_rows as u64, 9);
                        r.fold_scalar(challenge);
                        p.fold_scalar(challenge);
                    }
                    assert_eq!(p.children(), r.children(), "width={width}, lens={lens:?}");
                }
            }
        }
    }
}
