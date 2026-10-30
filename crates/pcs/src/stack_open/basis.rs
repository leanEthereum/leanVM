//! The opening's weight as terms, and the projection of the stack onto them.
//!
//! A claim's weight is a product over the bits of the stack index `y = l * 2^lane_vars + x`, each bit
//! carrying a [`Factor`]. Splitting `x` into a low part `x_lo` of `m = min(10, lane_vars)` bits and a
//! block index `h` gives
//!
//! ```text
//!     claim:  lambda * L(l) * gamma(h) * pi(x_lo)
//!     ring:   Phi(e(x) * s(l)),   e(x) = e_lo(x_lo) * e_hi(h)
//! ```
//!
//! `Phi` is F2-linear, so a ring claim is `sum_w bit_w(e(x)) * Phi(basis_w * s(l))`. The weight is then
//! `b(l, x) = sum_t A(l, t) * K_t(x)` over one term per claim and 192 per ring claim, and the table
//! `P(l, t) = sum_x stack(l, x) * K_t(x)` takes the stack's place in the lane rounds.

use primitives::bit_fold::BitFold;
use primitives::bits::bit_transpose_64bytes;
use primitives::field::{Acc8, F64, F192, F192x8, Weights8, dot_base, msg_lone8_ext, xor_into8};

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{RingWeight, coordinate_basis};
use crate::tensor_algebra::{DEGREE_E, transpose_s_hat};
use crate::whir::{InitialBasis, LaneLift, LiftBlock, adjacent_dots};

/// Bits of a block's low part.
pub(super) const LOW_VARS: usize = 10;
/// Packing width: the bit rows of a block of words.
const ROWS: usize = 64;

/// `g * t`, elementwise.
fn scale8(t: &[F192; 8], g: F192) -> [F192; 8] {
    (F192x8::from_array(t) * F192x8::splat(g)).to_array()
}

/// What a weight does to one bit of the stack index.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Factor {
    /// The bit must take this value.
    Fixed(bool),
    /// `eq(p, bit)`.
    Eq(F192),
}

/// Appends `prod_i factors[i](bit i of x)` for every `x` to `out`.
fn extend_table(out: &mut Vec<F192>, factors: &[Factor]) {
    let start = out.len();
    out.reserve(1 << factors.len());
    out.push(F192::ONE);
    for &factor in factors {
        let len = out.len() - start;
        out.resize(start + 2 * len, F192::ZERO);
        for i in start..start + len {
            let v = out[i];
            match factor {
                Factor::Eq(p) => {
                    let high = v * p;
                    out[i + len] = high;
                    out[i] = v + high;
                }
                Factor::Fixed(true) => {
                    out[i + len] = v;
                    out[i] = F192::ZERO;
                }
                Factor::Fixed(false) => {}
            }
        }
    }
}

/// `prod_i factors[i](bit i of x)` for every `x`.
fn table(factors: &[Factor]) -> Vec<F192> {
    let mut out = Vec::new();
    extend_table(&mut out, factors);
    out
}

/// A claim's factors on the low `bits` bits of the stack index.
fn claim_factors(claim: &StackClaim, bits: usize) -> Vec<Factor> {
    let StackClaim::Point { offset, low_point, .. } = claim;
    ring_factors(low_point, *offset, bits)
}

/// A ring claim's factors on the low `bits` bits of the stack index.
fn ring_factors(point: &[F192], offset: usize, bits: usize) -> Vec<Factor> {
    (0..bits)
        .map(|b| match point.get(b) {
            Some(&p) => Factor::Eq(p),
            None => Factor::Fixed((offset >> b) & 1 == 1),
        })
        .collect()
}

/// The claims that share one low factor list `pi`, and `pi`'s form.
struct Pattern {
    factors: Vec<Factor>,
    claims: Vec<usize>,
    low: Low,
    /// The blocks where some claim of the pattern is nonzero.
    active: Vec<bool>,
}

/// The table of `pi`: in vectors of eight for the lift, packed for the dot against a block.
struct Low {
    table: Vec<F192x8>,
    packed: Vec<Weights8>,
}

impl Low {
    fn new(factors: &[Factor]) -> Self {
        let table = table(factors);
        let packed = table.as_chunks::<8>().0.iter().map(Weights8::new).collect();
        let table = table.as_chunks::<8>().0.iter().map(F192x8::from_array).collect();
        Low { table, packed }
    }

    /// `sum_x block[x] * pi(x)`.
    fn dot(&self, block: &[F64]) -> F192 {
        dot_base(&self.packed, block).reduce()
    }
}

/// A ring claim's block structure and where its terms sit.
struct Ring {
    /// Folds a bit row of a block against `e_lo`.
    fold: BitFold,
    /// `e_hi(h)` for every block.
    e_hi: Vec<F192>,
    point: Vec<F192>,
    /// Where `e` starts inside a lane block.
    x_offset: usize,
    /// The first of its 192 terms.
    first: usize,
}

/// The factored terms of the opening's weight.
struct Terms {
    /// Bits of a lane block.
    lane_vars: usize,
    /// Bits of a block's low part.
    low_vars: usize,
    /// `gamma(h)` of every claim, `1 << (lane_vars - low_vars)` blocks each.
    gamma: Vec<F192>,
    /// The blocks a claim's `gamma` is nonzero on, widened to whole vectors.
    ranges: Vec<std::ops::Range<usize>>,
    patterns: Vec<Pattern>,
    rings: Vec<Ring>,
}

impl Terms {
    fn n_claims(&self) -> usize {
        self.ranges.len()
    }

    /// `gamma(h)` of claim `c` for every block.
    fn gamma(&self, c: usize) -> &[F192] {
        let n_blocks = 1 << (self.lane_vars - self.low_vars);
        &self.gamma[c * n_blocks..][..n_blocks]
    }

    fn n_terms(&self) -> usize {
        self.n_claims() + DEGREE_E * self.rings.len()
    }

    /// `P(l, .)` for the lane's words.
    ///
    /// The lane is swept in runs of `RUN` blocks, one pass per table, so a pattern's packed weights or a ring's
    /// fold matrices stay in L1 across the run while the run's words stay in L2.
    fn project_lane<const CHUNKS: usize>(&self, lane: &[F64], row: &mut [F192]) {
        const RUN: usize = 32;
        let n_blocks = lane.len() >> self.low_vars;
        let block = |h: usize| &lane[h << self.low_vars..][..1 << self.low_vars];
        let mut q = vec![F192::ZERO; n_blocks * self.patterns.len()];
        let mut sigmas = vec![F192::ZERO; ROWS * self.rings.len()];
        let mut cols = [[0u8; ROWS]; CHUNKS];
        for start in (0..n_blocks).step_by(RUN) {
            let blocks = start..(start + RUN).min(n_blocks);
            for (pattern, q) in self.patterns.iter().zip(q.chunks_exact_mut(n_blocks)) {
                for h in blocks.clone().filter(|&h| pattern.active[h]) {
                    q[h] = pattern.low.dot(block(h));
                }
            }
            for h in blocks {
                let mut transposed = false;
                for (ring, sigma) in self.rings.iter().zip(sigmas.as_chunks_mut::<ROWS>().0) {
                    let e_hi = ring.e_hi[h];
                    if e_hi == F192::ZERO {
                        continue;
                    }
                    if !transposed {
                        for (col, group) in cols.iter_mut().zip(block(h).as_chunks::<8>().0) {
                            bit_transpose_64bytes(&primitives::cast_slice::<F64, [u8; 64]>(group)[0], col);
                        }
                        transposed = true;
                    }
                    let mut folded = [F192::ZERO; ROWS];
                    ring.fold.fold_columns(&cols, &mut folded);
                    for (s, v) in sigma.as_chunks_mut::<8>().0.iter_mut().zip(folded.as_chunks::<8>().0) {
                        xor_into8(s, &scale8(v, e_hi));
                    }
                }
            }
        }
        // `P(l, c) = sum_h gamma_c(h) * Q(h)` over the claim's blocks.
        for (p, pattern) in self.patterns.iter().enumerate() {
            let q = &q[p * n_blocks..(p + 1) * n_blocks];
            for &c in &pattern.claims {
                let range = self.ranges[c].clone();
                let (gamma, q) = (&self.gamma(c)[range.clone()], &q[range]);
                let ((g8, g_r), (q8, q_r)) = (gamma.as_chunks::<8>(), q.as_chunks::<8>());
                let sum = g8.iter().zip(q8).fold(Acc8::ZERO, |mut acc, (g, q)| {
                    acc ^= msg_lone8_ext(g, q);
                    acc
                });
                row[c] = g_r.iter().zip(q_r).fold(sum.reduce(), |sum, (&g, &q)| sum + g * q);
            }
        }
        for (ring, sigma) in self.rings.iter().zip(sigmas.as_chunks::<ROWS>().0.iter()) {
            for (slot, k) in row[ring.first..].iter_mut().zip(transpose_s_hat(sigma)) {
                *slot = F192::from(k);
            }
        }
    }

    /// `P` over the stack.
    fn project(&self, stack: &[F64]) -> Vec<F192> {
        let (block, n_terms) = (1usize << self.lane_vars, self.n_terms());
        let mut p = vec![F192::ZERO; stack.len() / block * n_terms];
        parallel::chunks_mut(&mut p, n_terms, |l, row| {
            let lane = &stack[l * block..(l + 1) * block];
            match self.low_vars {
                6 => self.project_lane::<8>(lane, row),
                7 => self.project_lane::<16>(lane, row),
                8 => self.project_lane::<32>(lane, row),
                9 => self.project_lane::<64>(lane, row),
                _ => self.project_lane::<128>(lane, row),
            }
        });
        p
    }
}

impl LaneLift for Terms {
    /// `b[h * 2^m + x] = sum_claims A[c] * gamma_c(h) * pi_c(x) + sum_rings Phi'(e(x))`, where
    /// `Phi'` weighs the ring's coordinates by its 192 terms of `a`, and the message of `f` against `b`.
    ///
    /// The setup is each pattern's weight on each block, `sum_c a[c] * gamma_c(h)` over its claims, and the
    /// ring weights. A block is built in the caller's buffer, and the dense patterns share one reduction per vector.
    fn blocks<'a>(&'a self, a: &[F192]) -> LiftBlock<'a> {
        let block = 1usize << self.low_vars;
        let rings: Vec<_> = self
            .rings
            .iter()
            .map(|ring| {
                let vars = ring.point.len().min(self.lane_vars);
                let weights = a[ring.first..ring.first + DEGREE_E].to_vec();
                let weight = RingWeight::new(weights, ring.point[..vars].to_vec()).fold();
                (weight, ring.x_offset, 1usize << vars)
            })
            .collect();
        let n_patterns = self.patterns.len();
        // SAFETY: the fill writes every element before it reads any.
        let gs = unsafe {
            primitives::filled_vec((1 << (self.lane_vars - self.low_vars)) * n_patterns, |gs| {
                parallel::chunks_mut(gs, n_patterns.max(1), |h, row| {
                    for (g, pattern) in row.iter_mut().zip(&self.patterns) {
                        *g = pattern
                            .claims
                            .iter()
                            .fold(F192::ZERO, |sum, &c| sum + a[c] * self.gamma(c)[h]);
                    }
                });
            })
        };
        Box::new(move |h, f, out| {
            let live = || {
                self.patterns
                    .iter()
                    .zip(&gs[h * n_patterns..][..n_patterns])
                    .filter(|(_, g)| **g != F192::ZERO)
            };
            for (k, o) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                let products = live().map(|(pattern, &g)| pattern.low.table[k].mul_unreduced(F192x8::splat(g)));
                *o = products
                    .reduce(|acc, p| acc ^ p)
                    .map_or([F192::ZERO; 8], |acc| acc.reduce_lanes().to_array());
            }
            for (weight, offset, len) in &rings {
                let (lo, hi) = ((h * block).max(*offset), ((h + 1) * block).min(offset + len));
                if lo < hi {
                    weight.add_chunk(lo - offset, &mut out[lo - h * block..hi - h * block]);
                }
            }
            let (u_0, u_2, _) = adjacent_dots::<false>(f, out);
            (u_0, u_2)
        })
    }
}

/// The opening's weight as terms: its table `P` against the stack, its table `A`, and the lift of `A`'s last row.
///
/// Every claim must lie inside the stack, and `lane_vars` must be at least 6.
pub(super) fn project(
    stack: &[F64],
    lane_vars: usize,
    claims: &[StackClaim],
    lambdas: &[F192],
    ring: &RingSwitchOpen,
    rings: &[RingWeight],
) -> InitialBasis {
    assert_eq!(claims.len(), lambdas.len());
    assert_eq!(rings.len(), ring.claims.len());
    assert!(
        lane_vars >= ROWS.ilog2() as usize,
        "a lane block holds at least one row of bits"
    );
    let block = 1usize << lane_vars;
    let n_lanes = stack.len() / block;
    assert_eq!(stack.len(), n_lanes * block, "the stack is whole lane blocks");
    let (low_vars, lane_bits) = (
        lane_vars.min(LOW_VARS),
        (usize::BITS - (n_lanes - 1).leading_zeros()) as usize,
    );
    let bits = lane_vars + lane_bits;

    // Claim terms: A(l, c) = lambda_c * L_c(l), and the pattern each claim's low factors fall in.
    let mut terms = Terms {
        lane_vars,
        low_vars,
        gamma: Vec::new(),
        ranges: Vec::new(),
        patterns: Vec::new(),
        rings: Vec::new(),
    };
    // The claims' lane weights, then the rings', each `1 << lane_bits` long.
    let mut lanes: Vec<F192> = Vec::new();
    for (c, claim) in claims.iter().enumerate() {
        let factors = claim_factors(claim, bits);
        let (low, rest) = factors.split_at(low_vars);
        let (mid, lane) = rest.split_at(lane_vars - low_vars);
        extend_table(&mut terms.gamma, mid);
        let at = lanes.len();
        extend_table(&mut lanes, lane);
        lanes[at..].iter_mut().for_each(|l| *l *= lambdas[c]);
        match terms.patterns.iter_mut().find(|p| p.factors == low) {
            Some(pattern) => pattern.claims.push(c),
            None => terms.patterns.push(Pattern {
                low: Low::new(low),
                factors: low.to_vec(),
                claims: vec![c],
                active: Vec::new(),
            }),
        }
    }
    let n_blocks = 1usize << (lane_vars - low_vars);
    for gamma in terms.gamma.chunks_exact(n_blocks) {
        let nonzero = |h: &usize| gamma[*h] != F192::ZERO;
        let first = (0..n_blocks).find(nonzero).unwrap_or(0);
        let end = (0..n_blocks).rfind(nonzero).map_or(0, |h| h + 1);
        terms.ranges.push(first / 8 * 8..end.next_multiple_of(8).min(n_blocks));
    }
    let gamma = |c: usize| &terms.gamma[c * n_blocks..][..n_blocks];
    for pattern in &mut terms.patterns {
        pattern.active = (0..n_blocks)
            .map(|h| pattern.claims.iter().any(|&c| gamma(c)[h] != F192::ZERO))
            .collect();
    }
    for (i, weight) in rings.iter().enumerate() {
        let factors = ring_factors(weight.point(), ring.offset, bits);
        let (low, rest) = factors.split_at(low_vars);
        let (mid, lane) = rest.split_at(lane_vars - low_vars);
        terms.rings.push(Ring {
            fold: BitFold::new(&table(low)),
            e_hi: table(mid),
            point: weight.point().to_vec(),
            x_offset: ring.offset & (block - 1),
            first: claims.len() + DEGREE_E * i,
        });
        extend_table(&mut lanes, lane);
    }

    let n_terms = terms.n_terms();
    let mut a = vec![F192::ZERO; n_lanes * n_terms];
    for (l, row) in a.chunks_exact_mut(n_terms).enumerate() {
        let weight_of = |t: usize| lanes[(t << lane_bits) + l];
        for (c, slot) in row[..claims.len()].iter_mut().enumerate() {
            *slot = weight_of(c);
        }
        for (i, (weight, ring)) in rings.iter().zip(&terms.rings).enumerate() {
            let s = weight_of(claims.len() + i);
            if s != F192::ZERO {
                for (w, slot) in row[ring.first..ring.first + DEGREE_E].iter_mut().enumerate() {
                    *slot = weight.apply(coordinate_basis(w) * s);
                }
            }
        }
    }
    let p = terms.project(stack);
    InitialBasis {
        p,
        a,
        block: n_terms,
        lift_len: 1 << low_vars,
        lift: Box::new(terms),
    }
}
