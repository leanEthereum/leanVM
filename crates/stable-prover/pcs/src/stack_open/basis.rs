//! The opening's weight as terms, and the projections of `K`-valued sequences onto them, which level 0's fold rounds
//! run on ([`crate::whir_lanes`]) so that the weight is never written out over the stack.
//!
//! A claim's weight is a product over the bits of the stack index `y = l * 2^lane_vars + x`, each bit carrying a
//! [`Factor`]. Splitting `x` into a low part `x_lo` of [`LOW_VARS`] bits and a block index `h` gives
//!
//! ```text
//!     claim:  lambda * L(l) * gamma(h) * pi(x_lo)
//!     ring:   Phi(e(x) * s(l)),   e(x) = e_lo(x_lo) * e_hi(h)
//! ```
//!
//! `Phi` is F_2-linear, so a ring claim is `sum_w bit_w(e(x)) * Phi(b_w * s(l))` over the coordinate basis `b_w` of
//! `E`. The weight is then `W(l, x) = sum_t A(l, t) * K_t(x)` over one term per claim and 128 per ring claim, and level
//! 0's rounds take a lane's projections `P(t) = sum_x lane(x) * K_t(x)` in place of the lane.
//!
//! Two savings keep the projections cheap: the claims with one `pi` (a [`Pattern`]) share its dot with each block, and
//! a block equal to the one before it shares that block's dots and ring folds.

use std::ops::Range;

use primitives::bit_fold::BitFold;
use primitives::field::lanes::transpose_bits;
use primitives::field::{Acc8, F64, F64x8, F128, F128x8};

use super::StackClaim;
use crate::ring_switch::{DEGREE_E, RingFold, RingWeight, transpose_s_hat};

/// Bits of a block's low part: a block is the 64 bit rows a ring claim folds at once.
pub(crate) const LOW_VARS: usize = 6;
const BLOCK: usize = 1 << LOW_VARS;
/// A block in lanes of eight.
const LANES: usize = BLOCK / 8;

/// A block's `E` values, eight to a lane.
fn in_lanes(v: &[F128; BLOCK]) -> [F128x8; LANES] {
    core::array::from_fn(|i| F128x8::load(&v[8 * i..][..8]))
}

/// `sum_x pi[x] * words[x]` over a block, reduced once.
fn dot_block(pi: &[F128x8; LANES], words: &[F64; BLOCK]) -> F128 {
    let mut acc = Acc8::ZERO;
    for (p, w) in pi.iter().zip(words.as_chunks::<8>().0) {
        acc += p.mul_base_unreduced(F64x8::from_array(w));
    }
    acc.sum()
}

/// What a weight does to one bit of the stack index: its factor where the bit is 0, and where it is 1.
type Factor = [F128; 2];

/// `prod_i factors[i](bit i of x)` for every `x`.
fn table(factors: &[Factor]) -> Vec<F128> {
    let mut out = vec![F128::ONE];
    for &[lo, hi] in factors {
        out = out.iter().map(|&v| v * lo).chain(out.iter().map(|&v| v * hi)).collect();
    }
    out
}

/// The factors on the low `bits` bits of the stack index of a claim at `point`, placed at `offset`: `eq(p, bit)` on
/// the point's coordinates, then the offset's bits.
fn point_factors(point: &[F128], offset: usize, bits: usize) -> Vec<Factor> {
    (0..bits)
        .map(|b| match point.get(b) {
            Some(&p) => [F128::ONE + p, p],
            None if (offset >> b) & 1 == 1 => [F128::ZERO, F128::ONE],
            None => [F128::ONE, F128::ZERO],
        })
        .collect()
}

/// A claim's `gamma(h)` over every block, nonzero on `range` only.
struct ClaimBlocks {
    gamma: Vec<F128>,
    range: Range<usize>,
}

/// The claims that share one low factor list, its table `pi`, and the blocks where one of them is nonzero.
struct Pattern {
    factors: Vec<Factor>,
    pi: [F128x8; LANES],
    claims: Vec<usize>,
    active: Vec<bool>,
}

/// A ring claim's block structure and where its terms sit.
struct Ring {
    /// Folds a block's 64 bit slices against `e_lo`.
    fold: BitFold,
    /// `e_hi(h)` for every block.
    e_hi: Vec<F128>,
    point: Vec<F128>,
    /// Where `e` starts inside a lane block.
    x_offset: usize,
    /// The first of its 128 terms.
    first: usize,
}

impl Ring {
    /// `sum_(x_lo) e_lo(x_lo) * bit_i(words[x_lo])` for every bit `i`: the block's bit slices at `e_lo`.
    fn fold(&self, words: &[F64; BLOCK]) -> [F128x8; LANES] {
        // Byte `n` of column `j` holds bit `n` of words `8j..8j + 8`.
        let cols: [[u64; 8]; BLOCK / 8] =
            core::array::from_fn(|j| transpose_bits(core::array::from_fn(|k| words[8 * j + k].0)));
        let cols: &[[u8; BLOCK]; BLOCK / 8] = primitives::cast_slice(&cols)
            .try_into()
            .expect("a column per eight words");
        let mut folded = [F128::ZERO; BLOCK];
        self.fold.fold_columns(cols, &mut folded);
        in_lanes(&folded)
    }
}

/// The factored terms of the opening's weight.
pub(crate) struct Terms {
    /// Bits of a lane block.
    lane_vars: usize,
    claims: Vec<ClaimBlocks>,
    patterns: Vec<Pattern>,
    rings: Vec<Ring>,
}

impl Terms {
    fn n_blocks(&self) -> usize {
        1 << (self.lane_vars - LOW_VARS)
    }

    pub(crate) fn n_terms(&self) -> usize {
        self.claims.len() + DEGREE_E * self.rings.len()
    }

    /// Bits of a lane block.
    pub(crate) fn lane_vars(&self) -> usize {
        self.lane_vars
    }

    /// The projections of `n` items onto the terms, each item `S` sequences of `2^lane_vars` words: `blocks(i, h, out)`
    /// writes block `h` of each of item `i`'s sequences. A row of [`Self::n_terms`] per sequence, item by item.
    pub(crate) fn project<const S: usize>(
        &self,
        n: usize,
        blocks: impl Fn(usize, usize, &mut [[F64; BLOCK]; S]) + Sync,
    ) -> Vec<F128> {
        let (row, n_blocks) = (S * self.n_terms(), self.n_blocks());
        // Each item's blocks in ranges, enough tasks to balance the pool.
        let per = n_blocks.div_ceil((8 * parallel::num_threads()).div_ceil(n.max(1)));
        let n_ranges = n_blocks.div_ceil(per);
        let parts = parallel::map_collect(n * n_ranges, |task| {
            let (item, k) = (task / n_ranges, task % n_ranges);
            let range = k * per..((k + 1) * per).min(n_blocks);
            let mut sequences: [Projection; S] = core::array::from_fn(|_| Projection::new(self, range.clone()));
            let mut words = [[F64::ZERO; BLOCK]; S];
            for h in range {
                blocks(item, h, &mut words);
                for (sequence, words) in sequences.iter_mut().zip(&words) {
                    sequence.feed(h, words);
                }
            }
            sequences.map(Projection::finish).concat()
        });
        let mut rows = vec![F128::ZERO; n * row];
        for (task, part) in parts.iter().enumerate() {
            let rows = &mut rows[task / n_ranges * row..][..row];
            rows.iter_mut().zip(part).for_each(|(r, &p)| *r += p);
        }
        rows
    }

    /// The weight over one lane block after level 0's rounds, from the last row `a` of the table:
    /// `W[h * 2^6 + x] = sum_claims a[c] * gamma_c(h) * pi_c(x) + sum_rings Phi'(e(x))`, where `Phi'` weighs the ring's
    /// coordinates by its 128 terms of `a`.
    pub(crate) fn lift(&self, a: &[F128]) -> Vec<F128> {
        let rings: Vec<_> = self
            .rings
            .iter()
            .map(|ring| {
                let vars = ring.point.len().min(self.lane_vars);
                let phi = *a[ring.first..]
                    .first_chunk()
                    .expect("a ring claim has one term per coordinate");
                (RingFold::new(phi, &ring.point[..vars]), ring.x_offset, 1usize << vars)
            })
            .collect();
        let mut w = parallel::filled(1 << self.lane_vars, F128::ZERO);
        parallel::chunks_mut(&mut w, BLOCK, |h, out| {
            for pattern in &self.patterns {
                let g: F128 = pattern
                    .claims
                    .iter()
                    .filter(|&&c| self.claims[c].range.contains(&h))
                    .map(|&c| a[c] * self.claims[c].gamma[h])
                    .sum();
                if g != F128::ZERO {
                    let g = F128x8::splat(g);
                    for (o, pi) in out.as_chunks_mut::<8>().0.iter_mut().zip(&pattern.pi) {
                        (F128x8::load(o) + *pi * g).store(o);
                    }
                }
            }
            for (fold, offset, len) in &rings {
                let (lo, hi) = ((h * BLOCK).max(*offset), ((h + 1) * BLOCK).min(offset + len));
                if lo < hi {
                    fold.add_chunk(lo - offset, &mut out[lo - h * BLOCK..hi - h * BLOCK]);
                }
            }
        });
        w
    }
}

/// One sequence's projections over a range of blocks.
struct Projection<'a> {
    terms: &'a Terms,
    blocks: Range<usize>,
    /// The block before, and its dot with each pattern and fold by each ring once one is needed: an equal block
    /// shares them.
    last: Option<[F64; BLOCK]>,
    dots: Vec<Option<F128>>,
    folds: Vec<Option<[F128x8; LANES]>>,
    /// Each pattern's dot with every block of the range.
    q: Vec<F128>,
    /// Each ring's `e_hi` summed over the run of equal blocks, and its folds weighted by those sums.
    masses: Vec<F128>,
    sigmas: Vec<[Acc8; LANES]>,
}

impl<'a> Projection<'a> {
    fn new(terms: &'a Terms, blocks: Range<usize>) -> Self {
        let (n_patterns, n_rings) = (terms.patterns.len(), terms.rings.len());
        Self {
            terms,
            last: None,
            dots: vec![None; n_patterns],
            folds: vec![None; n_rings],
            q: vec![F128::ZERO; n_patterns * blocks.len()],
            masses: vec![F128::ZERO; n_rings],
            sigmas: vec![[Acc8::ZERO; LANES]; n_rings],
            blocks,
        }
    }

    fn feed(&mut self, h: usize, words: &[F64; BLOCK]) {
        if self.last.as_ref() != Some(words) {
            self.end_run();
            self.last = Some(*words);
            self.dots.fill(None);
        }
        let terms = self.terms;
        for (p, pattern) in terms.patterns.iter().enumerate() {
            if pattern.active[h] {
                let dot = *self.dots[p].get_or_insert_with(|| dot_block(&pattern.pi, words));
                self.q[p * self.blocks.len() + h - self.blocks.start] = dot;
            }
        }
        for (r, ring) in terms.rings.iter().enumerate() {
            if ring.e_hi[h] != F128::ZERO {
                self.masses[r] += ring.e_hi[h];
                self.folds[r].get_or_insert_with(|| ring.fold(words));
            }
        }
    }

    /// Adds each ring's fold of the run, weighted by its mass, to its sum.
    fn end_run(&mut self) {
        for ((fold, mass), sigma) in self.folds.iter_mut().zip(&mut self.masses).zip(&mut self.sigmas) {
            if let Some(fold) = fold.take() {
                let mass = F128x8::splat(*mass);
                sigma
                    .iter_mut()
                    .zip(fold)
                    .for_each(|(s, f)| *s += f.mul_unreduced(mass));
            }
            *mass = F128::ZERO;
        }
    }

    /// The sequence's row of projections over the range.
    fn finish(mut self) -> Vec<F128> {
        self.end_run();
        let (terms, blocks) = (self.terms, &self.blocks);
        let mut row = vec![F128::ZERO; terms.n_terms()];
        // `P(c) = sum_h gamma_c(h) * Q(h)` over the claim's blocks, `Q(h)` its pattern's dot with block `h`.
        for (q, pattern) in self.q.chunks_exact(blocks.len()).zip(&terms.patterns) {
            for &c in &pattern.claims {
                let claim = &terms.claims[c];
                let range = claim.range.start.max(blocks.start)..claim.range.end.min(blocks.end);
                if !range.is_empty() {
                    row[c] = crate::whir::dot(
                        &claim.gamma[range.clone()],
                        &q[range.start - blocks.start..range.end - blocks.start],
                    );
                }
            }
        }
        // A ring's 128 terms are the transpose of its 64 bit slices.
        for (ring, sigma) in terms.rings.iter().zip(&self.sigmas) {
            let slices: [[F128; 8]; LANES] = sigma.map(|s| s.reduce().to_array());
            let slices = slices.as_flattened().try_into().expect("a block");
            for (term, k) in row[ring.first..].iter_mut().zip(transpose_s_hat(slices)) {
                *term = F128::from(k);
            }
        }
        row
    }
}

/// The opening's weight as terms, and its table `A`: a row of [`Terms::n_terms`] for each of the
/// `2^(log_n - lane_vars)` lanes.
///
/// `lane_vars` must be at least [`LOW_VARS`], and every claim must lie inside `2^log_n` words. The ring claims lie at
/// `ring_offset`.
pub(super) fn initial_basis(
    log_n: usize,
    lane_vars: usize,
    claims: &[StackClaim],
    lambdas: &[F128],
    ring_offset: usize,
    rings: &[RingWeight],
) -> (Terms, Vec<F128>) {
    assert_eq!(claims.len(), lambdas.len());
    assert!(lane_vars >= LOW_VARS, "a lane block holds at least one block");
    let factors: Vec<Vec<Factor>> = claims
        .iter()
        .map(|StackClaim { offset, low_point }| point_factors(low_point, *offset, log_n))
        .collect();
    let mut terms = Terms {
        lane_vars,
        claims: parallel::map_collect(claims.len(), |c| {
            let gamma = table(&factors[c][LOW_VARS..lane_vars]);
            let first = gamma.iter().position(|g| *g != F128::ZERO).unwrap_or(0);
            let end = gamma.iter().rposition(|g| *g != F128::ZERO).map_or(0, |h| h + 1);
            ClaimBlocks {
                gamma,
                range: first..end,
            }
        }),
        patterns: Vec::new(),
        rings: Vec::new(),
    };
    for (c, factors) in factors.iter().enumerate() {
        let low = &factors[..LOW_VARS];
        match terms.patterns.iter_mut().find(|p| p.factors == low) {
            Some(pattern) => pattern.claims.push(c),
            None => terms.patterns.push(Pattern {
                pi: in_lanes(table(low).as_slice().try_into().expect("a block")),
                factors: low.to_vec(),
                claims: vec![c],
                active: Vec::new(),
            }),
        }
    }
    for pattern in &mut terms.patterns {
        pattern.active = vec![false; 1 << (lane_vars - LOW_VARS)];
        for &c in &pattern.claims {
            pattern.active[terms.claims[c].range.clone()].fill(true);
        }
    }
    let mut ring_lanes = Vec::new();
    for (i, weight) in rings.iter().enumerate() {
        let factors = point_factors(&weight.point, ring_offset, log_n);
        terms.rings.push(Ring {
            fold: BitFold::new(&table(&factors[..LOW_VARS])),
            e_hi: table(&factors[LOW_VARS..lane_vars]),
            point: weight.point.clone(),
            x_offset: ring_offset & ((1 << lane_vars) - 1),
            first: claims.len() + DEGREE_E * i,
        });
        ring_lanes.push(table(&factors[lane_vars..]));
    }

    // `A(l, c) = lambda_c L_c(l)`, and a ring's `A(l, w) = Phi(b_w s(l))`.
    let claim_lanes: Vec<Vec<F128>> = factors.iter().map(|factors| table(&factors[lane_vars..])).collect();
    let n_terms = terms.n_terms();
    let mut a = vec![F128::ZERO; n_terms << (log_n - lane_vars)];
    for (l, row) in a.chunks_exact_mut(n_terms).enumerate() {
        for ((term, lanes), &lambda) in row.iter_mut().zip(&claim_lanes).zip(lambdas) {
            *term = lambda * lanes[l];
        }
        for ((ring, weight), lanes) in terms.rings.iter().zip(rings).zip(&ring_lanes) {
            if lanes[l] != F128::ZERO {
                for (w, term) in row[ring.first..][..DEGREE_E].iter_mut().enumerate() {
                    *term = weight.apply(F128::from(1u128 << w) * lanes[l]);
                }
            }
        }
    }
    (terms, a)
}
