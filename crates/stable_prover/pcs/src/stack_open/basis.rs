//! The opening's weight as terms, and the projections of `K`-valued sequences onto them, which level 0's fold rounds
//! run on ([`crate::whir_lanes`]) so that the weight is never written out over the stack.
//!
//! A claim's weight is a product over the bits of the stack index `y = l * 2^lane_vars + x`, each bit carrying a
//! factor ([`eq_part`]). Splitting `x` into a low part `x_lo` of [`LOW_VARS`] bits and a block index `h` gives
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
use primitives::multilinear::eq_table_serial;

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{self, DEGREE_E, RingFold, transpose_s_hat};
use crate::whir_lanes::Sequences;

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

/// The weight of a claim at `point` placed at `offset` over the bits `bits` of the stack index, for every value of
/// those bits: the product of `eq(p_i, bit i)` over the point's coordinates and the indicator of the offset's bits
/// past them.
#[inline(never)]
fn eq_part(point: &[F128], offset: usize, bits: Range<usize>) -> Vec<F128> {
    let mid = point.len().clamp(bits.start, bits.end);
    let eq = eq_table_serial(point.get(bits.start..mid).unwrap_or_default());
    let mut out = vec![F128::ZERO; 1 << bits.len()];
    let at = (offset >> mid) & ((1 << (bits.end - mid)) - 1);
    out[at << (mid - bits.start)..][..eq.len()].copy_from_slice(&eq);
    out
}

/// A claim's `gamma(h)` over every block, nonzero on `range` only.
struct ClaimBlocks {
    gamma: Vec<F128>,
    range: Range<usize>,
}

/// The claims that share one low part `pi`, and the blocks where one of them is nonzero.
struct Pattern {
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
    pub(crate) lane_vars: usize,
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

    /// The projections of `n` items onto the terms, each item `s` sequences of `2^lane_vars` words read from
    /// `sequences`. A row of [`Self::n_terms`] per sequence, item by item.
    pub(crate) fn project(&self, n: usize, s: usize, sequences: &Sequences) -> Vec<F128> {
        let (row, n_blocks, n_sequences) = (self.n_terms(), self.n_blocks(), n * s);
        // Each sequence's blocks in ranges, enough tasks to balance the pool.
        let per = n_blocks.div_ceil((8 * parallel::num_threads()).div_ceil(n_sequences.max(1)));
        let n_ranges = n_blocks.div_ceil(per);
        let parts = parallel::map_collect(n_sequences * n_ranges, |task| {
            let (sequence, k) = (task / n_ranges, task % n_ranges);
            let range = k * per..((k + 1) * per).min(n_blocks);
            let mut projection = Projection::new(self, range.clone());
            let mut words = [F64::ZERO; BLOCK];
            for h in range {
                sequences.block(sequence / s, sequence % s, h, &mut words);
                projection.feed(h, &words);
            }
            projection.finish()
        });
        let mut rows = vec![F128::ZERO; n_sequences * row];
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

/// A ring's part of a [`Projection`]: its fold of the run's block once one is needed, its `e_hi` summed over the run
/// of equal blocks, and its folds weighted by those sums.
#[derive(Clone)]
struct RingRun {
    fold: Option<[F128x8; LANES]>,
    mass: F128,
    sigma: [Acc8; LANES],
}

/// One sequence's projections over a range of blocks.
struct Projection<'a> {
    terms: &'a Terms,
    blocks: Range<usize>,
    /// The block before: an equal block shares its dots and folds.
    last: Option<[F64; BLOCK]>,
    /// Each pattern's dot with every block of the range.
    q: Vec<F128>,
    rings: Vec<RingRun>,
}

impl<'a> Projection<'a> {
    fn new(terms: &'a Terms, blocks: Range<usize>) -> Self {
        let run = RingRun {
            fold: None,
            mass: F128::ZERO,
            sigma: [Acc8::ZERO; LANES],
        };
        Self {
            terms,
            last: None,
            q: vec![F128::ZERO; terms.patterns.len() * blocks.len()],
            rings: vec![run; terms.rings.len()],
            blocks,
        }
    }

    fn feed(&mut self, h: usize, words: &[F64; BLOCK]) {
        let same = self.last.as_ref() == Some(words);
        if !same {
            self.end_run();
            self.last = Some(*words);
        }
        let terms = self.terms;
        for (p, pattern) in terms.patterns.iter().enumerate() {
            if pattern.active[h] {
                let i = p * self.blocks.len() + h - self.blocks.start;
                // Block `h - 1` was fed just before.
                self.q[i] = if same && pattern.active[h - 1] {
                    self.q[i - 1]
                } else {
                    dot_block(&pattern.pi, words)
                };
            }
        }
        for (run, ring) in self.rings.iter_mut().zip(&terms.rings) {
            if ring.e_hi[h] != F128::ZERO {
                run.mass += ring.e_hi[h];
                run.fold.get_or_insert_with(|| ring.fold(words));
            }
        }
    }

    /// Adds each ring's fold of the run, weighted by its mass, to its sum.
    #[inline(never)]
    fn end_run(&mut self) {
        for run in &mut self.rings {
            if let Some(fold) = &run.fold {
                let mass = F128x8::splat(run.mass);
                for (s, f) in run.sigma.iter_mut().zip(fold) {
                    *s += f.mul_unreduced(mass);
                }
            }
            (run.fold, run.mass) = (None, F128::ZERO);
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
                    row[c] = primitives::field::dot(
                        &claim.gamma[range.clone()],
                        &q[range.start - blocks.start..range.end - blocks.start],
                    );
                }
            }
        }
        // A ring's 128 terms are the transpose of its 64 bit slices.
        for (ring, run) in terms.rings.iter().zip(&self.rings) {
            let slices: [[F128; 8]; LANES] = run.sigma.map(|s| s.reduce().to_array());
            let slices = slices.as_flattened().try_into().expect("a block");
            for (term, k) in row[ring.first..].iter_mut().zip(transpose_s_hat(slices)) {
                *term = F128::from(k);
            }
        }
        row
    }
}

/// The opening's weight as terms, and its table `A`: a row of [`Terms::n_terms`] for each of the
/// `2^(log_n - lane_vars)` lanes. `lambdas` are the ring claims' batching scalars, then the point claims', and `phi`
/// the ring switch's map by its images of the coordinate basis.
///
/// `lane_vars` must be at least [`LOW_VARS`], and every claim must lie inside `2^log_n` words.
pub(super) fn initial_basis(
    log_n: usize,
    lane_vars: usize,
    claims: &[&StackClaim],
    lambdas: &[F128],
    ring: &RingSwitchOpen,
    phi: &[F128; DEGREE_E],
) -> (Terms, Vec<F128>) {
    let (ring_lambdas, lambdas) = lambdas.split_at(ring.points.len());
    assert_eq!(claims.len(), lambdas.len());
    assert!(lane_vars >= LOW_VARS, "a lane block holds at least one block");
    let part = |claim: &StackClaim, bits| eq_part(&claim.low_point, claim.offset, bits);
    let mut terms = Terms {
        lane_vars,
        claims: parallel::map_collect(claims.len(), |c| {
            let gamma = part(claims[c], LOW_VARS..lane_vars);
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
    for (c, claim) in claims.iter().enumerate() {
        let pi = part(claim, 0..LOW_VARS);
        let same = |p: &&mut Pattern| p.pi.iter().zip(pi.as_chunks::<8>().0).all(|(p, v)| p.to_array() == *v);
        match terms.patterns.iter_mut().find(same) {
            Some(pattern) => pattern.claims.push(c),
            None => terms.patterns.push(Pattern {
                pi: in_lanes(pi.as_slice().try_into().expect("a block")),
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
    // `A(l, c) = lambda_c L_c(l)`, and a ring's `A(l, w) = Phi(b_w s(l))`.
    let n_terms = claims.len() + DEGREE_E * ring.points.len();
    let mut a = vec![F128::ZERO; n_terms << (log_n - lane_vars)];
    for (c, (claim, &lambda)) in claims.iter().zip(lambdas).enumerate() {
        for (l, lane) in part(claim, lane_vars..log_n).into_iter().enumerate() {
            a[l * n_terms + c] = lambda * lane;
        }
    }
    for (i, (point, &lambda)) in ring.points.iter().zip(ring_lambdas).enumerate() {
        let part = |bits| eq_part(point, ring.offset, bits);
        let first = claims.len() + DEGREE_E * i;
        for (l, lane) in part(lane_vars..log_n).into_iter().enumerate() {
            if lane != F128::ZERO {
                for (w, term) in a[l * n_terms + first..][..DEGREE_E].iter_mut().enumerate() {
                    *term = lambda * ring_switch::apply(phi, F128::from(1u128 << w) * lane);
                }
            }
        }
        terms.rings.push(Ring {
            fold: BitFold::new(&part(0..LOW_VARS)),
            e_hi: part(LOW_VARS..lane_vars),
            point: point.clone(),
            x_offset: ring.offset & ((1 << lane_vars) - 1),
            first,
        });
    }
    (terms, a)
}
