//! The opening's weight as terms, and the projection of lanes onto them.
//!
//! A claim's weight is a product over the bits of the stack index `y = l * 2^lane_vars + x`, each bit
//! carrying a [`Factor`]. Splitting `x` into a low part `x_lo` of [`LOW_VARS`] bits and a block index `h` gives
//!
//! ```text
//!     claim:  lambda * L(l) * gamma(h) * pi(x_lo)
//!     ring:   Phi(e(x) * s(l)),   e(x) = e_lo(x_lo) * e_hi(h)
//! ```
//!
//! `Phi` is F2-linear, so a ring claim is `sum_w bit_w(e(x)) * Phi(basis_w * s(l))`. The weight is then
//! `b(l, x) = sum_t A(l, t) * K_t(x)` over one term per claim and 128 per ring claim, and the table
//! `P(l, t) = sum_x lane(l, x) * K_t(x)` of a `K`-valued lane, the stack's or one derived from it, takes the lane's
//! place in level 0's fold rounds. Claims with the same `pi` share its dot with each block.

use primitives::bit_fold::BitFold;
use primitives::bits::bit_transpose_64bytes;
use primitives::field::{Acc8, F64, F64x8, F128, F128x8};

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{RingWeight, coordinate_basis};
use crate::tensor_algebra::{DEGREE_E, transpose_s_hat};
use crate::whir::InitialBasis;

/// Bits of a block's low part: a block is the 64 bit rows a ring claim folds at once.
pub(crate) const LOW_VARS: usize = 6;
const BLOCK: usize = 1 << LOW_VARS;
/// A block in lanes of eight.
const LANES: usize = BLOCK / 8;

/// A block's `E` values, eight to a lane.
fn in_lanes(v: &[F128]) -> [F128x8; LANES] {
    let v: &[F128; BLOCK] = v.try_into().expect("a block");
    core::array::from_fn(|i| F128x8::load(&v[8 * i..][..8]))
}

/// `sum_x pi[x] * words[x]` over a block, reduced once.
fn dot_block(pi: &[F128x8; LANES], words: &[F64]) -> F128 {
    let words: &[F64; BLOCK] = words.try_into().expect("a block");
    let mut acc = Acc8::ZERO;
    for (p, w) in pi.iter().zip(words.as_chunks::<8>().0) {
        acc += p.mul_base_unreduced(F64x8::from_array(w));
    }
    acc.sum()
}

/// What a weight does to one bit of the stack index.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Factor {
    /// The bit must take this value.
    Fixed(bool),
    /// `eq(p, bit)`.
    Eq(F128),
}

/// Appends `prod_i factors[i](bit i of x)` for every `x` to `out`.
fn extend_table(out: &mut Vec<F128>, factors: &[Factor]) {
    let start = out.len();
    out.push(F128::ONE);
    for &factor in factors {
        let len = out.len() - start;
        out.resize(start + 2 * len, F128::ZERO);
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
                    out[i] = F128::ZERO;
                }
                Factor::Fixed(false) => {}
            }
        }
    }
}

/// `prod_i factors[i](bit i of x)` for every `x`.
fn table(factors: &[Factor]) -> Vec<F128> {
    let mut out = Vec::new();
    extend_table(&mut out, factors);
    out
}

/// The factors on the low `bits` bits of the stack index of a claim at `point`, placed at `offset`.
fn point_factors(point: &[F128], offset: usize, bits: usize) -> Vec<Factor> {
    (0..bits)
        .map(|b| match point.get(b) {
            Some(&p) => Factor::Eq(p),
            None => Factor::Fixed((offset >> b) & 1 == 1),
        })
        .collect()
}

/// `sum_i a[i] * b[i]`, reduced once.
fn dot_ext(a: &[F128], b: &[F128]) -> F128 {
    let ((a8, a1), (b8, b1)) = (a.as_chunks::<8>(), b.as_chunks::<8>());
    let acc = a8.iter().zip(b8).fold(Acc8::ZERO, |acc, (a, b)| {
        acc + F128x8::from_array(a).mul_unreduced(F128x8::from_array(b))
    });
    a1.iter().zip(b1).fold(acc.sum(), |sum, (&a, &b)| sum + a * b)
}

/// A slot's run of equal blocks, which share their dots and their folds: a ring sums its fold once per run, weighted
/// by the run's mass, the sum of `e_hi` over its blocks.
struct Run {
    words: Option<[F64; BLOCK]>,
    /// The run's block as byte columns, once a ring has needed them.
    cols: Option<[[u8; BLOCK]; BLOCK / 8]>,
    dots: Vec<Option<F128>>,
    folds: Vec<Option<[F128x8; LANES]>>,
    masses: Vec<F128>,
    /// Each ring's sums of bit rows over the runs before.
    sigmas: Vec<[Acc8; LANES]>,
}

impl Run {
    fn new(n_patterns: usize, n_rings: usize) -> Self {
        Self {
            words: None,
            cols: None,
            dots: vec![None; n_patterns],
            folds: vec![None; n_rings],
            masses: vec![F128::ZERO; n_rings],
            sigmas: vec![[Acc8::ZERO; LANES]; n_rings],
        }
    }

    /// Starts a run at `words` unless they continue this one.
    fn feed(&mut self, words: &[F64]) {
        if self.words.as_ref().is_some_and(|w| w[..] == *words) {
            return;
        }
        self.flush();
        self.words = Some(words.try_into().expect("a block"));
        self.cols = None;
        self.dots.fill(None);
    }

    /// Adds each ring's fold of the run, weighted by its mass, to its sums.
    fn flush(&mut self) {
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
}

/// The claims that share one low factor list, its table `pi`, and the blocks where one of them is nonzero.
struct Pattern {
    factors: Vec<Factor>,
    claims: Vec<usize>,
    pi: [F128x8; LANES],
    active: Vec<bool>,
}

/// A ring claim's block structure and where its terms sit.
struct Ring {
    /// Folds the bit rows of a block against `e_lo`.
    fold: BitFold,
    /// `e_hi(h)` for every block.
    e_hi: Vec<F128>,
    point: Vec<F128>,
    /// Where `e` starts inside a lane block.
    x_offset: usize,
    /// The first of its 128 terms.
    first: usize,
}

/// The factored terms of the opening's weight.
pub(crate) struct Terms {
    /// Bits of a lane block.
    lane_vars: usize,
    /// `gamma(h)` of every claim, a block each.
    gamma: Vec<F128>,
    /// The blocks a claim's `gamma` is nonzero on.
    ranges: Vec<std::ops::Range<usize>>,
    patterns: Vec<Pattern>,
    rings: Vec<Ring>,
}

impl Terms {
    fn n_blocks(&self) -> usize {
        1 << (self.lane_vars - LOW_VARS)
    }

    /// `gamma(h)` of claim `c` for every block.
    fn gamma(&self, c: usize) -> &[F128] {
        &self.gamma[c * self.n_blocks()..][..self.n_blocks()]
    }

    pub(crate) fn n_terms(&self) -> usize {
        self.ranges.len() + DEGREE_E * self.rings.len()
    }

    /// Bits of a lane block.
    pub(crate) fn lane_vars(&self) -> usize {
        self.lane_vars
    }

    /// Projections of `n_lanes` lanes, `slots` rows of [`Self::n_terms`] each, onto the terms `live` marks, a range of
    /// blocks per task: `task(lane, blocks, feed)` hands `feed` a slot, a block and its words, for every block of the
    /// range and every slot it fills.
    pub(crate) fn project_rows(
        &self,
        n_lanes: usize,
        slots: usize,
        live: &[bool],
        task: impl Fn(usize, std::ops::Range<usize>, &mut dyn FnMut(usize, usize, &[F64])) + Sync,
    ) -> Vec<F128> {
        let (n_terms, n_blocks) = (self.n_terms(), self.n_blocks());
        let patterns: Vec<&Pattern> = self
            .patterns
            .iter()
            .filter(|pattern| pattern.claims.iter().any(|&c| live[c]))
            .collect();
        let rings: Vec<&Ring> = self
            .rings
            .iter()
            .filter(|ring| live[ring.first..ring.first + DEGREE_E].contains(&true))
            .collect();
        // Enough tasks to balance the pool.
        let per = n_blocks.div_ceil((8 * parallel::num_threads()).div_ceil(n_lanes.max(1)));
        let n_ranges = n_blocks.div_ceil(per);
        let parts = parallel::map_collect(n_lanes * n_ranges, |t| {
            let (lane, k) = (t / n_ranges, t % n_ranges);
            let blocks = k * per..((k + 1) * per).min(n_blocks);
            let mut out = vec![F128::ZERO; slots * n_terms];
            // Per slot: each pattern's dot with every block of the range, and the run the slot is in.
            let mut q = vec![F128::ZERO; slots * patterns.len() * blocks.len()];
            let mut runs: Vec<Run> = (0..slots).map(|_| Run::new(patterns.len(), rings.len())).collect();
            task(lane, blocks.clone(), &mut |slot, h, words| {
                let run = &mut runs[slot];
                run.feed(words);
                for (p, pattern) in patterns.iter().enumerate().filter(|(_, pattern)| pattern.active[h]) {
                    let dot = *run.dots[p].get_or_insert_with(|| dot_block(&pattern.pi, words));
                    q[(slot * patterns.len() + p) * blocks.len() + h - blocks.start] = dot;
                }
                for (r, ring) in rings.iter().enumerate() {
                    if ring.e_hi[h] == F128::ZERO {
                        continue;
                    }
                    run.masses[r] += ring.e_hi[h];
                    if run.folds[r].is_none() {
                        let cols = run.cols.get_or_insert_with(|| {
                            let mut cols = [[0u8; BLOCK]; BLOCK / 8];
                            for (col, group) in cols.iter_mut().zip(primitives::cast_slice::<F64, [u8; 64]>(words)) {
                                bit_transpose_64bytes(group, col);
                            }
                            cols
                        });
                        let mut folded = [F128::ZERO; BLOCK];
                        ring.fold.fold_columns(cols, &mut folded);
                        run.folds[r] = Some(in_lanes(&folded));
                    }
                }
            });
            for (slot, row) in out.chunks_exact_mut(n_terms).enumerate() {
                // `P(l, c) = sum_h gamma_c(h) * Q(h)` over the claim's blocks.
                for (p, pattern) in patterns.iter().enumerate() {
                    let q = &q[(slot * patterns.len() + p) * blocks.len()..][..blocks.len()];
                    for &c in &pattern.claims {
                        let range = self.ranges[c].start.max(blocks.start)..self.ranges[c].end.min(blocks.end);
                        if !range.is_empty() {
                            let q = &q[range.start - blocks.start..range.end - blocks.start];
                            row[c] = dot_ext(&self.gamma(c)[range], q);
                        }
                    }
                }
                let run = &mut runs[slot];
                run.flush();
                for (ring, sigma) in rings.iter().zip(&run.sigmas) {
                    let sigma: [[F128; 8]; LANES] = sigma.map(|s| s.reduce().to_array());
                    let sigma = sigma.as_flattened().try_into().expect("a block");
                    for (slot, k) in row[ring.first..].iter_mut().zip(transpose_s_hat(sigma)) {
                        *slot = F128::from(k);
                    }
                }
            }
            out
        });
        let mut rows = vec![F128::ZERO; n_lanes * slots * n_terms];
        for (t, part) in parts.iter().enumerate() {
            let rows = &mut rows[t / n_ranges * slots * n_terms..][..slots * n_terms];
            rows.iter_mut().zip(part).for_each(|(r, &p)| *r += p);
        }
        rows
    }

    /// The weight over one lane block after level 0's rounds, rebuilt from the term table's last row `a`:
    /// `b[h * 2^6 + x] = sum_claims a[c] * gamma_c(h) * pi_c(x) + sum_rings Phi'(e(x))`, where `Phi'` weighs the ring's
    /// coordinates by its 128 terms of `a`.
    pub(crate) fn lift(&self, a: &[F128]) -> Vec<F128> {
        let rings: Vec<_> = self
            .rings
            .iter()
            .map(|ring| {
                let vars = ring.point.len().min(self.lane_vars);
                let weights = *a[ring.first..]
                    .first_chunk::<DEGREE_E>()
                    .expect("a ring claim has one term per coordinate");
                let weight = RingWeight::new(weights, ring.point[..vars].to_vec()).fold();
                (weight, ring.x_offset, 1usize << vars)
            })
            .collect();
        let mut b = vec![F128::ZERO; 1 << self.lane_vars];
        parallel::chunks_mut(&mut b, BLOCK, |h, out| {
            for pattern in &self.patterns {
                let g: F128 = pattern.claims.iter().map(|&c| a[c] * self.gamma(c)[h]).sum();
                if g != F128::ZERO {
                    let g = F128x8::splat(g);
                    for (o, pi) in out.as_chunks_mut::<8>().0.iter_mut().zip(&pattern.pi) {
                        (F128x8::load(o) + *pi * g).store(o);
                    }
                }
            }
            for (weight, offset, len) in &rings {
                let (lo, hi) = ((h * BLOCK).max(*offset), ((h + 1) * BLOCK).min(offset + len));
                if lo < hi {
                    weight.add_chunk(lo - offset, &mut out[lo - h * BLOCK..hi - h * BLOCK]);
                }
            }
        });
        b
    }
}

/// The opening's weight as terms: its table `A`, a row for each of the `2^(log_n - lane_vars)` lanes, and the terms,
/// which project lanes onto them and lift a row of `A`.
///
/// `lane_vars` must be at least [`LOW_VARS`], and every claim must lie inside `2^log_n` words.
pub(super) fn initial_basis(
    log_n: usize,
    lane_vars: usize,
    claims: &[StackClaim],
    lambdas: &[F128],
    ring: &RingSwitchOpen,
    rings: &[RingWeight],
) -> InitialBasis {
    assert_eq!(claims.len(), lambdas.len());
    assert_eq!(rings.len(), ring.claims.len());
    assert!(lane_vars >= LOW_VARS, "a lane block holds at least one block");
    let lane_bits = log_n - lane_vars;
    let n_lanes = 1usize << lane_bits;

    // Claim terms: A(l, c) = lambda_c * L_c(l), and the pattern each claim's low factors fall in.
    let mut terms = Terms {
        lane_vars,
        gamma: Vec::new(),
        ranges: Vec::new(),
        patterns: Vec::new(),
        rings: Vec::new(),
    };
    // The claims' lane weights, then the rings', each `1 << lane_bits` long.
    let mut lanes: Vec<F128> = Vec::new();
    for (c, claim) in claims.iter().enumerate() {
        let StackClaim::Point { offset, low_point, .. } = claim;
        let factors = point_factors(low_point, *offset, log_n);
        let (low, rest) = factors.split_at(LOW_VARS);
        let (mid, lane) = rest.split_at(lane_vars - LOW_VARS);
        extend_table(&mut terms.gamma, mid);
        let at = lanes.len();
        extend_table(&mut lanes, lane);
        lanes[at..].iter_mut().for_each(|l| *l *= lambdas[c]);
        match terms.patterns.iter_mut().find(|p| p.factors == low) {
            Some(pattern) => pattern.claims.push(c),
            None => terms.patterns.push(Pattern {
                pi: in_lanes(&table(low)),
                factors: low.to_vec(),
                claims: vec![c],
                active: Vec::new(),
            }),
        }
    }
    let n_blocks = terms.n_blocks();
    for gamma in terms.gamma.chunks_exact(n_blocks) {
        let first = gamma.iter().position(|g| *g != F128::ZERO).unwrap_or(0);
        let end = gamma.iter().rposition(|g| *g != F128::ZERO).map_or(0, |h| h + 1);
        terms.ranges.push(first..end);
    }
    for pattern in &mut terms.patterns {
        pattern.active = (0..n_blocks)
            .map(|h| pattern.claims.iter().any(|&c| terms.ranges[c].contains(&h)))
            .collect();
    }
    for (i, weight) in rings.iter().enumerate() {
        let factors = point_factors(weight.point(), ring.offset, log_n);
        let (low, rest) = factors.split_at(LOW_VARS);
        let (mid, lane) = rest.split_at(lane_vars - LOW_VARS);
        terms.rings.push(Ring {
            fold: BitFold::new(&table(low)),
            e_hi: table(mid),
            point: weight.point().to_vec(),
            x_offset: ring.offset & ((1 << lane_vars) - 1),
            first: claims.len() + DEGREE_E * i,
        });
        extend_table(&mut lanes, lane);
    }

    let n_terms = terms.n_terms();
    let mut a = vec![F128::ZERO; n_lanes * n_terms];
    for (l, row) in a.chunks_exact_mut(n_terms).enumerate() {
        let weight_of = |t: usize| lanes[(t << lane_bits) + l];
        for (c, slot) in row[..claims.len()].iter_mut().enumerate() {
            *slot = weight_of(c);
        }
        for (i, (weight, ring)) in rings.iter().zip(&terms.rings).enumerate() {
            let s = weight_of(claims.len() + i);
            if s != F128::ZERO {
                for (w, slot) in row[ring.first..ring.first + DEGREE_E].iter_mut().enumerate() {
                    *slot = weight.apply(coordinate_basis(w) * s);
                }
            }
        }
    }
    InitialBasis { a, n_terms, terms }
}
