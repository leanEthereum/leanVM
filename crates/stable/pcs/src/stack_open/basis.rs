//! The opening's weight as terms, and the projection of lanes onto them.
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
//! `b(l, x) = sum_t A(l, t) * K_t(x)` over one term per claim and 128 per ring claim, and the table
//! `P(l, t) = sum_x lane(l, x) * K_t(x)` of a `K`-valued lane, the stack's or one derived from it, takes the lane's
//! place in level 0's fold rounds.

use primitives::bit_fold::BitFold;
use primitives::bits::bit_transpose_64bytes;
use primitives::field::{Acc8, F64, F128, F128x8, Weights8, dot_base, msg_lone8_ext, xor_into8};

use super::{RingSwitchOpen, StackClaim};
use crate::ring_switch::{RingWeight, coordinate_basis};
use crate::tensor_algebra::{DEGREE_E, transpose_s_hat};
use crate::whir::InitialBasis;

/// Bits of a block's low part.
pub(super) const LOW_VARS: usize = 10;
/// Packing width: the bit rows of a block of words.
const ROWS: usize = 64;

/// `g * t`, elementwise.
fn scale8(t: &[F128; 8], g: F128) -> [F128; 8] {
    (F128x8::from_array(t) * F128x8::splat(g)).to_array()
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
    out.reserve(1 << factors.len());
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
    table: Vec<F128x8>,
    packed: Vec<Weights8>,
}

impl Low {
    fn new(factors: &[Factor]) -> Self {
        let table = table(factors);
        let packed = table.as_chunks::<8>().0.iter().map(Weights8::new).collect();
        let table = table.as_chunks::<8>().0.iter().map(F128x8::from_array).collect();
        Low { table, packed }
    }

    /// `sum_x block[x] * pi(x)`.
    fn dot(&self, block: &[F64]) -> F128 {
        dot_base(&self.packed, block).reduce()
    }
}

/// Adds each ring's pending fold of an ended run of equal blocks into its `sigma`, weighted by the run's mass.
fn flush(folds: &mut [Option<[F128; ROWS]>], masses: &mut [F128], sigmas: &mut [F128]) {
    for ((fold, mass), sigma) in folds.iter_mut().zip(masses).zip(sigmas.as_chunks_mut::<ROWS>().0) {
        if let Some(folded) = fold.take() {
            for (s, v) in sigma.as_chunks_mut::<8>().0.iter_mut().zip(folded.as_chunks::<8>().0) {
                xor_into8(s, &scale8(v, *mass));
            }
        }
        *mass = F128::ZERO;
    }
}

/// For each block of `2^LOW_VARS` words of `stack`, whether it equals the block before it.
fn equal_blocks(stack: &[F64]) -> Vec<bool> {
    let blocks = primitives::cast_slice::<F64, u64>(stack)
        .as_chunks::<{ 1 << LOW_VARS }>()
        .0;
    parallel::map_collect(blocks.len(), |b| b > 0 && blocks[b] == blocks[b - 1])
}

/// A ring claim's block structure and where its terms sit.
struct Ring {
    /// Folds a bit row of a block against `e_lo`.
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
    /// Bits of a block's low part.
    low_vars: usize,
    /// `gamma(h)` of every claim, `1 << (lane_vars - low_vars)` blocks each.
    gamma: Vec<F128>,
    /// The blocks a claim's `gamma` is nonzero on, widened to whole vectors.
    ranges: Vec<std::ops::Range<usize>>,
    patterns: Vec<Pattern>,
    rings: Vec<Ring>,
    /// Tags the stack's blocks of `2^low_vars` words that equal their predecessor, or is empty.
    repeats: Vec<bool>,
}

impl Terms {
    fn n_claims(&self) -> usize {
        self.ranges.len()
    }

    /// `gamma(h)` of claim `c` for every block.
    fn gamma(&self, c: usize) -> &[F128] {
        let n_blocks = 1 << (self.lane_vars - self.low_vars);
        &self.gamma[c * n_blocks..][..n_blocks]
    }

    pub(crate) fn n_terms(&self) -> usize {
        self.n_claims() + DEGREE_E * self.rings.len()
    }

    /// The patterns and rings some term `live` marks needs.
    fn live<'a>(&'a self, live: &[bool]) -> Live<'a> {
        Live {
            patterns: self
                .patterns
                .iter()
                .filter(|pattern| pattern.claims.iter().any(|&c| live[c]))
                .collect(),
            rings: self
                .rings
                .iter()
                .filter(|ring| live[ring.first..ring.first + DEGREE_E].contains(&true))
                .collect(),
        }
    }

    /// Projections of `n_lanes` lanes, `slots` rows of [`Self::n_terms`] each, for the terms `live` marks, a range of
    /// blocks per task: `task(lane, blocks, feed)` hands `feed` a slot, the first block of some words of the range,
    /// the words and their repeat tags, in order of blocks per slot, [`SWEEP`] blocks or more at a time.
    ///
    /// A repeat tag says a block equals the block fed before it to its slot, and means nothing on the slot's first
    /// block. Tags may be empty.
    pub(crate) fn project_rows(
        &self,
        n_lanes: usize,
        slots: usize,
        live: &[bool],
        task: impl Fn(usize, std::ops::Range<usize>, &mut dyn FnMut(usize, usize, &[F64], &[bool])) + Sync,
    ) -> Vec<F128> {
        let n_terms = self.n_terms();
        let n_blocks = 1usize << (self.lane_vars - self.low_vars);
        let live = self.live(live);
        // Enough tasks to balance the pool, each at least one sweep of blocks where the lane allows.
        let want = (8 * parallel::num_threads()).div_ceil(n_lanes.max(1));
        let per = (n_blocks / want.next_power_of_two()).max(SWEEP.min(n_blocks));
        let n_ranges = n_blocks.div_ceil(per);
        let parts = parallel::map_collect(n_lanes * n_ranges, |t| {
            let (lane, k) = (t / n_ranges, t % n_ranges);
            let blocks = k * per..((k + 1) * per).min(n_blocks);
            let mut projections: Vec<Option<Projection>> = (0..slots).map(|_| None).collect();
            task(lane, blocks.clone(), &mut |slot, start, words, repeats| {
                projections[slot]
                    .get_or_insert_with(|| Projection::new(&live, blocks.clone()))
                    .feed(self, &live, start, words, repeats);
            });
            let mut out = vec![F128::ZERO; slots * n_terms];
            for (projection, row) in projections.into_iter().zip(out.chunks_exact_mut(n_terms)) {
                if let Some(projection) = projection {
                    projection.finish(self, &live, row);
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

    /// The repeat tags of the blocks `blocks` of lane `l`.
    pub(crate) fn lane_repeats(&self, l: usize, blocks: std::ops::Range<usize>) -> &[bool] {
        let n_blocks = 1usize << (self.lane_vars - self.low_vars);
        self.repeats
            .get(l * n_blocks + blocks.start..l * n_blocks + blocks.end)
            .unwrap_or(&[])
    }

    /// Bits of a block of the projection.
    pub(crate) fn low_vars(&self) -> usize {
        self.low_vars
    }

    /// Bits of a lane block.
    pub(crate) fn lane_vars(&self) -> usize {
        self.lane_vars
    }

    /// The weight over one lane block after level 0's rounds, rebuilt from the term table's last row `a`.
    ///
    /// `b[h * 2^m + x] = sum_claims A[c] * gamma_c(h) * pi_c(x) + sum_rings Phi'(e(x))`, where
    /// `Phi'` weighs the ring's coordinates by its 128 terms of `a`.
    ///
    /// The setup is each pattern's weight on each block, `sum_c a[c] * gamma_c(h)` over its claims, and the
    /// ring weights. A block is built at a time, and the dense patterns share one reduction per vector.
    pub(crate) fn lift(&self, a: &[F128]) -> Vec<F128> {
        let block = 1usize << self.low_vars;
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
        let n_patterns = self.patterns.len();
        // SAFETY: the fill writes every element before it reads any.
        let gs = unsafe {
            primitives::filled_vec((1 << (self.lane_vars - self.low_vars)) * n_patterns, |gs| {
                parallel::chunks_mut(gs, n_patterns.max(1), |h, row| {
                    for (g, pattern) in row.iter_mut().zip(&self.patterns) {
                        *g = pattern.claims.iter().map(|&c| a[c] * self.gamma(c)[h]).sum();
                    }
                });
            })
        };
        // SAFETY: the fill writes every element before it reads any.
        unsafe {
            primitives::filled_vec(1 << self.lane_vars, |b| {
                parallel::chunks_mut(b, block, |h, out| {
                    let live = || {
                        self.patterns
                            .iter()
                            .zip(&gs[h * n_patterns..][..n_patterns])
                            .filter(|(_, g)| **g != F128::ZERO)
                    };
                    for (k, o) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                        let products = live().map(|(pattern, &g)| pattern.low.table[k].mul_unreduced(F128x8::splat(g)));
                        *o = products
                            .reduce(|acc, p| acc ^ p)
                            .map_or([F128::ZERO; 8], |acc| acc.reduce_lanes().to_array());
                    }
                    for (weight, offset, len) in &rings {
                        let (lo, hi) = ((h * block).max(*offset), ((h + 1) * block).min(offset + len));
                        if lo < hi {
                            weight.add_chunk(lo - offset, &mut out[lo - h * block..hi - h * block]);
                        }
                    }
                });
            })
        }
    }
}

/// Blocks a projection sweeps at a time, one pass per table, so a pattern's packed weights or a ring's fold matrices
/// stay in L1 across the sweep while its words stay in L2.
pub(crate) const SWEEP: usize = 32;

/// The patterns and rings a projection computes.
struct Live<'a> {
    patterns: Vec<&'a Pattern>,
    rings: Vec<&'a Ring>,
}

/// `P(l, .)` of one lane over a range of its blocks, fed the blocks in order.
///
/// A run of equal blocks shares its dots and its folds, a fold weighted by the run's `e_hi` mass, so its words are
/// read once per run.
struct Projection {
    blocks: std::ops::Range<usize>,
    /// Each pattern's dot with every block of the range.
    q: Vec<F128>,
    sigmas: Vec<F128>,
    dots: Vec<Option<F128>>,
    folds: Vec<Option<[F128; ROWS]>>,
    masses: Vec<F128>,
}

impl Projection {
    fn new(live: &Live, blocks: std::ops::Range<usize>) -> Self {
        Self {
            q: vec![F128::ZERO; blocks.len() * live.patterns.len()],
            sigmas: vec![F128::ZERO; ROWS * live.rings.len()],
            dots: vec![None; live.patterns.len()],
            folds: vec![None; live.rings.len()],
            masses: vec![F128::ZERO; live.rings.len()],
            blocks,
        }
    }

    /// Feeds `words`, which start at block `start` of the lane, with their repeat tags.
    fn feed(&mut self, terms: &Terms, live: &Live, start: usize, words: &[F64], repeats: &[bool]) {
        match terms.low_vars {
            6 => self.sweep::<8>(terms, live, start, words, repeats),
            7 => self.sweep::<16>(terms, live, start, words, repeats),
            8 => self.sweep::<32>(terms, live, start, words, repeats),
            9 => self.sweep::<64>(terms, live, start, words, repeats),
            _ => self.sweep::<128>(terms, live, start, words, repeats),
        }
    }

    fn sweep<const CHUNKS: usize>(
        &mut self,
        terms: &Terms,
        live: &Live,
        start: usize,
        words: &[F64],
        repeats: &[bool],
    ) {
        let low = terms.low_vars;
        let n_blocks = words.len() >> low;
        debug_assert!(self.blocks.start <= start && start + n_blocks <= self.blocks.end);
        let block = |h: usize| &words[h << low..][..1 << low];
        let repeat = |h: usize| repeats.get(h) == Some(&true);
        let range = self.blocks.len();
        let mut cols = [[0u8; ROWS]; CHUNKS];
        for first in (0..n_blocks).step_by(SWEEP) {
            let blocks = first..(first + SWEEP).min(n_blocks);
            for (p, (pattern, dot)) in live.patterns.iter().zip(&mut self.dots).enumerate() {
                for h in blocks.clone() {
                    if !repeat(h) {
                        *dot = None;
                    }
                    if pattern.active[start + h] {
                        self.q[p * range + start + h - self.blocks.start] =
                            *dot.get_or_insert_with(|| pattern.low.dot(block(h)));
                    }
                }
            }
            for h in blocks {
                if !repeat(h) {
                    flush(&mut self.folds, &mut self.masses, &mut self.sigmas);
                }
                let mut transposed = false;
                for ((ring, fold), mass) in live.rings.iter().zip(&mut self.folds).zip(&mut self.masses) {
                    let e_hi = ring.e_hi[start + h];
                    if e_hi == F128::ZERO {
                        continue;
                    }
                    *mass += e_hi;
                    fold.get_or_insert_with(|| {
                        if !transposed {
                            for (col, group) in cols.iter_mut().zip(block(h).as_chunks::<8>().0) {
                                bit_transpose_64bytes(&primitives::cast_slice::<F64, [u8; 64]>(group)[0], col);
                            }
                            transposed = true;
                        }
                        let mut folded = [F128::ZERO; ROWS];
                        ring.fold.fold_columns(&cols, &mut folded);
                        folded
                    });
                }
            }
        }
    }

    /// Adds the projection to `row`.
    fn finish(mut self, terms: &Terms, live: &Live, row: &mut [F128]) {
        flush(&mut self.folds, &mut self.masses, &mut self.sigmas);
        // `P(l, c) = sum_h gamma_c(h) * Q(h)` over the claim's blocks.
        let mine = &self.blocks;
        for (pattern, q) in live.patterns.iter().zip(self.q.chunks_exact(mine.len())) {
            for &c in &pattern.claims {
                let range = terms.ranges[c].start.max(mine.start)..terms.ranges[c].end.min(mine.end);
                if range.is_empty() {
                    continue;
                }
                let gamma = &terms.gamma(c)[range.clone()];
                let q = &q[range.start - mine.start..range.end - mine.start];
                let ((g8, g_r), (q8, q_r)) = (gamma.as_chunks::<8>(), q.as_chunks::<8>());
                let sum = g8.iter().zip(q8).fold(Acc8::ZERO, |mut acc, (g, q)| {
                    acc ^= msg_lone8_ext(g, q);
                    acc
                });
                row[c] += g_r.iter().zip(q_r).fold(sum.reduce(), |sum, (&g, &q)| sum + g * q);
            }
        }
        for (ring, sigma) in live.rings.iter().zip(self.sigmas.as_chunks::<ROWS>().0.iter()) {
            for (slot, k) in row[ring.first..].iter_mut().zip(transpose_s_hat(sigma)) {
                *slot += F128::from(k);
            }
        }
    }
}

/// The opening's weight as terms: its table `A`, a row for each of the `2^(log_n - lane_vars)` lanes, and the terms,
/// which project lanes onto them and lift a row of `A`.
///
/// `stack` is the committed lanes, `lane_vars` must be at least 6, and every claim must lie inside `2^log_n` words.
pub(super) fn initial_basis(
    stack: &[F64],
    log_n: usize,
    lane_vars: usize,
    claims: &[StackClaim],
    lambdas: &[F128],
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
    assert!(stack.len().is_multiple_of(block), "the stack is whole lane blocks");
    let (low_vars, lane_bits, bits) = (lane_vars.min(LOW_VARS), log_n - lane_vars, log_n);
    let n_lanes = 1usize << lane_bits;

    // Claim terms: A(l, c) = lambda_c * L_c(l), and the pattern each claim's low factors fall in.
    let mut terms = Terms {
        lane_vars,
        low_vars,
        gamma: Vec::new(),
        ranges: Vec::new(),
        patterns: Vec::new(),
        rings: Vec::new(),
        // Padding repeats blocks, which the stack's projection skips.
        repeats: if low_vars == LOW_VARS {
            tracing::info_span!("Repeats").in_scope(|| equal_blocks(stack))
        } else {
            Vec::new()
        },
    };
    // The claims' lane weights, then the rings', each `1 << lane_bits` long.
    let mut lanes: Vec<F128> = Vec::new();
    for (c, claim) in claims.iter().enumerate() {
        let StackClaim::Point { offset, low_point, .. } = claim;
        let factors = point_factors(low_point, *offset, bits);
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
        let nonzero = |h: &usize| gamma[*h] != F128::ZERO;
        let first = (0..n_blocks).find(nonzero).unwrap_or(0);
        let end = (0..n_blocks).rfind(nonzero).map_or(0, |h| h + 1);
        terms.ranges.push(first / 8 * 8..end.next_multiple_of(8).min(n_blocks));
    }
    let gamma = |c: usize| &terms.gamma[c * n_blocks..][..n_blocks];
    for pattern in &mut terms.patterns {
        pattern.active = (0..n_blocks)
            .map(|h| pattern.claims.iter().any(|&c| gamma(c)[h] != F128::ZERO))
            .collect();
    }
    for (i, weight) in rings.iter().enumerate() {
        let factors = point_factors(weight.point(), ring.offset, bits);
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
