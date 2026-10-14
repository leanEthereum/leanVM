//! The stacked opening's weight, which the prover never stores.
//!
//! - The first pass reads it one aligned chunk at a time, each chunk filled on demand.
//! - The first fold reads it folded over its lane bits, in closed form:
//!
//! ```text
//!     point claim:  the lanes' eq weights add into one seed of its eq table
//!     ring claim:   sum_l e_l * Phi(c_l * u) is one GF(2)-linear map of u
//! ```

use crate::ring_switch::{DeferredWeight, RingFamily};
use crate::stack::{StackClaim, Statement};
use crate::whir::anchor::eq_prefix;
use crate::whir::{INITIAL_BASIS_CHUNK, InitialWeight};
use primitives::bit_fold::F192Map;
use primitives::field::F192;
use primitives::multilinear::{eq_table, eq_table_seeded, fill_eq_table_uninit};
use std::mem::MaybeUninit;
use std::ops::Range;

/// The most lanes one fold binds at once: the first pass's four lane rounds.
const MAX_FOLDED_LANES: usize = 16;

/// A point claim's weight, its eq table split at one fill chunk.
///
/// - The high table is built once.
/// - The low table is built per chunk, from one seed of the high table.
struct PointWeight<'a> {
    /// The slice's first word.
    offset: usize,
    /// The slice's past-the-end word.
    end: usize,
    /// The frozen low coordinates' value, zero for a plain claim.
    slot: usize,
    /// The distance between two weighted words.
    stride: usize,
    /// The coordinates one chunk spans.
    low: &'a [F192],
    /// The eq table of the other coordinates, scaled by the claim's power of lambda.
    high: Vec<F192>,
}

impl<'a> PointWeight<'a> {
    fn new(claim: &'a StackClaim, lambda: F192, chunk_log: usize) -> Self {
        let (offset, slot, stride_log, point) = match claim {
            StackClaim::Point { offset, low_point, .. } => (*offset, 0, 0, low_point.as_slice()),
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => (*offset, *slot, *stride_log, point.as_slice()),
        };
        // The coordinates one chunk covers, past the frozen ones.
        let low_vars = point.len().min(chunk_log.saturating_sub(stride_log));
        let (low, high_point) = point.split_at(low_vars);
        Self {
            offset,
            end: offset + (1usize << (stride_log + point.len())),
            slot,
            stride: 1 << stride_log,
            low,
            high: eq_table_seeded(high_point, lambda),
        }
    }

    /// Where the claim meets the chunk of `len` words at `start`.
    ///
    /// # Returns
    ///
    /// Its first word in the chunk, and the seed of its low table there.
    fn hit(&self, start: usize, len: usize) -> Option<(usize, F192)> {
        // The weighted words this chunk holds, as indices along the stride.
        let base = self.offset + self.slot;
        let (lo, hi) = (start.max(base), (start + len).min(self.end));
        if lo >= hi {
            return None;
        }
        let first = (lo - base).div_ceil(self.stride);
        let end = (hi - base).div_ceil(self.stride);
        if first == end {
            return None;
        }

        // Invariant: a chunk covers exactly one entry of the high table.
        let n = 1usize << self.low.len();
        assert!(first.is_multiple_of(n) && end - first == n);
        Some((base + first * self.stride - start, self.high[first / n]))
    }

    /// The in-lane words the claim covers: a whole lane when it spans lanes, its own slice otherwise.
    const fn in_lane(&self, lane_block: usize) -> Range<usize> {
        if self.end - self.offset >= lane_block {
            0..lane_block
        } else {
            let start = self.offset % lane_block;
            start..start + (self.end - self.offset)
        }
    }

    /// Add the low eq table, seeded by `seed`, at every `stride`-th word of `dst` from `at`.
    fn scatter(&self, at: usize, seed: F192, dst: &mut [F192], scratch: &mut [MaybeUninit<F192>]) {
        let n = 1usize << self.low.len();
        fill_eq_table_uninit(self.low, seed, &mut scratch[..n]);
        // SAFETY: the build above initializes this prefix before it is read.
        let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), n) };
        for (i, &value) in eq.iter().enumerate() {
            dst[at + i * self.stride] += value;
        }
    }
}

/// A ring-switched claim's weight on the window `start..end` of a buffer.
///
/// The buffer is the stack, or the stack folded over its lanes.
struct RingPiece {
    start: usize,
    end: usize,
    weight: RingWeight,
}

/// A ring-switched claim's weight over its window.
enum RingWeight {
    /// Every word in memory, the first one at index zero.
    Kept(Vec<F192>),
    /// The factored form, its map applied whenever a word is read.
    Deferred(DeferredWeight),
}

impl RingPiece {
    /// Add its share of the chunk of `dst.len()` words at `start`.
    fn add_to(&self, start: usize, dst: &mut [F192]) {
        let (lo, hi) = (start.max(self.start), (start + dst.len()).min(self.end));
        if lo < hi {
            let dst = &mut dst[lo - start..hi - start];
            match &self.weight {
                RingWeight::Kept(words) => {
                    for (d, &w) in dst.iter_mut().zip(&words[lo - self.start..]) {
                        *d += w;
                    }
                }
                RingWeight::Deferred(weight) => weight.add_to(lo - self.start, dst),
            }
        }
    }
}

/// A region spanning at most this many lanes keeps its weight in memory.
///
/// Why: its lane fold is then one product per word.
///
/// The closed form costs one map application per folded word, which pays only over regions spanning more lanes.
const KEEP_MAX_LANES: usize = 2;

/// Words one task of a dense weight build writes, a whole number of 64-entry blocks.
const DENSE_CHUNK: usize = 1 << 12;

/// Every word of `len` built in parallel, each chunk written by `fill(start, chunk)` into zeros.
fn dense(len: usize, fill: impl Fn(usize, &mut [F192]) + Sync) -> Vec<F192> {
    let mut words = vec![F192::ZERO; len];
    parallel::chunks_mut(&mut words, DENSE_CHUNK, |i, chunk| fill(i * DENSE_CHUNK, chunk));
    words
}

/// One ring-switched claim: its region, its point, and its scale `gamma_rs^j`.
struct RingClaim<'a> {
    offset: usize,
    vars: usize,
    point: &'a [F192],
    scale: F192,
}

/// The original anchor's equality weight, truncated to the occupied lane prefix.
///
/// Coordinates are least-significant first: in-lane coordinates precede lane bits.
/// A partial first fold binds the *lowest* lane bits, retaining one scalar seed
/// per group, including its possibly incomplete last group. The remaining lane
/// bits stay in the original equality coefficients, not a newly sampled point.
struct AnchorWeight<'a> {
    low: &'a [F192],
    rows_high: Vec<F192>,
    lanes: Vec<F192>,
}

impl<'a> AnchorWeight<'a> {
    fn new(point: &'a [F192], lambda: F192, lane_block: usize, n_lanes: usize) -> Self {
        let block_log = lane_block.ilog2() as usize;
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        Self {
            low: &point[..chunk_log],
            rows_high: eq_table(&point[chunk_log..block_log]),
            lanes: eq_prefix(&point[block_log..], n_lanes, lambda),
        }
    }

    fn add_chunk(&self, x: usize, lane_seed: F192, dst: &mut [F192], scratch: &mut [MaybeUninit<F192>]) {
        let n = 1usize << self.low.len();
        assert_eq!(dst.len(), n);
        let seed = lane_seed * self.rows_high[x / n];
        fill_eq_table_uninit(self.low, seed, &mut scratch[..n]);
        // SAFETY: the table build initializes all n entries before this read.
        let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), n) };
        for (d, &w) in dst.iter_mut().zip(eq) {
            *d += w;
        }
    }

    fn folded_seeds(&self, eq: &[F192]) -> Vec<F192> {
        self.lanes
            .chunks(eq.len())
            .map(|lanes| lanes.iter().zip(eq).fold(F192::ZERO, |sum, (&lane, &e)| sum + lane * e))
            .collect()
    }
}

/// The stacked opening's weight, never stored whole.
pub(super) struct StackWeight<'a> {
    /// Words of the committed stack.
    stack_len: usize,
    /// Words per lane block.
    lane_block: usize,
    /// The ring-switching map.
    phi: F192Map,
    /// Every ring-switched claim, in family order.
    ring_claims: Vec<RingClaim<'a>>,
    /// Each ring-switched claim's weight over its region.
    pieces: Vec<RingPiece>,
    /// Each point claim's weight.
    points: Vec<PointWeight<'a>>,
    /// For each lane block, the point claims whose slice meets it.
    by_lane: Vec<Vec<usize>>,
    /// The borrowed immutable anchor, separate from ordinary full-slice claims; a hiding stack has none.
    anchor: Option<AnchorWeight<'a>>,
}

impl<'a> StackWeight<'a> {
    /// The weight of the statement's point claims at their powers of lambda, plus its ring-switched family.
    ///
    /// An anchored stack adds its commitment-time anchor point at its own power of lambda, on the occupied lanes.
    pub(super) fn new(
        stack_len: usize,
        lane_block: usize,
        statement: Statement<'a>,
        lambdas: &[F192],
        family: &RingFamily,
        anchor: Option<(&'a [F192], F192)>,
    ) -> Self {
        let Statement { points: claims, rings } = statement;
        assert_eq!(claims.len(), lambdas.len());

        // A fill writes one chunk, or one whole lane block when blocks are smaller.
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        let points: Vec<_> = (claims.iter().zip(lambdas))
            .map(|(claim, &lambda)| PointWeight::new(claim, lambda, chunk_log))
            .collect();

        // Index the point claims by the lane blocks they meet, so a fill visits only those.
        let mut by_lane = vec![Vec::new(); stack_len / lane_block];
        for (index, weight) in points.iter().enumerate() {
            for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
                lane.push(index);
            }
        }

        // Ring-switched claim `j` takes `gamma_rs^j`, in region order.
        let n_claims = rings.iter().map(|ring| ring.claims.len()).sum();
        let mut scales = family.gamma_rs().powers(n_claims).into_iter();
        let ring_claims: Vec<RingClaim<'_>> = (rings.iter())
            .flat_map(|ring| ring.claims.iter().map(move |claim| (ring, claim)))
            .map(|(ring, claim)| RingClaim {
                offset: ring.offset,
                vars: ring.qflock_vars,
                point: &claim.suffix_point,
                scale: scales.next().expect("one scale per claim"),
            })
            .collect();

        // Each claim's weight on its region: Phi of its scaled eq table, kept in memory where its region is narrow.
        let phi = family.map();
        let block_log = lane_block.ilog2() as usize;
        let weights = DeferredWeight::batch(ring_claims.iter().map(|claim| (claim.point, claim.scale, phi.clone())));
        let pieces = (ring_claims.iter().zip(weights))
            .map(|(claim, weight)| {
                let lanes = 1usize << claim.vars.saturating_sub(block_log);
                let weight = if lanes <= KEEP_MAX_LANES {
                    RingWeight::Kept(dense(weight.len(), |start, chunk| weight.add_to(start, chunk)))
                } else {
                    RingWeight::Deferred(weight)
                };
                RingPiece {
                    start: claim.offset,
                    end: claim.offset + (1 << claim.vars),
                    weight,
                }
            })
            .collect();

        Self {
            stack_len,
            lane_block,
            phi,
            ring_claims,
            pieces,
            points,
            by_lane,
            anchor: anchor.map(|(point, lambda)| AnchorWeight::new(point, lambda, lane_block, stack_len / lane_block)),
        }
    }

    /// The ring-switched claims' weights folded over the lanes by the eq weights `eq`.
    ///
    /// - A kept region's words are scaled by their lane's eq weight as each folded chunk is written.
    /// - A wider region fills whole lanes, so its folded weight is one GF(2)-linear map of an in-lane eq table:
    ///
    /// ```text
    ///     sum_l e_l · Phi(c · eq(r_hi, l) · eq(r_lo, x))  =  Psi(eq(r_lo, x))
    ///     Psi(u) = sum_l e_l · Phi(c · eq(r_hi, l) · u)
    /// ```
    ///
    /// # Returns
    ///
    /// The kept regions to fold, then one weight per group of folded lanes of every wider region.
    fn folded_pieces(&self, eq: &[F192]) -> (Vec<KeptFold<'_>>, Vec<RingPiece>) {
        let block_log = self.lane_block.ilog2() as usize;
        let per = eq.len();
        let n_lanes = self.stack_len / self.lane_block;
        let mut kept = Vec::new();
        // Each group's window, the in-lane point and the terms of its map.
        let mut groups = Vec::new();
        for (claim, piece) in self.ring_claims.iter().zip(&self.pieces) {
            let first_lane = claim.offset >> block_log;
            match &piece.weight {
                // A kept region lies in one group: its folded words are its lanes' words, each scaled by its lane's eq weight.
                RingWeight::Kept(words) => {
                    let len = words.len().min(self.lane_block);
                    kept.push(KeptFold {
                        start: first_lane / per * self.lane_block + claim.offset % self.lane_block,
                        len,
                        first_lane,
                        words,
                    });
                }
                // Whole lanes: each lane's scale is the eq of its index at the claim's high coordinates.
                RingWeight::Deferred(_) if claim.vars >= block_log => {
                    let (low, high) = claim.point.split_at(block_log);
                    let scales = eq_table_seeded(high, claim.scale);
                    let lanes = first_lane..first_lane + scales.len();

                    // One map per group of folded lanes, over the group's lanes in the region.
                    for group in lanes.start / per..lanes.end.div_ceil(per) {
                        let in_group = lanes.start.max(group * per)..lanes.end.min((group + 1) * per).min(n_lanes);
                        let terms: Vec<(F192, F192)> = in_group
                            .map(|lane| (eq[lane - group * per], scales[lane - first_lane]))
                            .collect();
                        groups.push((group * self.lane_block, low, terms));
                    }
                }
                RingWeight::Deferred(_) => unreachable!("a region inside one lane is kept"),
            }
        }

        // Every group's map is one task, then every group's weight one claim of a batch.
        let maps = parallel::map_collect(groups.len(), |g| self.phi.sum_after_mul(&groups[g].2));
        let weights = DeferredWeight::batch((groups.iter().zip(maps)).map(|((_, low, _), map)| (*low, F192::ONE, map)));
        let deferred = (groups.iter().zip(weights))
            .map(|(&(start, ..), weight)| RingPiece {
                start,
                end: start + self.lane_block,
                weight: RingWeight::Deferred(weight),
            })
            .collect();
        (kept, deferred)
    }
}

/// A kept region's words, folded over its lanes as each chunk of the folded weight is written.
struct KeptFold<'a> {
    /// The folded index of its first word.
    start: usize,
    /// Its words in one lane.
    len: usize,
    /// The lane its region starts in.
    first_lane: usize,
    /// Its kept words, lane after lane.
    words: &'a [F192],
}

impl KeptFold<'_> {
    /// Adds its folded words to the chunk of `dst.len()` folded words at `start`, lane `l` scaled by `eq[l mod |eq|]`.
    fn add_to(&self, start: usize, eq: &[F192], dst: &mut [F192]) {
        let (lo, hi) = (start.max(self.start), (start + dst.len()).min(self.start + self.len));
        if lo < hi {
            let dst = &mut dst[lo - start..hi - start];
            for (lane, words) in self.words.chunks_exact(self.len).enumerate() {
                let e = eq[(self.first_lane + lane) % eq.len()];
                for (d, &w) in dst.iter_mut().zip(&words[lo - self.start..]) {
                    *d += e * w;
                }
            }
        }
    }
}

impl InitialWeight for StackWeight<'_> {
    fn fill(&self, start: usize, dst: &mut [F192]) {
        dst.fill(F192::ZERO);

        // The ring-switched regions this chunk meets.
        for piece in &self.pieces {
            piece.add_to(start, dst);
        }

        // The point claims of this chunk's lane block.
        let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
        for &index in &self.by_lane[start / self.lane_block] {
            let point = &self.points[index];
            if let Some((at, seed)) = point.hit(start, dst.len()) {
                point.scatter(at, seed, dst, &mut scratch);
            }
        }
        if let Some(anchor) = &self.anchor {
            anchor.add_chunk(
                start % self.lane_block,
                anchor.lanes[start / self.lane_block],
                dst,
                &mut scratch,
            );
        }
    }

    fn fold_lanes(&self, rs: &[F192]) -> Vec<F192> {
        let eq = eq_table(rs);
        let per = eq.len();
        assert!(per <= MAX_FOLDED_LANES, "the first fold binds at most four lane bits");
        let n_lanes = self.stack_len / self.lane_block;
        let n_groups = n_lanes.div_ceil(per);
        let (kept, pieces) = self.folded_pieces(&eq);
        let anchor_seeds = self.anchor.as_ref().map(|anchor| anchor.folded_seeds(&eq));

        // The point claims meeting each group of folded lanes, each once, with the in-lane words it covers.
        let by_group: Vec<Vec<(usize, Range<usize>)>> = (0..n_groups)
            .map(|group| {
                let lanes = &self.by_lane[group * per..((group + 1) * per).min(n_lanes)];
                let mut claims: Vec<usize> = lanes.iter().flatten().copied().collect();
                claims.sort_unstable();
                claims.dedup();
                (claims.into_iter())
                    .map(|index| (index, self.points[index].in_lane(self.lane_block)))
                    .collect()
            })
            .collect();

        let chunk = self.lane_block.min(INITIAL_BASIS_CHUNK);
        let mut out = Box::new_uninit_slice(n_groups * self.lane_block);
        // SAFETY: each chunk is zeroed below before anything is added to it.
        let folded = unsafe { primitives::write_only(&mut out) };
        parallel::chunks_mut(folded, chunk, |c, dst| {
            let start = c * chunk;
            let (group, x) = (start / self.lane_block, start % self.lane_block);
            dst.fill(F192::ZERO);

            // The ring-switched claims: kept regions folded here, the others already folded.
            for region in &kept {
                region.add_to(start, &eq, dst);
            }
            for piece in &pieces {
                piece.add_to(start, dst);
            }

            // The point claims: lanes meeting the chunk at one word add their seeds, then one table is built.
            let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
            let mut hits = [(0, F192::ZERO); MAX_FOLDED_LANES];
            let words = x..x + dst.len();
            for (index, covered) in &by_group[group] {
                if covered.end <= words.start || words.end <= covered.start {
                    continue;
                }
                let point = &self.points[*index];
                let mut n_hits = 0;
                for (lane, &e) in (group * per..n_lanes).zip(&eq) {
                    if let Some((at, seed)) = point.hit(lane * self.lane_block + x, dst.len()) {
                        match hits[..n_hits].iter_mut().find(|(a, _)| *a == at) {
                            Some((_, sum)) => *sum += e * seed,
                            None => {
                                hits[n_hits] = (at, e * seed);
                                n_hits += 1;
                            }
                        }
                    }
                }
                for &(at, seed) in &hits[..n_hits] {
                    point.scatter(at, seed, dst, &mut scratch);
                }
            }
            if let (Some(anchor), Some(seeds)) = (&self.anchor, &anchor_seeds) {
                anchor.add_chunk(x, seeds[group], dst, &mut scratch);
            }
        });
        // SAFETY: the chunks above wrote every word.
        unsafe { out.assume_init() }.into_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::{RingSwitch, SliceClaim};
    use fiat_shamir::{ProverState, SessionId};
    use primitives::bit_fold::BLOCK;
    use primitives::field::F64;
    use primitives::test_util::Rng;

    /// A stack of `lanes` lane blocks of `2^lane_vars` words, and claims of every shape on it.
    ///
    /// Ring regions span lanes or lie inside one; point claims are plain or strided.
    fn statement(rng: &mut Rng, lane_vars: usize, lanes: usize) -> (Vec<RingSwitch>, Vec<StackClaim>, Vec<F192>) {
        let lane_block = 1 << lane_vars;
        // Regions: the second quarter of the last lane up to lane 1, two lanes from lane 2, and lane 4 whole: all kept.
        let mut regions = vec![((lanes.min(2) - 1) * lane_block + lane_block / 4, lane_vars - 2)];
        if lanes >= 4 {
            regions.push((2 * lane_block, lane_vars + 1));
        }
        if lanes >= 5 {
            regions.push((4 * lane_block, lane_vars));
        }
        // Wider regions, folded in closed form rather than kept: four lanes, then sixteen.
        if lanes >= 8 {
            regions.push((4 * lane_block, lane_vars + 2));
        }
        if lanes >= 32 {
            regions.push((16 * lane_block, lane_vars + 4));
        }
        let rings = (regions.iter())
            .map(|&(offset, vars)| RingSwitch {
                offset,
                qflock_vars: vars,
                // The weight reads only the points, so the slices are any 64 values.
                claims: (0..2)
                    .map(|_| SliceClaim {
                        suffix_point: rng.ext_vec(vars),
                        s_hat_v: rng.ext_vec(F64::DEGREE),
                    })
                    .collect(),
            })
            .collect();
        // Point claims: a lane, a short slice, a single word, a run of lanes, and strided columns.
        let mut supports = vec![(0, lane_vars), (8, 3), (0, 0)];
        if lanes >= 4 {
            supports.push((0, lane_vars + 2));
        }
        let mut claims: Vec<StackClaim> = (supports.into_iter())
            .map(|(offset, vars)| StackClaim::Point {
                offset,
                low_point: rng.ext_vec(vars),
                value: rng.ext(),
            })
            .collect();
        for stride_log in [0, 1, 3, lane_vars - 1, lane_vars] {
            claims.push(StackClaim::Strided {
                offset: 0,
                slot: (1 << stride_log) - 1,
                stride_log,
                point: rng.ext_vec(lane_vars - stride_log),
                value: rng.ext(),
            });
        }
        let lambdas = rng.ext_vec(claims.len());
        (rings, claims, lambdas)
    }

    /// The weight written out naively, one eq entry at a time, sharing no code with the fill under test.
    fn dense_weight(
        stack_len: usize,
        rings: &[RingSwitch],
        claims: &[StackClaim],
        lambdas: &[F192],
        family: &RingFamily,
    ) -> Vec<F192> {
        let mut dense = vec![F192::ZERO; stack_len];
        let phi = family.map();
        let mut scale = F192::ONE;
        for ring in rings {
            for claim in &ring.claims {
                for (i, &e) in eq_table(&claim.suffix_point).iter().enumerate() {
                    let mut one = [F192::ZERO; 1];
                    phi.apply_add(&[scale * e; BLOCK], &mut one);
                    dense[ring.offset + i] += one[0];
                }
                scale *= family.gamma_rs();
            }
        }
        for (claim, &lambda) in claims.iter().zip(lambdas) {
            let (base, stride_log, point) = match claim {
                StackClaim::Point { offset, low_point, .. } => (*offset, 0, low_point.as_slice()),
                StackClaim::Strided {
                    offset,
                    slot,
                    stride_log,
                    point,
                    ..
                } => (*offset + *slot, *stride_log, point.as_slice()),
            };
            for j in 0..1usize << point.len() {
                let w = point.iter().enumerate().fold(lambda, |w, (i, &p_i)| {
                    w * if (j >> i) & 1 == 1 { p_i } else { F192::ONE + p_i }
                });
                dense[base + (j << stride_log)] += w;
            }
        }
        dense
    }

    #[test]
    fn the_weight_and_its_lane_folds_are_the_dense_ones() {
        // Invariant: the chunked fill is the dense weight.
        //
        // And every lane fold is the dense weight folded by the lanes' eq weights.
        let mut rng = Rng::new(0xBA515);
        // Fixture state: lane blocks below, at and above one fill chunk; lane counts below one group, at it, and past it.
        for (lane_vars, lanes) in [
            (6usize, 1usize),
            (6, 3),
            (6, 5),
            (8, 16),
            (8, 17),
            (10, 15),
            (10, 33),
            (10, 64),
            (12, 3),
        ] {
            for anchored in [false, true] {
                let lane_block = 1 << lane_vars;
                let stack_len = lanes * lane_block;
                let (rings, claims, lambdas) = statement(&mut rng, lane_vars, lanes);
                let family = RingFamily::sample(&mut ProverState::new(&SessionId::new(b"stack-weight-test"), &0u64));
                let mut dense = dense_weight(stack_len, &rings, &claims, &lambdas, &family);
                let anchor_point = rng.ext_vec(lane_vars + 6);
                let anchor_lambda = rng.ext();
                if anchored {
                    for (i, value) in dense.iter_mut().enumerate() {
                        let eq = anchor_point.iter().enumerate().fold(anchor_lambda, |acc, (j, &r)| {
                            acc * if (i >> j) & 1 == 0 { F192::ONE + r } else { r }
                        });
                        *value += eq;
                    }
                }
                let statement = Statement {
                    points: &claims,
                    rings: &rings,
                };
                let anchor = anchored.then_some((anchor_point.as_slice(), anchor_lambda));
                let weight = StackWeight::new(stack_len, lane_block, statement, &lambdas, &family, anchor);
                let label = format!("lane_vars={lane_vars}, lanes={lanes}, anchored={anchored}");

                // The fill, chunk by chunk as the first pass reads it.
                let chunk = lane_block.min(INITIAL_BASIS_CHUNK);
                let mut filled = vec![F192::ZERO; stack_len];
                for (i, out) in filled.chunks_exact_mut(chunk).enumerate() {
                    weight.fill(i * chunk, out);
                }
                assert_eq!(filled, dense, "fill, {label}");

                // The fold over one to four lane bits, lanes past the last one folding as zeros.
                for bits in 1..=4 {
                    let rs = rng.ext_vec(bits);
                    let eq = eq_table(&rs);
                    let groups = lanes.div_ceil(eq.len());
                    let mut expected = vec![F192::ZERO; groups * lane_block];
                    for (word, e) in expected.iter_mut().enumerate() {
                        let (group, x) = (word / lane_block, word % lane_block);
                        for (j, &w) in eq.iter().enumerate() {
                            let lane = group * eq.len() + j;
                            if lane < lanes {
                                *e += w * dense[lane * lane_block + x];
                            }
                        }
                    }
                    assert_eq!(weight.fold_lanes(&rs), expected, "fold over {bits} bits, {label}");
                }
            }
        }
    }
}
