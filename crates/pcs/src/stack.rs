// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The stacked opening: one WHIR run proves every claim on the committed stack.
//!
//! # Overview
//!
//! The stack is `2^log_n` words of `K`.
//!
//! Only its leading lane blocks are committed, and every claim lives inside them.
//!
//! Two kinds of claims share one weight:
//!
//! - A point claim: a multilinear evaluation of an aligned slice of the stack.
//! - A ring-switched claim: the 64 bit-slices of a packed region at a point.
//!
//! The ring-switched claims form one family.
//!
//! - Claim `j` is scaled by `gamma_rs^j`.
//! - One GF(2)-linear map `Phi` then covers them all (doc `leanvm` Annex A, `rs:family`).
//! - Their points need not be related.
//!
//! # The weight
//!
//! ```text
//!     w(x) = sum_j  Phi(gamma_rs^j · eq(r_j, ·))   on region j
//!          + sum_i  lambda^(1+i) · eq(p_i, ·)      on claim i's slice
//! ```
//!
//! - The family takes `lambda^0`, the point claims the next powers (the batching step of `thm:rbr`).
//! - `lambda` is drawn after the map, so the family's error is the constant term of the batched error.
//!
//! # Transcript order
//!
//! ```text
//!     gamma_rs  ->  the map's six challenges  ->  lambda  ->  WHIR
//! ```
//!
//! The caller bound every claim's slices and value already, so none is observed again.
//!
//! # Who evaluates the weight
//!
//! - The prover never stores it: chunks for the first pass, a closed-form lane fold for the first fold.
//! - The verifier evaluates it once, at the terminal sumcheck point.

use std::mem::MaybeUninit;
use std::ops::Range;

use super::ring_switch::{DeferredWeight, RingFamily, RingSwitch};
use super::verifier::OpeningVerifier;
use super::whir::{Config, INITIAL_BASIS_CHUNK, InitialWeight, ProverData, WhirError};
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::Transmitter;
use primitives::bit_fold::F192Map;
use primitives::field::{F64, F192, powers};
use primitives::multilinear::{eq_table, eq_table_seeded, fill_eq_table_uninit};

/// A point claim on the committed stack.
///
/// Its point and value are field elements, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim<E = F192> {
    /// Weight `eq(low_point, ·)` on the aligned slice `[offset, offset + 2^|low_point|)`.
    Point { offset: usize, low_point: Vec<E>, value: E },

    /// A claim on a packed column.
    ///
    /// - The low `stride_log` coordinates are frozen to the bits of `slot`.
    /// - The weight sits at `offset + slot + j · 2^stride_log`, at `eq(point, j)`.
    ///
    /// It is a point claim over `slot_bits ++ point`, folded in `O(2^|point|)` work.
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<E>,
        value: E,
    },
}

impl<E: Copy> StackClaim<E> {
    /// The value the claim states.
    #[inline]
    pub const fn value(&self) -> E {
        match self {
            Self::Point { value, .. } | Self::Strided { value, .. } => *value,
        }
    }

    /// The claim's slice: its first word, and the base-two logarithm of its length.
    const fn support(&self) -> (usize, usize) {
        match self {
            Self::Point { offset, low_point, .. } => (*offset, low_point.len()),
            Self::Strided {
                offset,
                stride_log,
                point,
                ..
            } => (*offset, *stride_log + point.len()),
        }
    }

    /// Whether the claim is an aligned slice of the first `committed` words.
    ///
    /// A strided claim's slot must also fit its stride.
    fn is_well_formed(&self, committed: usize) -> bool {
        let (offset, vars) = self.support();
        let slot_fits = match self {
            Self::Point { .. } => true,
            Self::Strided { slot, stride_log, .. } => 1usize.checked_shl(*stride_log as u32).is_some_and(|s| *slot < s),
        };
        slot_fits && is_aligned_slice(offset, vars, committed)
    }

    /// The claim's weight at a point `x` of the stack cube.
    ///
    /// ```text
    ///     point:    eq(low_point, x_low)                          · eq(offset bits, x_high)
    ///     strided:  eq(slot bits, x_slot) · eq(point, x_middle)   · eq(offset bits, x_high)
    /// ```
    fn eq_at<A: Arith<E = E>>(&self, a: &mut A, x: &[E]) -> E {
        match self {
            Self::Point { offset, low_point, .. } => {
                let n = low_point.len();
                let low = a.eq_eval(low_point, &x[..n]);
                let sel = a.eq_bits(offset >> n, &x[n..]);
                a.mul(low, sel)
            }
            Self::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => {
                let block = stride_log + point.len();
                let slot = a.eq_bits(*slot, &x[..*stride_log]);
                let low = a.eq_eval(point, &x[*stride_log..block]);
                let sel = a.eq_bits(offset >> block, &x[block..]);
                let inner = a.mul(slot, low);
                a.mul(inner, sel)
            }
        }
    }
}

/// Whether `[offset, offset + 2^vars)` is aligned to its length and inside the first `committed` words.
///
/// Shifts are checked, so an absurd width is refused rather than wrapped.
fn is_aligned_slice(offset: usize, vars: usize, committed: usize) -> bool {
    1usize
        .checked_shl(vars as u32)
        .is_some_and(|len| offset.is_multiple_of(len) && offset.checked_add(len).is_some_and(|end| end <= committed))
}

/// What an opening proves about one committed stack.
///
/// Its points and values are field elements, or whatever a verifier holds them as.
#[derive(Clone, Copy, Debug)]
pub struct Statement<'a, E = F192> {
    /// Point claims on aligned slices of the stack.
    pub points: &'a [StackClaim<E>],
    /// Ring-switched claims on packed regions of the stack.
    pub rings: &'a [RingSwitch<E>],
}

impl<E: Copy> Statement<'_, E> {
    /// The statement's invariants, one check for the prover and the verifier.
    ///
    /// - There is at least one ring-switched claim.
    /// - Every region and every claim is an aligned slice of the first `committed` words.
    /// - Every ring-switched claim's point spans its region.
    fn check(&self, log_n: usize, committed: usize) -> Result<(), WhirError> {
        if self.rings.iter().all(|ring| ring.claims.is_empty()) {
            return Err(WhirError::NoRingClaim);
        }
        for (index, ring) in self.rings.iter().enumerate() {
            let spans = (ring.claims.iter()).all(|claim| claim.suffix_point.len() == ring.qflock_vars);
            if ring.qflock_vars > log_n || !spans || !is_aligned_slice(ring.offset, ring.qflock_vars, committed) {
                return Err(WhirError::Region { index });
            }
        }
        if let Some(index) = self.points.iter().position(|claim| !claim.is_well_formed(committed)) {
            return Err(WhirError::PointClaim { index });
        }
        Ok(())
    }
}

/// A committed stack, as its prover keeps it for opening.
///
/// The stack's words are not kept: the caller holds them, and hands them back to open.
pub struct CommittedStack {
    /// The stack's size, as a base-two logarithm of words.
    log_n: usize,
    /// The configuration the stack is committed and opened under.
    config: Config,
    /// The codeword and its Merkle tree.
    data: ProverData,
}

impl CommittedStack {
    /// Commit to a stack's leading lane blocks.
    ///
    /// The stack's other lanes are zero, and the root is the one a full stack would have.
    ///
    /// # Panics
    ///
    /// Panics unless `stack` is a whole number of lane blocks, at least one and at most the configuration's lane count.
    pub fn new(stack: &[F64], log_n: usize, config: Config) -> Self {
        let data = super::whir::commit(stack, log_n, config.initial_k(), config.log_inv_rates()[0]);
        Self { log_n, config, data }
    }

    /// The commitment's Merkle root.
    pub fn root(&self) -> Hash {
        self.data.root()
    }

    /// Prove `statement` about `stack`, the words committed.
    ///
    /// The opening observes none of the claims, so the caller must have bound them before it:
    ///
    /// - every claim's value is in the transcript or the public statement,
    /// - every point is an earlier challenge or public.
    ///
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claims are bound.
    ///
    /// # Panics
    ///
    /// Panics on a statement the verifier would refuse.
    pub fn open(&self, ps: &mut impl Transmitter, stack: &[F64], statement: Statement<'_>) {
        if let Err(error) = statement.check(self.log_n, stack.len()) {
            panic!("a malformed statement: {error}");
        }
        let span = tracing::info_span!("Ring switch").entered();

        // The family's challenges, then lambda.
        let family = RingFamily::sample(ps);
        let lambdas = powers(ps.sample(), 1 + statement.points.len());

        // The target: the family's at lambda^0, then each point claim's value at its own power.
        let points = (statement.points.iter()).zip(&lambdas[1..]);
        let target = family.share(&mut Native, statement.rings).target(&mut Native)
            + points.fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());

        // The weight, never stored: WHIR reads it by chunks, then folded.
        let lane_block = 1usize << (self.log_n - self.config.initial_k());
        let weight = StackWeight::new(stack.len(), lane_block, statement, &lambdas[1..], &family);
        drop(span);

        super::whir::prove(&self.config, self.log_n, stack, &weight, target, &self.data, ps);
    }
}

/// A committed stack, as its verifier holds it.
///
/// Its root is a digest, or whatever a verifier holds it as.
#[derive(Clone, Debug)]
pub struct StackCommitment<R> {
    /// The commitment's Merkle root.
    root: R,
    /// The stack's size, as a base-two logarithm of words.
    log_n: usize,
    /// The committed lane blocks.
    n_lanes: usize,
    /// The configuration the stack is committed and opened under.
    config: Config,
}

impl<R: Copy> StackCommitment<R> {
    /// The commitment to a stack of `2^log_n` words, its first `n_lanes` lane blocks committed under `config`.
    pub const fn new(root: R, log_n: usize, n_lanes: usize, config: Config) -> Self {
        Self {
            root,
            log_n,
            n_lanes,
            config,
        }
    }

    /// Verify an opening of `statement`, as the prover opened it.
    ///
    /// - It replays the ring switch succinctly and recomputes the target.
    /// - The WHIR verifier then evaluates the weight once, at its terminal point.
    ///
    /// The same code runs natively and as the recursion machine's rows.
    ///
    /// The opening observes none of the claims, so the caller must have bound them before it:
    ///
    /// - every claim's value is in the transcript or the public statement,
    /// - every point is an earlier challenge or public.
    ///
    /// A value the prover picks after the batching challenges breaks soundness.
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claims are bound.
    ///
    /// # Errors
    ///
    /// - A region or a claim that is no aligned slice of the committed words.
    /// - The WHIR verifier's refusal.
    pub fn verify<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        statement: Statement<'_, V::E>,
    ) -> Result<(), WhirError> {
        let committed = self.n_lanes << (self.log_n - self.config.initial_k());
        statement.check(self.log_n, committed)?;

        // The family's challenges, then lambda, as the prover drew them.
        let family = RingFamily::draw(v);
        let lambda = v.sample();
        let lambdas = v.powers(lambda, 1 + statement.points.len());
        let share = family.share(v, statement.rings);

        // The target, recomputed from the claims.
        let target = v.scope("target", |v| {
            let family_target = share.target(v);
            (statement.points.iter().zip(&lambdas[1..]))
                .fold(family_target, |acc, (claim, &g)| v.mul_add(g, claim.value(), acc))
        });

        // The weight at the terminal point: the family's closed form, then each point claim's eq.
        let weight_at = |v: &mut V, x: &[V::E]| {
            let family_weight = share.weight_at(v, x);
            (statement.points.iter().zip(&lambdas[1..])).fold(family_weight, |acc, (claim, &g)| {
                let eq = claim.eq_at(v, x);
                v.mul_add(g, eq, acc)
            })
        };
        v.scope("whir", |v| {
            super::whir::verify(v, &self.config, self.log_n, self.n_lanes, target, self.root, weight_at)
        })
    }
}

// The prover's weight
//
// It is filled one aligned chunk at a time, for the first pass.
//
// It is folded over its lane bits in closed form, for the first fold:
//
//     point claim:  the lanes' eq weights add into one seed of its eq table
//     ring claim:   sum_l e_l · Phi(c_l · u) is one GF(2)-linear map of u

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

/// The stacked opening's weight, never stored whole.
struct StackWeight<'a> {
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
}

impl<'a> StackWeight<'a> {
    /// The weight of the statement's point claims at their powers of lambda, plus its ring-switched family.
    fn new(
        stack_len: usize,
        lane_block: usize,
        statement: Statement<'a>,
        lambdas: &[F192],
        family: &RingFamily,
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
        let mut scales = powers(family.gamma_rs(), n_claims).into_iter();
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
    }

    fn fold_lanes(&self, rs: &[F192]) -> Vec<F192> {
        let eq = eq_table(rs);
        let per = eq.len();
        assert!(per <= MAX_FOLDED_LANES, "the first fold binds at most four lane bits");
        let n_lanes = self.stack_len / self.lane_block;
        let n_groups = n_lanes.div_ceil(per);
        let (kept, pieces) = self.folded_pieces(&eq);

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
        });
        // SAFETY: the chunks above wrote every word.
        unsafe { out.assume_init() }.into_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::SliceClaim;
    use crate::ring_switch::tests::s_hat_v_reference;
    use crate::whir::config::tests::{default_config, test_config_for};
    use crate::whir::inner_product_base_ext;
    use fiat_shamir::merkle::Hash;
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::bit_fold::BLOCK;
    use primitives::test_util::Rng;

    const DOMAIN: &[u8] = b"stack-open-test";

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
        for (lane_vars, lanes) in [(6usize, 1usize), (6, 5), (8, 16), (10, 15), (10, 37)] {
            let lane_block = 1 << lane_vars;
            let stack_len = lanes * lane_block;
            let (rings, claims, lambdas) = statement(&mut rng, lane_vars, lanes);
            let family = RingFamily::sample(&mut ProverState::from_label(DOMAIN));
            let dense = dense_weight(stack_len, &rings, &claims, &lambdas, &family);
            let statement = Statement {
                points: &claims,
                rings: &rings,
            };
            let weight = StackWeight::new(stack_len, lane_block, statement, &lambdas, &family);
            let label = format!("lane_vars={lane_vars}, lanes={lanes}");

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

    #[test]
    fn a_malformed_statement_is_refused() {
        // Invariant: the verifier refuses what the prover refuses.
        //
        // Every region and claim is an aligned slice of the committed lanes, a strided slot inside its stride.
        let ring = |offset: usize, vars: usize| RingSwitch {
            offset,
            qflock_vars: vars,
            claims: vec![SliceClaim {
                suffix_point: vec![F192::ZERO; vars],
                s_hat_v: vec![F192::ZERO; F64::DEGREE],
            }],
        };
        let point = |offset: usize, vars: usize| StackClaim::Point {
            offset,
            low_point: vec![F192::ZERO; vars],
            value: F192::ZERO,
        };
        let strided = |slot: usize| StackClaim::Strided {
            offset: 0,
            slot,
            stride_log: 2,
            point: vec![F192::ZERO; 3],
            value: F192::ZERO,
        };
        // Fixture state: a 2^10-word cube, its first 2^9 words committed.
        let check = |points: &[StackClaim], rings: &[RingSwitch]| Statement { points, rings }.check(10, 1 << 9);
        assert!(check(&[point(64, 6), strided(3)], &[ring(256, 8)]).is_ok());

        // No ring claim; a region past the committed lanes, misaligned, or wider than the cube.
        assert!(matches!(check(&[], &[]), Err(WhirError::NoRingClaim)));
        assert!(matches!(
            check(&[], &[ring(512, 8)]),
            Err(WhirError::Region { index: 0 })
        ));
        assert!(matches!(
            check(&[], &[ring(128, 8)]),
            Err(WhirError::Region { index: 0 })
        ));
        assert!(matches!(
            check(&[], &[ring(0, 64)]),
            Err(WhirError::Region { index: 0 })
        ));

        // A point claim misaligned, or past the committed lanes; a strided slot outside its stride.
        let rings = [ring(0, 8)];
        assert!(matches!(
            check(&[point(32, 6)], &rings),
            Err(WhirError::PointClaim { index: 0 })
        ));
        assert!(matches!(
            check(&[point(512, 6)], &rings),
            Err(WhirError::PointClaim { index: 0 })
        ));
        assert!(matches!(
            check(&[strided(4)], &rings),
            Err(WhirError::PointClaim { index: 0 })
        ));
    }

    struct Instance {
        vc: Config,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        rings: Vec<RingSwitch>,
        fs: ProofTranscript,
    }

    /// A proven opening of a 2^14-word stack.
    ///
    /// ```text
    ///     words 0 .. 3·2^12    three columns, one point claim each
    ///     then 2^8 words       a packed region: one strided claim, one ring-switched claim
    ///     then filler          rings at prefixes of that claim's point, and one at an unrelated point
    /// ```
    ///
    /// The packed region is small, so the verifier's residual cube sits above its coordinates, as in production.
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn build_instance(seed: u64) -> Instance {
        let log_n = 14usize;
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qflock_vars = 8usize;
        let qflock_offset = 3 * col_len;
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        while stack.len() < 1 << log_n {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = eq_table(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::Point {
                    offset,
                    low_point,
                    value,
                }
            })
            .collect();

        // One strided claim into the packed region: its low 3 coordinates frozen to slot 5.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point = rng.ext_vec(qflock_vars - stride_log);
            let eq = eq_table(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qflock_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::Strided {
                offset: qflock_offset,
                slot,
                stride_log,
                point,
                value,
            });
        }

        // The ring-switched regions, each with one claim (plain eq prefix weights).
        let suffix_point = rng.ext_vec(qflock_vars);
        let past = qflock_offset + (1 << qflock_vars);
        let regions = [
            (qflock_offset, suffix_point.clone()),
            (past, suffix_point[..qflock_vars - 1].to_vec()),
            (past + (1 << (qflock_vars - 1)), rng.ext_vec(qflock_vars - 2)),
            (
                past + 3 * (1 << (qflock_vars - 2)),
                suffix_point[..qflock_vars - 2].to_vec(),
            ),
            (
                past + 4 * (1 << (qflock_vars - 2)),
                suffix_point[..qflock_vars - 2].to_vec(),
            ),
        ];
        let rings: Vec<RingSwitch> = regions
            .iter()
            .map(|(offset, suffix_point)| RingSwitch {
                offset: *offset,
                qflock_vars: suffix_point.len(),
                claims: vec![SliceClaim {
                    suffix_point: suffix_point.clone(),
                    s_hat_v: s_hat_v_reference(&stack[*offset..*offset + (1 << suffix_point.len())], suffix_point),
                }],
            })
            .collect();

        let pc = test_config_for(log_n);
        // Invariant: the residual cube sits entirely above the packed region's coordinates.
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let committed = CommittedStack::new(&stack, log_n, pc.clone());
        let mut ps = ProverState::from_label(DOMAIN);
        let statement = Statement {
            points: &point_claims,
            rings: &rings,
        };
        committed.open(&mut ps, &stack, statement);

        Instance {
            vc: pc,
            log_n,
            root: committed.root(),
            point_claims,
            rings,
            fs: ps.into_proof(),
        }
    }

    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        rings: &[RingSwitch],
        fs: &ProofTranscript,
    ) -> bool {
        let mut vs = VerifierState::from_label(DOMAIN, fs);
        let commitment = StackCommitment::new(inst.root, inst.log_n, 1 << inst.vc.initial_k(), inst.vc.clone());
        let statement = Statement {
            points: point_claims,
            rings,
        };
        commitment.verify(&mut vs, statement).is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        // Invariant: an honest opening verifies, and a tampered claim, slice, point or stream word is refused.
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.rings, &inst.fs),
            "honest stacked opening rejected"
        );

        // Wrong point-claim value (dense column claim).
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.rings, &inst.fs),
            "tampered Point value accepted"
        );

        // Wrong strided-claim value.
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Strided { value, .. } = &mut bad_points[3] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.rings, &inst.fs),
            "tampered Strided value accepted"
        );

        // A wrong slice is refused by the ring switch's target.
        // A moved point is refused by the weight, whether it shares its prefix pass or not.
        for r in 0..inst.rings.len() {
            let mut bad_ring = inst.rings.clone();
            bad_ring[r].claims[0].s_hat_v[7] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "tampered ring-switch slice {r} accepted"
            );
            let mut bad_ring = inst.rings.clone();
            bad_ring[r].claims[0].suffix_point[0] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "moved ring-switch point {r} accepted"
            );
        }

        // Every scalar the opening sends is WHIR's, on the stream: a tampered one is refused.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.rings, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // A truncated stream is refused, never a panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.rings, &short_fs),
            "short stream accepted"
        );
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn stacked_open_residual_crosses_qflock() {
        // Invariant: an opening verifies when the residual cube crosses into a ring-switched region.
        //
        // Fixture state: the region is half a 2^14 stack, and the residual cube (3 variables) is wider than its one
        // selector coordinate, so Boolean residual bits cover some of the region's coordinates.
        let log_n = 14usize;
        let qflock_vars = 13usize;
        let qflock_offset = 1usize << 13;
        let mut rng = Rng::new(3);

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point = rng.ext_vec(12);
        let eq = eq_table(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_flock.
        let qflock = &stack[qflock_offset..];
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = s_hat_v_reference(qflock, &suffix_point);
        let claims = vec![SliceClaim { suffix_point, s_hat_v }];

        // A fixed fallback config, so the residual cube's size is known.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let committed = CommittedStack::new(&stack, log_n, pc.clone());
        let ring = RingSwitch {
            offset: qflock_offset,
            qflock_vars,
            claims,
        };
        let statement = |ring| Statement {
            points: &point_claims,
            rings: std::slice::from_ref(ring),
        };
        let mut ps = ProverState::from_label(DOMAIN);
        committed.open(&mut ps, &stack, statement(&ring));
        let fs = ps.into_proof();

        let commitment = StackCommitment::new(committed.root(), log_n, 1 << pc.initial_k(), pc);
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            commitment.verify(&mut vs, statement(&ring)).is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_ring = ring.clone();
        bad_ring.claims[0].s_hat_v[7] += F192::ONE;
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            commitment.verify(&mut vs, statement(&bad_ring)).is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
