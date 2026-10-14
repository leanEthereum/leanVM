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
//!          + lambda^(m+1) · clipped_eq(anchor, x)   on the committed prefix
//! ```
//!
//! - The family takes `lambda^0`, the `m` point claims the next powers, and the immutable anchor the last.
//! - A hiding commitment has no anchor, so its point claims take every power past the family's.
//! - `lambda` is drawn after the map, so the family's error is the constant term of the batched error.
//!
//! # Transcript order
//!
//! ```text
//!     immutable record frame -> gamma_rs -> the map's six challenges -> lambda -> WHIR
//! ```
//!
//! The caller bound every claim's slices and value already, so none is observed again.
//! The frame carries its root and captured chaining value as raw32 prover messages; shape, cursor metadata, pending words, anchor point and value retain their F192 packing.
//! A hiding commitment's opening has no frame: it starts at `gamma_rs`.
//!
//! # Who evaluates the weight
//!
//! - The prover never stores it: chunks for the first pass, a closed-form lane fold for the first fold.
//! - The verifier evaluates it once, at the terminal sumcheck point.
//!
//! # The hiding opening
//!
//! A hiding commitment ends with an aligned group of four uniform lanes, and pads every lane past its power of two.
//!
//! - Each lane carries `k = q_0 + 2` uniform padding coefficients.
//! - The uniform group needs no claim: no weight of the statement has to touch it.
//!
//! Its opening differs from the plain one in three steps, all right after the lane fold's last challenge:
//!
//! - in a zero-knowledge proof, the prover turns its transcript's hiding off and sends the running claim in the clear;
//! - the verifier checks that claim against the one it holds, and continues from it;
//! - the prover sends the padding folded as the lanes are, `g_1[j] = sum_u eq(r, u) pad_u[j]`.
//!
//! Each level-0 query then takes the padding's share off its folded row.
//!
//! What remains is the codeword of the folded data, which the rest of the opening proves about.
//!
//! # Why it hides
//!
//! - Level 0's opened rows: any `k` symbols of a padded lane are uniform, and a query opens at most `q_0` columns.
//! - The folded witness and `g_1`: the uniform group adds a uniform element of `E` to each of their coordinates.
//! - Everything after the lane fold is a function of that uniform folded witness and of public challenges.
//! - Unopened leaves: every lane keeps two spare padding coefficients, so each leaf keeps a uniform symbol per lane.
//!
//! The doc's PCS annex, `sec:pcs-zk`, states and proves this.
//!
//! # Why a hiding commitment has no anchor
//!
//! A plain commitment publishes its anchor: the stack's multilinear extension at a point drawn right after its root.
//! On a hiding commitment that value is one more evaluation of the hidden stack, which `sec:pcs-zk` does not account for.
//! So a hiding commitment, and every weighted opening, which only the hiding key commitment takes, stays unanchored;
//! the anchored constructors refuse a configuration that pads, and the hiding ones a configuration that does not.

mod weight;

use weight::StackWeight;

use crate::merkle::Hash;
use crate::ring_switch::{RingFamily, RingShare, RingSwitch};
use crate::verifier::OpeningVerifier;
use crate::whir::anchor::anchor_eq_at;
use crate::whir::{
    BaseCommitment, Commitment, CommitmentShape, Config, DenseWeight, RANDOM_LANES, WeightAt, WhirError,
    check_config_shape, commit, receive_commitment, send_record_binding, verify_record_binding,
};
use fiat_shamir::ProverState;
use fiat_shamir::arith::{Arith, Native, Stage};
use primitives::field::{F64, F192};
use rand_core::CryptoRng;

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

    /// The claim's slice: its first word, and the base-two logarithm of its length, `None` if that overflows.
    const fn support(&self) -> (usize, Option<usize>) {
        match self {
            Self::Point { offset, low_point, .. } => (*offset, Some(low_point.len())),
            Self::Strided {
                offset,
                stride_log,
                point,
                ..
            } => (*offset, stride_log.checked_add(point.len())),
        }
    }

    /// Whether the claim is an aligned slice of the first `committed` words.
    ///
    /// A strided claim's slot must also fit its stride.
    fn is_well_formed(&self, committed: usize) -> bool {
        let (offset, vars) = self.support();
        let slot_fits = match self {
            Self::Point { .. } => true,
            Self::Strided { slot, stride_log, .. } => pow2(*stride_log).is_some_and(|s| *slot < s),
        };
        slot_fits && vars.is_some_and(|vars| is_aligned_slice(offset, vars, committed))
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
/// Widths are checked whole, so an absurd one is refused rather than wrapped.
fn is_aligned_slice(offset: usize, vars: usize, committed: usize) -> bool {
    pow2(vars)
        .is_some_and(|len| offset.is_multiple_of(len) && offset.checked_add(len).is_some_and(|end| end <= committed))
}

/// `2^log`, or nothing if it does not fit a `usize`.
fn pow2(log: usize) -> Option<usize> {
    u32::try_from(log).ok().and_then(|log| 1usize.checked_shl(log))
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
    /// - Every ring-switched claim's point spans its region and carries its 64 slices.
    fn check(&self, log_n: usize, committed: usize) -> Result<(), WhirError> {
        let mut index = 0;
        let mut all_empty = true;
        while index < self.rings.len() && all_empty {
            all_empty = self.rings[index].claims.is_empty();
            index += 1;
        }
        if all_empty {
            return Err(WhirError::NoRingClaim);
        }
        let mut result = Ok(());
        index = 0;
        while index < self.rings.len() && result.is_ok() {
            let ring = &self.rings[index];
            let mut claim_index = 0;
            let mut spans = true;
            while claim_index < ring.claims.len() && spans {
                let claim = &ring.claims[claim_index];
                spans = claim.suffix_point.len() == ring.qflock_vars && claim.s_hat_v.len() == F64::DEGREE;
                claim_index += 1;
            }
            if ring.qflock_vars > log_n || !spans || !is_aligned_slice(ring.offset, ring.qflock_vars, committed) {
                result = Err(WhirError::Region { index });
            }
            index += 1;
        }
        index = 0;
        while index < self.points.len() && result.is_ok() {
            if !self.points[index].is_well_formed(committed) {
                result = Err(WhirError::PointClaim { index });
            }
            index += 1;
        }
        result
    }
}

/// The claim that the stack's leading words, weighted, sum to a value.
///
/// ```text
///     sum_{x < |weight|} weight[x] * stack[x] = value
/// ```
///
/// It states what no point or ring-switched claim does: a weight given word by word.
///
/// Its elements are field elements, or whatever a verifier holds them as.
#[derive(Clone, Copy, Debug)]
pub struct Weighted<'a, E = F192> {
    /// One weight per leading word, a power of two of them.
    pub weight: &'a [E],
    /// The weighted sum.
    pub value: E,
}

impl<E> Weighted<'_, E> {
    /// The weight's variables, if it is a power of two of words that the committed ones hold.
    fn vars(&self, committed: usize) -> Option<usize> {
        let len = self.weight.len();
        (len.is_power_of_two() && len <= committed).then(|| len.trailing_zeros() as usize)
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
    data: BaseCommitment,
    /// The immutable original commitment, including its pre-header context and anchor; a hiding stack has none.
    record: Option<Commitment>,
}

impl CommittedStack {
    /// Commit to a stack's leading lane blocks under an immutable anchored record, sent on `ps`.
    ///
    /// The stack's other lanes are zero, and the root is the one a full stack would have.
    ///
    /// # Panics
    ///
    /// Panics unless `stack` is a whole number of lane blocks, at least one and at most the configuration's lane count,
    /// or on a configuration that pads: a hiding commitment takes no anchor ([`Self::new_hiding`]).
    pub fn new(ps: &mut ProverState, stack: &[F64], log_n: usize, config: Config) -> Self {
        assert_eq!(config.padding(), 0, "an anchored commitment does not hide");
        check_config_shape(&config, log_n).expect("a valid stack configuration");
        let (record, data) = commit(ps, stack, log_n, config.initial_k(), config.log_inv_rates()[0]);
        Self {
            log_n,
            config,
            data,
            record: Some(record),
        }
    }

    /// The hiding commitment of a stack, which reveals nothing of it beyond the claims its openings prove.
    ///
    /// It has no anchor: the anchor's value would be one more evaluation of the hidden stack.
    /// The caller sends its root.
    ///
    /// The stack's last four lanes are the random group: they are filled here, uniform, from `rng`.
    ///
    /// - Every lane, the group's too, is padded by the configuration's coefficients, drawn from `rng`.
    /// - The lanes before the group hold the data, then zeros up to the group.
    /// - No claim of an opening may weight the group.
    ///
    /// # Panics
    ///
    /// Panics on a configuration that does not pad, or a stack whose lanes are not a multiple of four, at least eight.
    pub fn new_hiding(stack: &mut [F64], log_n: usize, config: Config, rng: &mut impl CryptoRng) -> Self {
        let k = config.padding();
        assert!(k > 0, "a hiding commitment takes a configuration that pads");
        let lane = 1usize << (log_n - config.initial_k());
        let lanes = stack.len() / lane;
        assert!(
            stack.len() == lanes * lane && lanes.is_multiple_of(RANDOM_LANES) && lanes >= 2 * RANDOM_LANES,
            "a hiding stack is whole lanes, its random group an aligned last four"
        );

        // The random group, then every lane's padding.
        let group = &mut stack[(lanes - RANDOM_LANES) * lane..];
        group.iter_mut().for_each(|w| *w = F64(rng.next_u64()));
        let pads: Vec<F64> = (0..lanes * k).map(|_| F64(rng.next_u64())).collect();
        let data = BaseCommitment::new(stack, log_n, config.initial_k(), config.log_inv_rates()[0], &pads);
        Self {
            log_n,
            config,
            data,
            record: None,
        }
    }

    /// The commitment's Merkle root.
    pub fn root(&self) -> Hash {
        self.data.root()
    }

    /// The complete immutable commitment every opening binds, or none for a hiding stack.
    pub const fn record(&self) -> Option<&Commitment> {
        self.record.as_ref()
    }

    /// Prove `statement` about `stack`, the words committed.
    ///
    /// An anchored stack binds its complete record first, then batches its anchor with the claims.
    ///
    /// The opening observes none of the claims, so the caller must have bound them before it:
    ///
    /// - every claim's value is a prover message or part of the instance,
    /// - every point is an earlier challenge or public.
    ///
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claims are bound.
    ///
    /// # Panics
    ///
    /// Panics on a statement the verifier would refuse.
    pub fn open(&self, ps: &mut ProverState, stack: &[F64], statement: Statement<'_>) {
        let lane_block = 1usize << (self.log_n - self.config.initial_k());
        if let Some(record) = &self.record {
            let shape = record.shape();
            assert!(
                shape.valid()
                    && shape.log_n == self.log_n
                    && self.config.initial_k() == shape.log_batch_size
                    && self.config.log_inv_rates().first() == Some(&shape.log_inv_rate)
                    && record.point().len() == shape.log_n
                    && record.valid_context(),
                "a valid immutable stack record"
            );
            check_config_shape(&self.config, shape.log_n).expect("a valid stack configuration");
            assert_eq!(
                stack.len(),
                shape.n_lanes * lane_block,
                "the original committed lane prefix"
            );
        }
        if let Err(error) = statement.check(self.log_n, stack.len()) {
            panic!("a malformed statement: {error}");
        }
        if let Some(record) = &self.record {
            send_record_binding(ps, record);
        }
        let span = tracing::info_span!("Ring switch").entered();

        // The family's challenges, then lambda.
        let family = RingFamily::sample(ps);
        let m = statement.points.len();
        let lambdas = F192::powers(ps.verifier_message(), 1 + m + usize::from(self.record.is_some()));
        let point_lambdas = &lambdas[1..1 + m];

        // Family power zero, ordinary points next, and the original supported anchor last.
        let points = statement.points.iter().zip(point_lambdas);
        let mut target = family.share(&mut Native, statement.rings).target(&mut Native)
            + points.fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());
        if let Some(record) = &self.record {
            target += lambdas[1 + m] * record.value();
        }

        // The weight, never stored: WHIR reads it by chunks, then folded.
        // Borrow the original point; never turn its occupied-prefix weight into a full-cube claim.
        let anchor = (self.record.as_ref()).map(|record| (record.point(), lambdas[1 + m]));
        let weight = StackWeight::new(stack.len(), lane_block, statement, point_lambdas, &family, anchor);
        drop(span);

        crate::whir::prove(&self.config, self.log_n, stack, &weight, target, &self.data, ps);
    }

    /// Prove a weighted claim about `stack`, the words committed, under a hiding commitment.
    ///
    /// The opening observes neither the claim's value nor its weight, so the caller must have bound both before it.
    ///
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claim is bound.
    ///
    /// # Panics
    ///
    /// Panics on a claim the verifier would refuse, or on an anchored stack, whose openings bind its anchor through [`Self::open`].
    pub fn open_weighted(&self, ps: &mut ProverState, stack: &[F64], claim: Weighted<'_>) {
        assert!(self.record.is_none(), "an anchored stack opens through its statement");
        assert!(
            claim.vars(stack.len()).is_some(),
            "a weight on a power of two of committed words"
        );
        let lane_block = 1usize << (self.log_n - self.config.initial_k());
        let mut weight = claim.weight.to_vec();
        weight.resize(stack.len(), F192::ZERO);
        let weight = DenseWeight {
            weight,
            block: lane_block,
        };
        crate::whir::prove(&self.config, self.log_n, stack, &weight, claim.value, &self.data, ps);
    }
}

/// What an opening binds of its commitment.
#[derive(Clone, Debug)]
enum Binding<E, R, K> {
    /// A plain commitment's complete immutable record, anchor included.
    Anchored(Commitment<E, R, K>),
    /// A hiding commitment's root and shape: it has no anchor.
    Hiding {
        /// The commitment's Merkle root.
        root: R,
        /// The committed stack's encoding shape.
        shape: CommitmentShape,
    },
}

/// A committed stack, as its verifier holds it.
///
/// Its complete record's scalars, digest and context words can be native values or recursion wires.
#[derive(Clone, Debug)]
pub struct StackCommitment<E = F192, R = Hash, K = F64> {
    /// The anchored record, or a hiding commitment's root.
    binding: Binding<E, R, K>,
    /// The configuration the stack is committed and opened under.
    config: Config,
}

/// The stack's borrowed terminal weight, shared by native and recursion verifiers.
struct StatementWeight<'a, 'r, E> {
    share: &'a RingShare<'r, E>,
    points: &'a [StackClaim<E>],
    point_lambdas: &'a [E],
    shape: CommitmentShape,
    /// The anchor's point and power of lambda; none for a hiding commitment.
    anchor: Option<(&'a [E], E)>,
}

impl<E: Copy + PartialEq, V: OpeningVerifier<E = E>> WeightAt<V> for StatementWeight<'_, '_, E> {
    fn call(self, v: &mut V, x: &[E]) -> E {
        let mut weight = self.share.weight_at(v, x);
        for i in 0..self.points.len().min(self.point_lambdas.len()) {
            let eq = self.points[i].eq_at(v, x);
            weight = v.mul_add(self.point_lambdas[i], eq, weight);
        }
        match self.anchor {
            Some((point, lambda)) => {
                let anchor = anchor_eq_at(v, self.shape, point, x);
                v.mul_add(lambda, anchor, weight)
            }
            None => weight,
        }
    }
}

/// A weighted claim's terminal weight: its words at the low coordinates, zero high coordinates above them.
struct WeightedAt<'a, E> {
    weight: &'a [E],
    vars: usize,
}

impl<E: Copy, V: OpeningVerifier<E = E>> WeightAt<V> for WeightedAt<'_, E> {
    fn call(self, v: &mut V, x: &[E]) -> E {
        let eq = v.eq_table(&x[..self.vars]);
        let zero = v.zero();
        let mut low = zero;
        let mut i = 0;
        while i < eq.len().min(self.weight.len()) {
            low = v.mul_add(eq[i], self.weight[i], low);
            i += 1;
        }
        let high = v.eq_bits(0, &x[self.vars..]);
        v.mul(low, high)
    }
}

impl<E: Copy, R: Copy, K: Copy> StackCommitment<E, R, K> {
    /// Receive the original commitment header and its sampled anchor under the expected shape.
    ///
    /// Shape and configuration guards run before reading the frame or drawing its anchor.
    ///
    /// # Errors
    ///
    /// - [`WhirError::Anchoring`] for a configuration that pads: a hiding commitment has no anchor.
    /// - A shape the configuration does not fit, different public constants, or a malformed stream.
    pub fn receive<V: OpeningVerifier<E = E, Root = R, K = K>>(
        v: &mut V,
        log_n: usize,
        n_lanes: usize,
        config: Config,
    ) -> Result<Self, WhirError> {
        if config.padding() > 0 {
            return Err(WhirError::Anchoring);
        }
        check_config_shape(&config, log_n)?;
        let rate = *config.log_inv_rates().first().ok_or(WhirError::CommitmentMismatch)?;
        let record = receive_commitment(v, log_n, config.initial_k(), rate, n_lanes)?;
        Ok(Self {
            binding: Binding::Anchored(record),
            config,
        })
    }

    /// The hiding commitment to a stack of `2^log_n` words, its first `n_lanes` lane blocks committed under `config`.
    ///
    /// The caller has read its root.
    ///
    /// # Errors
    ///
    /// [`WhirError::Anchoring`] for a configuration that does not pad: a plain commitment is received with its anchor.
    pub fn hiding(root: R, log_n: usize, n_lanes: usize, config: Config) -> Result<Self, WhirError> {
        if config.padding() == 0 {
            return Err(WhirError::Anchoring);
        }
        let shape = CommitmentShape {
            log_n,
            log_batch_size: config.initial_k(),
            log_inv_rate: config.log_inv_rates()[0],
            n_lanes,
        };
        Ok(Self {
            binding: Binding::Hiding { root, shape },
            config,
        })
    }

    /// The complete original commitment every opening binds, or none for a hiding commitment.
    pub const fn record(&self) -> Option<&Commitment<E, R, K>> {
        match &self.binding {
            Binding::Anchored(record) => Some(record),
            Binding::Hiding { .. } => None,
        }
    }

    /// The commitment's Merkle root.
    pub const fn root(&self) -> R {
        match &self.binding {
            Binding::Anchored(record) => record.root(),
            Binding::Hiding { root, .. } => *root,
        }
    }

    /// The committed stack's encoding shape.
    pub const fn shape(&self) -> CommitmentShape {
        match &self.binding {
            Binding::Anchored(record) => record.shape(),
            Binding::Hiding { shape, .. } => *shape,
        }
    }

    /// The shape, once it and the record fit the configuration.
    fn checked_shape(&self) -> Result<CommitmentShape, WhirError> {
        let shape = self.shape();
        let record_fits = self
            .record()
            .is_none_or(|record| record.point().len() == shape.log_n && record.valid_context());
        if !shape.valid()
            || self.config.initial_k() != shape.log_batch_size
            || self.config.log_inv_rates().first() != Some(&shape.log_inv_rate)
            || !record_fits
        {
            return Err(WhirError::CommitmentMismatch);
        }
        check_config_shape(&self.config, shape.log_n)?;
        Ok(shape)
    }

    /// Verify an opening of `statement`, as the prover opened it.
    ///
    /// - An anchored commitment's opening checks its complete record frame first.
    /// - It replays the ring switch succinctly and recomputes the target, the anchor's value at the last power.
    /// - The WHIR verifier then evaluates the weight once, at its terminal point.
    ///
    /// The same code runs natively and as the recursion machine's rows.
    ///
    /// The opening observes none of the claims, so the caller must have bound them before it:
    ///
    /// - every claim's value is a prover message or part of the instance,
    /// - every point is an earlier challenge or public.
    ///
    /// A value the prover picks after the batching challenges breaks soundness.
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claims are bound.
    ///
    /// # Errors
    ///
    /// - A record that does not fit the configuration, or a frame that differs from it.
    /// - A region or a claim that is no aligned slice of the committed words.
    /// - The WHIR verifier's refusal.
    pub fn verify<V: OpeningVerifier<E = E, Root = R, K = K>>(
        &self,
        v: &mut V,
        statement: Statement<'_, E>,
    ) -> Result<(), WhirError>
    where
        E: PartialEq,
    {
        let shape = self.checked_shape()?;
        let committed = shape.n_lanes * (1usize << (shape.log_n - shape.log_batch_size));
        statement.check(shape.log_n, committed)?;
        let record = self.record();
        if let Some(record) = record {
            verify_record_binding(v, record)?;
        }
        // The family's challenges, then lambda, as the prover drew them.
        let family = RingFamily::draw(v);
        let lambda = v.verifier_message();
        let m = statement.points.len();
        let lambdas = v.powers(lambda, 1 + m + usize::from(record.is_some()));
        let point_lambdas = &lambdas[1..1 + m];
        let share = family.share(v, statement.rings);

        // The target, recomputed from the claims.
        v.begin_scope(Stage::Target);
        let mut target = share.target(v);
        let mut i = 0;
        while i < m {
            target = v.mul_add(point_lambdas[i], statement.points[i].value(), target);
            i += 1;
        }
        if let Some(record) = record {
            target = v.mul_add(lambdas[1 + m], record.value(), target);
        }
        v.end_scope();

        // The weight at the terminal point: the family's closed form, each point claim's eq, then the anchor's.
        let weight_at = StatementWeight {
            share: &share,
            points: statement.points,
            point_lambdas,
            shape,
            anchor: record.map(|record| (record.point(), lambdas[1 + m])),
        };
        self.verify_whir(v, shape, target, weight_at)
    }

    /// Verify an opening of a weighted claim on a hiding commitment, as the prover opened it.
    ///
    /// The weight's multilinear extension is evaluated once, at the terminal point.
    ///
    /// The opening observes neither the claim's value nor its weight, so the caller must have bound both before it.
    ///
    /// Each call site expects the workspace's `clippy::disallowed_methods` and says where its claim is bound.
    ///
    /// # Errors
    ///
    /// - [`WhirError::Anchoring`] on an anchored commitment, whose openings bind its anchor through [`Self::verify`].
    /// - A weight that is no power of two of committed words.
    /// - The WHIR verifier's refusal.
    pub fn verify_weighted<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        claim: Weighted<'_, V::E>,
    ) -> Result<(), WhirError> {
        if self.record().is_some() {
            return Err(WhirError::Anchoring);
        }
        let shape = self.checked_shape()?;
        let committed = shape.n_lanes << (shape.log_n - shape.log_batch_size);
        let vars = claim.vars(committed).ok_or(WhirError::WeightedClaim)?;
        let weight_at = WeightedAt {
            weight: claim.weight,
            vars,
        };
        self.verify_whir(v, shape, claim.value, weight_at)
    }

    /// The WHIR verifier of this commitment, against a target and the weight's extension at the terminal point.
    fn verify_whir<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        shape: CommitmentShape,
        target: V::E,
        weight_at: impl WeightAt<V>,
    ) -> Result<(), WhirError> {
        v.begin_scope(Stage::Whir);
        let result = crate::whir::verify(
            v,
            &self.config,
            shape.log_n,
            shape.n_lanes,
            target,
            self.root(),
            weight_at,
        );
        v.end_scope();
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::Hash;
    use crate::ring_switch::SliceClaim;
    use crate::ring_switch::tests::s_hat_v_reference;
    use crate::whir::MIN_LOG_N_HIDING;
    use crate::whir::config::tests::{default_config, test_config_for};
    use fiat_shamir::{ProofTranscript, ProverState, SessionId, VerifierState};
    use primitives::multilinear::eq_table;
    use primitives::multilinear::inner_product_base;
    use primitives::test_util::Rng;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;
    use std::ops::Range;

    const DOMAIN: &[u8] = b"stack-open-test";

    impl StackCommitment {
        /// The anchored record, to alter in place.
        fn record_mut(&mut self) -> &mut Commitment {
            match &mut self.binding {
                Binding::Anchored(record) => record,
                Binding::Hiding { .. } => unreachable!("an anchored commitment"),
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

        // A stride or slice width past the word is refused, not wrapped to a small one: `2^32` would read as `0`.
        let wide = |stride_log: usize, point: usize| StackClaim::Strided {
            offset: 0,
            slot: 0,
            stride_log,
            point: vec![F192::ZERO; point],
            value: F192::ZERO,
        };
        for (stride_log, point) in [(1 << 32, 0), (usize::BITS as usize, 0), (usize::MAX, 1)] {
            assert!(matches!(
                check(&[wide(stride_log, point)], &rings),
                Err(WhirError::PointClaim { index: 0 })
            ));
        }
    }

    struct Instance {
        vc: Config,
        log_n: usize,
        n_lanes: usize,
        opening_label: Option<&'static [u8]>,
        header: Option<ProofTranscript>,
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
    fn build_instance(seed: u64) -> Instance {
        build_instance_in_session(seed, false, None)
    }

    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn build_instance_in_session(seed: u64, omit_last_lane: bool, opening_label: Option<&'static [u8]>) -> Instance {
        let log_n = 14usize;
        let pc = test_config_for(log_n);
        let lane_block = 1usize << (log_n - pc.initial_k());
        let n_lanes = (1usize << pc.initial_k()) - usize::from(omit_last_lane);
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qflock_vars = 8usize;
        let qflock_offset = 3 * col_len;
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        while stack.len() < n_lanes * lane_block {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), n_lanes * lane_block);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = eq_table(&low_point);
                let value = inner_product_base(&stack[offset..offset + col_len], &eq);
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

        // Invariant: the residual cube sits entirely above the packed region's coordinates.
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let mut ps = ProverState::new(&SessionId::new(DOMAIN), &0u64);
        let committed = CommittedStack::new(&mut ps, &stack, log_n, pc.clone());
        let header = opening_label.map(|label| {
            let source = std::mem::replace(&mut ps, ProverState::new(&SessionId::new(label), &0u64));
            source.into_proof()
        });
        let statement = Statement {
            points: &point_claims,
            rings: &rings,
        };
        committed.open(&mut ps, &stack, statement);

        Instance {
            vc: pc,
            log_n,
            n_lanes,
            opening_label,
            header,
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
        let label = inst.opening_label.unwrap_or(DOMAIN);
        let mut vs = VerifierState::new(&SessionId::new(label), &0u64, fs);
        let commitment = inst.header.as_ref().map_or_else(
            || StackCommitment::receive(&mut vs, inst.log_n, inst.n_lanes, inst.vc.clone()),
            |header| {
                let mut source = VerifierState::new(&SessionId::new(DOMAIN), &0u64, header);
                StackCommitment::receive(&mut source, inst.log_n, inst.n_lanes, inst.vc.clone())
            },
        );
        let Ok(commitment) = commitment else { return false };
        let statement = Statement {
            points: point_claims,
            rings,
        };
        commitment.verify(&mut vs, statement).is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        // Invariant: an honest opening verifies, and a tampered claim, slice, point or message byte is refused.
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

        // Commitment frames and WHIR scalars are authenticated by the typed route.
        for idx in [17 * 24, inst.fs.narg.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.narg[idx] ^= 1;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.rings, &bad_fs),
                "tampered message byte {idx} accepted"
            );
        }

        // A truncated proof is refused, never a panic.
        let mut short_fs = inst.fs.clone();
        short_fs.narg.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.rings, &short_fs),
            "short proof accepted"
        );
    }

    #[test]
    fn occupied_lanes_open_in_the_original_and_fresh_sessions() {
        for opening_label in [None, Some(b"stack-fresh-session".as_slice())] {
            let inst = build_instance_in_session(2, true, opening_label);
            assert!(!inst.n_lanes.is_power_of_two());
            assert!(verify_instance(&inst, &inst.point_claims, &inst.rings, &inst.fs));
        }
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn a_fresh_opening_binds_the_complete_original_record() {
        const FRESH: &[u8] = b"stack-fresh-record";
        let inst = build_instance_in_session(4, true, Some(FRESH));
        let mut source = VerifierState::new(&SessionId::new(DOMAIN), &0u64, inst.header.as_ref().unwrap());
        let commitment = StackCommitment::receive(&mut source, inst.log_n, inst.n_lanes, inst.vc.clone()).unwrap();
        let statement = Statement {
            points: &inst.point_claims,
            rings: &inst.rings,
        };
        let check = |commitment: &StackCommitment| {
            let mut v = VerifierState::new(&SessionId::new(FRESH), &0u64, &inst.fs);
            commitment.verify(&mut v, statement)
        };
        assert!(check(&commitment).is_ok());

        // A fresh opening session binds its public instance as well as its protocol identity.
        for (session, instance) in [(b"foreign-stack-session".as_slice(), 0u64), (FRESH, 1u64)] {
            let mut v = VerifierState::new(&SessionId::new(session), &instance, &inst.fs);
            assert!(commitment.verify(&mut v, statement).is_err());
        }

        // Same actual root, but another original transcript context.
        let empty = ProverState::new(&SessionId::new(DOMAIN), &0u64).into_proof();
        let mut other = VerifierState::new(&SessionId::new(b"another-original-context"), &0u64, &empty);
        let mut altered = commitment.clone();
        altered.record_mut().context = OpeningVerifier::context(&mut other);
        assert_eq!(altered.root(), commitment.root());
        assert!(matches!(check(&altered), Err(WhirError::CommitmentMismatch)));

        let mut altered = commitment.clone();
        altered.record_mut().point[0] += F192::ONE;
        assert!(matches!(check(&altered), Err(WhirError::CommitmentMismatch)));
        let mut altered = commitment.clone();
        altered.record_mut().value += F192::ONE;
        assert!(matches!(check(&altered), Err(WhirError::CommitmentMismatch)));
        let mut altered = commitment.clone();
        altered.record_mut().shape.n_lanes -= 1;
        assert!(matches!(check(&altered), Err(WhirError::CommitmentMismatch)));

        let mut frame = inst.fs.clone();
        frame.narg[0] ^= 1;
        let mut v = VerifierState::new(&SessionId::new(FRESH), &0u64, &frame);
        assert!(matches!(
            commitment.verify(&mut v, statement),
            Err(WhirError::CommitmentMismatch)
        ));
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's statement is fixed before the transcript: public"
    )]
    fn malformed_metadata_is_refused_before_frame_reads_or_challenges() {
        let inst = build_instance_in_session(5, true, Some(b"metadata-fresh"));
        let mut source = VerifierState::new(&SessionId::new(DOMAIN), &0u64, inst.header.as_ref().unwrap());
        let commitment = StackCommitment::receive(&mut source, inst.log_n, inst.n_lanes, inst.vc.clone()).unwrap();
        let empty = ProverState::new(&SessionId::new(DOMAIN), &0u64).into_proof();
        let pristine_challenge: F192 = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty).verifier_message();
        let statement = Statement {
            points: &inst.point_claims,
            rings: &inst.rings,
        };
        for case in 0..5 {
            let mut malformed = commitment.clone();
            match case {
                0 => malformed.record_mut().shape.log_n = usize::MAX,
                1 => malformed.record_mut().shape.n_lanes = usize::MAX,
                2 => {
                    malformed.record_mut().point.pop();
                }
                3 => malformed.record_mut().context.pending_bytes = 65,
                _ => malformed.record_mut().context.pending[7] = Some(F64::ONE),
            }
            let mut v = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty);
            assert!(matches!(
                malformed.verify(&mut v, statement),
                Err(WhirError::CommitmentMismatch)
            ));
            assert_eq!(v.verifier_message::<F192>(), pristine_challenge);
        }

        let malformed = StackClaim::Strided {
            offset: 0,
            slot: 0,
            stride_log: usize::MAX,
            point: vec![F192::ZERO],
            value: F192::ZERO,
        };
        let mut v = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty);
        assert!(matches!(
            commitment.verify(
                &mut v,
                Statement {
                    points: &[malformed],
                    rings: &inst.rings,
                }
            ),
            Err(WhirError::PointClaim { index: 0 })
        ));
        assert_eq!(v.verifier_message::<F192>(), pristine_challenge);

        let mut malformed_rings = inst.rings.clone();
        malformed_rings[0].claims[0].s_hat_v.pop();
        let mut v = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty);
        assert!(matches!(
            commitment.verify(
                &mut v,
                Statement {
                    points: &inst.point_claims,
                    rings: &malformed_rings,
                }
            ),
            Err(WhirError::Region { index: 0 })
        ));
        assert_eq!(v.verifier_message::<F192>(), pristine_challenge);

        for (log_n, lanes) in [(usize::MAX, 1), (inst.log_n, 0), (inst.log_n, usize::MAX)] {
            let mut v = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty);
            assert!(StackCommitment::receive(&mut v, log_n, lanes, inst.vc.clone()).is_err());
            assert_eq!(v.verifier_message::<F192>(), pristine_challenge);
        }
    }

    #[test]
    fn the_supported_anchor_matches_the_actual_mle_and_terminal_weight() {
        use crate::whir::anchor::anchor_value;
        let mut rng = Rng::new(0xA11CE);
        let log_rows = 3;
        let shape = CommitmentShape {
            log_n: 9,
            log_batch_size: 6,
            log_inv_rate: 1,
            n_lanes: 1,
        };
        for lanes in [1, 3, 17, 33, 64] {
            let stack: Vec<F64> = (0..lanes << log_rows).map(|_| F64(rng.next_u64())).collect();
            for edge in [None, Some(F192::ZERO), Some(F192::ONE)] {
                let mut point = rng.ext_vec(shape.log_n);
                if let Some(edge) = edge {
                    point[shape.log_n - 1] = edge;
                }
                let x = rng.ext_vec(shape.log_n);
                let eq_bits = |i: usize, point: &[F192]| {
                    point.iter().enumerate().fold(F192::ONE, |acc, (j, &r)| {
                        acc * if (i >> j) & 1 == 0 { F192::ONE + r } else { r }
                    })
                };
                let value = stack
                    .iter()
                    .enumerate()
                    .fold(F192::ZERO, |sum, (i, &v)| sum + eq_bits(i, &point).mul_base(v));
                assert_eq!(anchor_value(&stack, log_rows, &point), value);
                let terminal = (0..stack.len()).fold(F192::ZERO, |sum, i| sum + eq_bits(i, &point) * eq_bits(i, &x));
                assert_eq!(
                    anchor_eq_at(
                        &mut Native,
                        CommitmentShape {
                            n_lanes: lanes,
                            ..shape
                        },
                        &point,
                        &x
                    ),
                    terminal
                );
            }
        }
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
        let value = inner_product_base(&stack[..1 << 12], &eq);
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

        let mut ps = ProverState::new(&SessionId::new(DOMAIN), &0u64);
        let committed = CommittedStack::new(&mut ps, &stack, log_n, pc.clone());
        let ring = RingSwitch {
            offset: qflock_offset,
            qflock_vars,
            claims,
        };
        let statement = |ring| Statement {
            points: &point_claims,
            rings: std::slice::from_ref(ring),
        };
        committed.open(&mut ps, &stack, statement(&ring));
        let fs = ps.into_proof();

        let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &fs);
        let commitment = StackCommitment::receive(&mut vs, log_n, 1 << pc.initial_k(), pc).unwrap();
        assert!(
            commitment.verify(&mut vs, statement(&ring)).is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_ring = ring.clone();
        bad_ring.claims[0].s_hat_v[7] += F192::ONE;
        let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &fs);
        let _ = StackCommitment::receive(
            &mut vs,
            log_n,
            1 << commitment.config.initial_k(),
            commitment.config.clone(),
        )
        .unwrap();
        assert!(
            commitment.verify(&mut vs, statement(&bad_ring)).is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }

    /// A statement on the data lanes of a hiding commitment.
    struct HidingStatement {
        log_n: usize,
        config: Config,
        data_lanes: usize,
        stack: Vec<F64>,
        points: Vec<StackClaim>,
        rings: Vec<RingSwitch>,
    }

    impl HidingStatement {
        fn new(log_inv_rate: usize, data_lanes: usize, seed: u64) -> Self {
            let log_n = MIN_LOG_N_HIDING;
            let config = Config::hiding(log_n, log_inv_rate).unwrap();
            let lane_vars = log_n - config.initial_k();
            let mut rng = Rng::new(seed);

            // The data lanes, then room for the zero lanes and the random group.
            let mut stack: Vec<F64> = (0..data_lanes << lane_vars).map(|_| F64(rng.next_u64())).collect();
            stack.resize(Config::hiding_lanes(data_lanes) << lane_vars, F64::ZERO);

            // A ring-switched claim on lanes 0 and 1, a point claim on lane 2.
            let qflock_vars = lane_vars + 1;
            let suffix_point = rng.ext_vec(qflock_vars);
            let s_hat_v = s_hat_v_reference(&stack[..1 << qflock_vars], &suffix_point);
            let rings = vec![RingSwitch {
                offset: 0,
                qflock_vars,
                claims: vec![SliceClaim { suffix_point, s_hat_v }],
            }];
            let offset = 2 << lane_vars;
            let low_point = rng.ext_vec(lane_vars);
            let value = inner_product_base(&stack[offset..offset + (1 << lane_vars)], &eq_table(&low_point));
            let points = vec![StackClaim::Point {
                offset,
                low_point,
                value,
            }];
            assert!(data_lanes > 2, "the claims sit on three data lanes");
            Self {
                log_n,
                config,
                data_lanes,
                stack,
                points,
                rings,
            }
        }

        const fn statement(&self) -> Statement<'_> {
            Statement {
                points: self.points.as_slice(),
                rings: self.rings.as_slice(),
            }
        }

        /// Commit with the randomness of `seed` and open; `forge` may change the padding the prover folds.
        #[expect(
            clippy::disallowed_methods,
            reason = "the test's statement is fixed before the transcript: public"
        )]
        fn prove(&self, seed: u64, forge: impl FnOnce(&mut Vec<F64>)) -> (Hash, ProofTranscript) {
            let mut stack = self.stack.clone();
            let mut rng = ChaCha20Rng::seed_from_u64(seed);
            let mut committed = CommittedStack::new_hiding(&mut stack, self.log_n, self.config.clone(), &mut rng);
            forge(&mut committed.data.pads);
            // A zero-knowledge proof's opening starts hidden: zero keys leave the values as they are.
            let mut ps = ProverState::new(&SessionId::new(DOMAIN), &0u64);
            ps.set_keys(vec![F192::ZERO; 64]);
            ps.set_hidden(true);
            committed.open(&mut ps, &stack, self.statement());
            (committed.root(), ps.into_proof())
        }

        #[expect(
            clippy::disallowed_methods,
            reason = "the test's statement is fixed before the transcript: public"
        )]
        fn verify(&self, root: Hash, fs: &ProofTranscript) -> Result<(), WhirError> {
            let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, fs);
            vs.set_hidden(true);
            let n_lanes = Config::hiding_lanes(self.data_lanes);
            let commitment: StackCommitment = StackCommitment::hiding(root, self.log_n, n_lanes, self.config.clone())?;
            commitment.verify(&mut vs, self.statement())
        }

        /// The byte range of the `i`-th scalar the opening sends: before the reveal, it sends scalars alone.
        const fn scalar(i: usize) -> Range<usize> {
            24 * i..24 * (i + 1)
        }

        /// The revealed claim's index: after the first round's message and the lane rounds' but the last, two scalars each.
        const fn revealed_at(&self) -> usize {
            2 * self.config.initial_k()
        }
    }

    /// A proof with one scalar changed: its lowest bit flipped.
    fn bump(fs: &ProofTranscript, at: Range<usize>) -> ProofTranscript {
        let mut forged = fs.clone();
        forged.narg[at.start] ^= 1;
        forged
    }

    #[test]
    fn a_hiding_opening_verifies_and_binds_what_it_reveals() {
        // Small and large data, at rate 1/2 and 1/4; the random group sits at the next multiple of four.
        for (log_inv_rate, data_lanes) in [(1usize, 3usize), (1, 60), (2, 37)] {
            let st = HidingStatement::new(log_inv_rate, data_lanes, 0x41D + data_lanes as u64);
            let (root, fs) = st.prove(7, |_| {});
            let what = format!("rate 2^-{log_inv_rate}, {data_lanes} data lanes");
            assert_eq!(st.verify(root, &fs), Ok(()), "honest opening, {what}");

            // The revealed claim must be the one the lane rounds reach.
            let claim = HidingStatement::scalar(st.revealed_at());
            assert_eq!(
                st.verify(root, &bump(&fs, claim)),
                Err(WhirError::RevealedClaim),
                "{what}"
            );

            // Each end of the padding's fold `g_1`, which follows the claim.
            let k = st.config.padding();
            for j in [1, k] {
                let at = HidingStatement::scalar(st.revealed_at() + j);
                assert!(st.verify(root, &bump(&fs, at)).is_err(), "tampered g_1, {what}");
            }

            // Mutation: the prover folds a padding other than the committed one.
            //
            //     committed pads  p
            //     folded pads     p + e_0   (lane 0, coefficient 0)
            //     -> g_1 is consistent with the forged pads, and level 0's correction misses the codeword
            let (root, fs) = st.prove(7, |pads| pads[0] += F64::ONE);
            assert!(st.verify(root, &fs).is_err(), "g_1 of other pads, {what}");
        }
    }

    #[test]
    fn a_hiding_opening_is_a_function_of_its_randomness() {
        let st = HidingStatement::new(1, 6, 0x5EED);
        let (root, fs) = st.prove(1, |_| {});
        assert_eq!(st.prove(1, |_| {}), (root, fs.clone()), "same randomness, same proof");

        // Other randomness: another valid proof, whose revealed claim and padding fold share no scalar with the first.
        let (other_root, other_fs) = st.prove(2, |_| {});
        assert_eq!(st.verify(other_root, &other_fs), Ok(()));
        for j in 0..=st.config.padding() {
            let at = HidingStatement::scalar(st.revealed_at() + j);
            assert_ne!(fs.narg[at.clone()], other_fs.narg[at], "scalar {j} after the lane fold");
        }
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's weight and value are fixed before the transcript: public"
    )]
    fn a_weighted_opening_binds_its_value() {
        // A hiding stack of one data lane, then the zero lanes and the random group: eight lanes.
        let log_n = MIN_LOG_N_HIDING;
        let config = Config::hiding(log_n, 1).unwrap();
        let lane = 1usize << (log_n - config.initial_k());
        let mut rng = Rng::new(0x3E1);
        let mut stack: Vec<F64> = (0..lane).map(|_| F64(rng.next_u64())).collect();
        stack.resize(Config::hiding_lanes(1) * lane, F64::ZERO);
        let committed =
            CommittedStack::new_hiding(&mut stack, log_n, config.clone(), &mut ChaCha20Rng::seed_from_u64(1));

        // A weight on the data lane alone, word by word, and its sum.
        let weight = rng.ext_vec(lane);
        let value = inner_product_base(&stack[..lane], &weight);
        let mut ps = ProverState::new(&SessionId::new(DOMAIN), &0u64);
        committed.open_weighted(&mut ps, &stack, Weighted { weight: &weight, value });
        let fs = ps.into_proof();

        let check = |weight: &[F192], value: F192| {
            let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &fs);
            let commitment: StackCommitment =
                StackCommitment::hiding(committed.root(), log_n, Config::hiding_lanes(1), config.clone())?;
            commitment.verify_weighted(&mut vs, Weighted { weight, value })
        };
        assert_eq!(check(&weight, value), Ok(()));

        // Mutation: the value off by one, which the terminal check refuses.
        assert!(check(&weight, value + F192::ONE).is_err());

        // Mutation: a weight of three words, no power of two, refused before any read.
        assert_eq!(check(&weight[..3], value), Err(WhirError::WeightedClaim));
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test's weight and value are fixed before the transcript: public"
    )]
    fn anchored_and_hiding_commitments_refuse_each_other() {
        // A hiding configuration is never received with an anchor, and a plain one never without.
        let log_n = MIN_LOG_N_HIDING;
        let hiding = Config::hiding(log_n, 1).unwrap();
        let plain = Config::for_rate(log_n, 1).unwrap();
        let empty = ProverState::new(&SessionId::new(DOMAIN), &0u64).into_proof();
        let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &empty);
        let refused = StackCommitment::receive(&mut vs, log_n, 8, hiding);
        assert!(matches!(refused, Err(WhirError::Anchoring)));
        assert!(matches!(
            StackCommitment::<F192, Hash, F64>::hiding([0; 32], log_n, 8, plain.clone()),
            Err(WhirError::Anchoring)
        ));

        // An anchored stack is opened through its statement, never by a weighted claim.
        let lane = 1usize << (log_n - plain.initial_k());
        let mut rng = Rng::new(0xA7C);
        let stack: Vec<F64> = (0..lane).map(|_| F64(rng.next_u64())).collect();
        let mut ps = ProverState::new(&SessionId::new(DOMAIN), &0u64);
        let committed = CommittedStack::new(&mut ps, &stack, log_n, plain.clone());
        assert!(committed.record().is_some());
        let fs = ps.into_proof();
        let mut vs = VerifierState::new(&SessionId::new(DOMAIN), &0u64, &fs);
        let commitment = StackCommitment::receive(&mut vs, log_n, 1, plain).unwrap();
        let weight = rng.ext_vec(lane);
        let value = inner_product_base(&stack, &weight);
        assert_eq!(
            commitment.verify_weighted(&mut vs, Weighted { weight: &weight, value }),
            Err(WhirError::Anchoring)
        );
    }
}
