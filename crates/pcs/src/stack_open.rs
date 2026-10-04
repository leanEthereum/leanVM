// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`], which only encodes and only transmits the lane blocks
//! that carry data: every claim lives inside them and the weight is zero past
//! them), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a `Point` claim's weight is
//!   `eq(low_point, .)` supported on `[offset, offset + 2^|low_point|)`; a
//!   `Strided` claim freezes the low `stride_log` in-block coords to `slot`'s
//!   bits, so its weight is nonzero only at `offset + slot + j * 2^stride_log`),
//! - **ring-switched claims** ([`RingSwitchOpen`], one per packed sub-block, each
//!   circuit committing its own): bit-MLE evaluation claims
//!   on the packed sub-block `q_flock = stack[offset .. offset + 2^qflock_vars]`,
//!   combined into ONE family, whose 64 slices are the claims' slices weighted by
//!   powers of one challenge `gamma_rs`, and ring-switched once to an inner-product
//!   claim `<q, rs_eq_ind> = target` against the transparent E-valued weight
//!   `rs_eq_ind`, claim `j` contributing `Phi(gamma_rs^j·eq(r_j, .))` on its sub-block
//!   (doc `leanvm` Annex A, `rs:family`). The claims' points need not be related.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring switch succinctly (the family's target, with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and the family's weight.
//!
//! ## Transcript order (identical on both sides)
//!
//! Sample the family's challenge `gamma_rs`, then the shared linear map, then one batching challenge for the family and the point claims, then run WHIR. The caller already bound each claim's slices and value through the transcript, so none is observed again here.
//!
//! ## The combined weight
//!
//! With `sel = offset >> qflock_vars` the selector coords of a q_flock slice,
//! the lifted weight at a full-stack point `x = (x_lo, x_hi)` (split at
//! `qflock_vars`, LSB-first) is, for one such slice (several add up, each with
//! its own selector, its claims taking their own powers of `gamma_rs`),
//!
//! ```text
//! b(x) = eq(sel, x_hi) * sum_j MLE(Phi(gamma_rs^j * eq(r_j, .)))(x_lo)
//!      + sum_i lambda^(1 + i) * eq(claim_i, x)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each claim's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).
//!
//! The family takes `lambda^0` and the point claims the next powers of ONE
//! challenge, as the table sumcheck's xi ranges do (the batching step of `thm:rbr`).
//! `lambda` is drawn after the map, so the family's error is fixed by then and is the
//! constant term of the batched error, which is what lets it take `lambda^0 = 1`.

use super::pack::PACKING_WIDTH;
use super::ring_switch;
use super::ring_switch::RsEqQuery;
use super::whir::{Basis, ProverConfig, ProverData, VerifierConfig, WhirError, recursive_verifier_with_basis_succinct};
use crate::merkle::Hash;
use basis::StackWeight;
use fiat_shamir::transcript::{Challenger, Receiver, Transmitter};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_eval;
use std::cmp::Reverse;

mod basis;

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// An owning point claim folded into the stacked mixed opening.
///
/// Its point and value are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim<E = F192> {
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point { offset: usize, low_point: Vec<E>, value: E },
    /// A boolean-selector claim on a packed column: the low `stride_log`
    /// in-block coords are frozen to `slot`'s bits (so the weight is nonzero
    /// only at `offset + slot + j * 2^stride_log`) and `point` is the high
    /// part. Equivalent to a `Point` with `low_point = slot_bits ++ point`,
    /// folded in `O(2^|point|)` instead of `O(2^(stride_log + |point|))`.
    /// `offset` must be a multiple of `2^(stride_log + |point|)` and
    /// `slot < 2^stride_log`.
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

    /// The b_stack range the claim's weight is supported on.
    ///
    /// Every range is an aligned dyadic interval (the offset asserts below), so two of them are nested or disjoint and never partially overlap.
    /// `Strided` reports its whole block rather than the strided positions inside it.
    /// That is conservative in the direction that matters: it only ever makes a later claim accumulate.
    pub fn range(&self) -> (usize, usize) {
        match self {
            Self::Point { offset, low_point, .. } => (*offset, *offset + (1usize << low_point.len())),
            Self::Strided {
                offset,
                stride_log,
                point,
                ..
            } => (*offset, *offset + (1usize << (stride_log + point.len()))),
        }
    }
}

/// One ring-switched claim on the q_flock sub-block: the 64 bit-slice MLEs of
/// q_flock at `suffix_point` (see [`super::ring_switch`]), which has
/// `qflock_vars` coords.
///
/// `s_hat_v` holds those 64 values. The caller transmits and checks them itself
/// (flock sends its family and pins it in its own lincheck terminal), so this
/// layer only binds them to the commitment. `None` asks the prover to fold the slices from the witness:
/// no transcript sees them then, so the verifier must hold slices bound some other way before the opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Option<Vec<F192>>,
}

/// Prover-side bundle of the ring-switched claims discharged in the same
/// stacked opening as the [`StackClaim`]s. Each claim may carry its
/// precomputed `s_hat_v`.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    /// q_flock's offset inside the committed stack; must be a multiple of
    /// `2^qflock_vars` (an aligned slice).
    pub offset: usize,
    /// log2 of q_flock's length in F64 words; the opener slices
    /// `q_flock = stack[offset .. offset + 2^qflock_vars]` (no separate copy).
    pub qflock_vars: usize,
    pub claims: Vec<RingSwitchClaim>,
}

/// A verifier claim whose slices were transmitted and checked by the caller.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Copy, Debug)]
pub struct RingSwitchVerifyClaim<'a, E = F192> {
    pub suffix_point: &'a [E],
    pub s_hat_v: &'a [E; PACKING_WIDTH],
}

/// Verifier inputs borrowed from the upstream reduction.
#[derive(Clone, Debug)]
pub struct RingSwitchVerify<'a, E = F192> {
    pub offset: usize,
    pub qflock_vars: usize,
    pub claims: Vec<RingSwitchVerifyClaim<'a, E>>,
}

// ---------------------------------------------------------------------------
// Shared claim folding / evaluation
// ---------------------------------------------------------------------------

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of
/// the full stack cube. A `Point`'s full point is `[low_point, sel_bits]`, a
/// `Strided`'s is `[slot_bits, point, sel_bits]`; neither is materialized.
fn stack_claim_eq_at(claim: &StackClaim, x: &[F192]) -> F192 {
    match claim {
        StackClaim::Point { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = eq_eval(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F192::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_flock claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored in
/// [`ProverData`]): the `2^log_n`-word stack truncated to the lane blocks that
/// carry data, so every claim must live inside it and the padding past it is
/// exactly the weight's zero region. `config.initial_k` / `config.log_inv_rates[0]`
/// must match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut impl Transmitter,
    log_n: usize,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    rings: &[RingSwitchOpen],
) {
    for ring in rings {
        let qflock_len = 1usize << ring.qflock_vars;
        assert!(
            ring.offset.is_multiple_of(qflock_len),
            "q_flock offset must be 2^qflock_vars-aligned"
        );
        assert!(
            ring.offset + qflock_len <= stack.len(),
            "q_flock slice must fit inside the stack"
        );
    }
    assert!(
        point_claims.iter().all(|c| c.range().1 <= stack.len()),
        "every claim must live inside the committed lanes"
    );
    let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Every claim's slices (the caller bound them upstream), combined into the
    //    family by powers of one challenge, then one shared linear map.
    let mut points = Vec::with_capacity(n_rs);
    let mut slices = Vec::with_capacity(n_rs);
    for ring in rings {
        let qflock = &stack[ring.offset..ring.offset + (1usize << ring.qflock_vars)];
        for claim in &ring.claims {
            assert_eq!(
                claim.suffix_point.len(),
                ring.qflock_vars,
                "ring-switch suffix point must have qflock_vars coords"
            );
            points.push(claim.suffix_point.as_slice());
            slices.push(
                claim
                    .s_hat_v
                    .clone()
                    .unwrap_or_else(|| ring_switch::slices_at(qflock, &claim.suffix_point)),
            );
        }
    }
    let family = RingFamily::sample(ps);
    let coordinate_weights = family.coordinate_weights();

    // 2. The ONE batching challenge: the family takes its first power, the point claims the rest. Nothing is
    //    observed first: every claim value reached the caller through a binding stream read, so the challenge
    //    already depends on all of them (`leanvm_core::pcs::open`).
    let lambdas = powers(ps.sample(), 1 + point_claims.len());
    let lambdas_pd = &lambdas[1..];
    let rs_outputs: Vec<_> = (points.iter().zip(powers(family.gamma_rs(), n_rs)))
        .map(|(point, scale)| ring_switch::deferred_weight(point, scale, &coordinate_weights))
        .collect();
    drop(span);

    // 3. Combined target and lifted stack weight b_stack: each claim's share of
    //    the family's weight scattered at its q_flock slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let target = family.target(slices.iter().map(Vec::as_slice))
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());

    // The lifted weight is never stored.
    //
    //     first pass:  each chunk is filled, then feeds the first lane rounds' sums while hot
    //     first fold:  each chunk is filled again, then folded by those rounds' challenges
    //
    // Filling costs less than writing the weight out and reading it back.
    let lane_block = 1usize << (log_n - config.initial_k());
    let weight = StackWeight::new(stack.len(), lane_block, point_claims, lambdas_pd, rings, &rs_outputs);
    let fill = |start: usize, dst: &mut [F192]| weight.fill(start, dst);
    let initial = tracing::info_span!("Basis")
        .in_scope(|| super::whir::initial_rounds(stack, lane_block, config.initial_k(), &Basis::Virtual(&fill)));

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    super::whir::recursive_prover_with_prepared_basis(
        config,
        log_n,
        stack,
        Basis::Virtual(&fill),
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        Some(initial),
        ps,
    );
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_whir_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct WHIR verifier with one terminal evaluation of the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::whir::Commitment::root`]).
pub fn verify_opening_batch_mixed_whir_stacked(
    vs: &mut impl Receiver,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    root: &Hash,
    point_claims: &[StackClaim],
    rings: &[RingSwitchVerify<'_>],
) -> Result<(), WhirError> {
    let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    for ring in rings {
        assert!(ring.qflock_vars <= log_n);
        assert!(
            ring.offset.is_multiple_of(1usize << ring.qflock_vars),
            "q_flock offset must be 2^qflock_vars-aligned"
        );
        for claim in &ring.claims {
            assert_eq!(claim.suffix_point.len(), ring.qflock_vars);
        }
        // Every claim's support must lie inside the cube, or its selector coords would
        // run off the end of the fold point (mirror of the opener's own bound).
        assert!(ring.offset + (1usize << ring.qflock_vars) <= 1usize << log_n);
    }
    assert!(
        point_claims.iter().all(|c| c.range().1 <= 1usize << log_n),
        "every claim must live inside the committed cube"
    );

    // 1. The family: every claim arrives with its 64 slices, bound upstream by the
    //    caller, so nothing is read here; they combine by powers of one challenge.
    //    Then sample one shared map.
    let family = RingFamily::sample(vs);

    // 2. The one batching challenge (see the opener: the caller already bound the claim values),
    //    the family taking its first power.
    let lambdas = powers(vs.sample(), 1 + point_claims.len());
    let lambdas_pd = &lambdas[1..];
    let slices = rings
        .iter()
        .flat_map(|ring| &ring.claims)
        .map(|claim| claim.s_hat_v.as_slice());
    let mut target = family.target(slices);
    for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
        target += *g * claim.value();
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let eval_b_at = |x: &[F192]| -> F192 {
        let point_part = (point_claims.iter().zip(lambdas_pd)).fold(F192::ZERO, |acc, (claim, &lambda)| {
            acc + lambda * stack_claim_eq_at(claim, x)
        });
        family.weight(rings, x) + point_part
    };

    recursive_verifier_with_basis_succinct(config, log_n, n_lanes, target, root, eval_b_at, vs)
}

/// The ring switch's one family per opening: claim `j` scaled by `gamma_rs^j`, then one map `Phi` for all.
///
/// Both sides draw `gamma_rs` once every claim's slices are bound, then the map's six challenges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RingFamily {
    gamma_rs: F192,
    map_challenges: [F192; ring_switch::COMPOSITION_SHIFTS.len()],
}

impl RingFamily {
    /// The family at its challenges.
    pub const fn new(gamma_rs: F192, map_challenges: [F192; ring_switch::COMPOSITION_SHIFTS.len()]) -> Self {
        Self {
            gamma_rs,
            map_challenges,
        }
    }

    /// Draw the family's challenges: `gamma_rs`, then the map's.
    pub fn sample(ch: &mut impl Challenger) -> Self {
        let gamma_rs = ch.sample();
        Self::new(gamma_rs, ring_switch::sample_map_challenges(ch))
    }

    /// The challenge `gamma_rs` whose powers scale the claims.
    pub const fn gamma_rs(&self) -> F192 {
        self.gamma_rs
    }

    /// The map's weight on each of the 192 coordinates.
    fn coordinate_weights(&self) -> Vec<F192> {
        ring_switch::build_coordinate_weights(&self.map_challenges)
    }

    /// The family's target `sum_i x^i Phi(s_i)`, its slices `s_i = sum_j gamma_rs^j s_{j,i}` over the claims in order.
    ///
    /// # Panics
    ///
    /// If a claim does not carry 64 slices.
    pub fn target<'s>(&self, slices: impl IntoIterator<Item = &'s [F192]>) -> F192 {
        let mut family = [F192::ZERO; PACKING_WIDTH];
        let mut scale = F192::ONE;
        for claim in slices {
            assert_eq!(claim.len(), PACKING_WIDTH, "a ring-switched claim has 64 slices");
            for (f, &s) in family.iter_mut().zip(claim) {
                *f += scale * s;
            }
            scale *= self.gamma_rs;
        }
        ring_switch::verify_finish(&family, &self.coordinate_weights())
    }

    /// The family's weight at a point `x` of the stack cube: `sum_j eq(sel_j, x_hi) MLE(Phi(gamma_rs^j eq(r_j, .)))(x_lo)`.
    ///
    /// Claim `j` is the `j`-th claim across the regions in order, `sel_j` its region's selector bits.
    ///
    /// - The Frobenius moves onto `x`, so one precomputed query serves every claim.
    /// - Claims whose points are prefixes of one another share one pass over the longest.
    /// - The claims of one region add their scaled terms and close once.
    ///
    /// # Panics
    ///
    /// If a region or a claim's point is longer than `x`.
    pub fn weight(&self, rings: &[RingSwitchVerify<'_>], x: &[F192]) -> F192 {
        let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
        let scales = powers(self.gamma_rs, n_rs);
        let max_qflock_vars = rings.iter().map(|ring| ring.qflock_vars).max().unwrap_or(0);
        let rs_query = RsEqQuery::new(&self.map_challenges, &x[..max_qflock_vars]);
        let mut terms = vec![[F192::ZERO; ring_switch::LINEARIZED_TERMS]; rings.len()];
        for group in PrefixGroup::of(rings) {
            let at = ring_switch::rs_eq_prefix_terms(group.lead, &rs_query, &group.lengths);
            for member in group.members {
                for (term, &t) in terms[member.ring].iter_mut().zip(&at[member.length]) {
                    *term += scales[member.claim] * t;
                }
            }
        }
        rings.iter().zip(&terms).fold(F192::ZERO, |acc, (ring, terms)| {
            let sel = ring.offset >> ring.qflock_vars;
            let sel_eq = (x[ring.qflock_vars..].iter().enumerate()).fold(F192::ONE, |e, (k, &xi)| {
                e * if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi }
            });
            acc + sel_eq * ring_switch::close_rs_eq(terms)
        })
    }
}

/// Ring claims whose suffix points are all prefixes of the longest, `lead`.
struct PrefixGroup<'a> {
    lead: &'a [F192],
    /// The distinct prefix lengths its claims sit at.
    lengths: Vec<usize>,
    members: Vec<PrefixMember>,
}

/// One claim of a prefix group.
#[derive(Clone, Copy, Debug)]
struct PrefixMember {
    /// Its index across every ring, which picks its scale.
    claim: usize,
    /// Its ring.
    ring: usize,
    /// Its entry in the group's lengths.
    length: usize,
}

impl<'a> PrefixGroup<'a> {
    /// Every ring claim in a group whose lead point it is a prefix of, longest points first.
    fn of(rings: &[RingSwitchVerify<'a>]) -> Vec<Self> {
        let mut claims: Vec<(usize, usize, &'a [F192])> = rings
            .iter()
            .enumerate()
            .flat_map(|(r, ring)| ring.claims.iter().map(move |claim| (r, claim.suffix_point)))
            .enumerate()
            .map(|(i, (r, point))| (i, r, point))
            .collect();
        claims.sort_by_key(|&(_, _, point)| Reverse(point.len()));
        let mut groups: Vec<Self> = Vec::new();
        for (claim, ring, point) in claims {
            let g = groups
                .iter()
                .position(|g| g.lead.starts_with(point))
                .unwrap_or_else(|| {
                    groups.push(Self {
                        lead: point,
                        lengths: Vec::new(),
                        members: Vec::new(),
                    });
                    groups.len() - 1
                });
            let group = &mut groups[g];
            let length = group.lengths.iter().position(|&n| n == point.len()).unwrap_or_else(|| {
                group.lengths.push(point.len());
                group.lengths.len() - 1
            });
            group.members.push(PrefixMember { claim, ring, length });
        }
        groups
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::fold_1b_rows;
    use crate::whir::{INITIAL_BASIS_CHUNK, commit, inner_product_base_ext};
    use crate::whir_config::tests::{default_config, test_config_for};
    use basis::StackWeight;
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    const DOMAIN: &[u8] = b"stack-open-test";

    #[test]
    fn fused_basis_matches_dense_weights() {
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes) in [(6usize, 1usize), (6, 3), (10, 15), (10, 37)] {
            let lane_block = 1 << lane_vars;
            let stack: Vec<F64> = (0..lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let qflock_vars = lane_vars + usize::from(lanes > 1);
            let qflock_len = 1 << qflock_vars;
            let offset = if stack.len() >= 2 * qflock_len { qflock_len } else { 0 };
            let ring = RingSwitchOpen {
                offset,
                qflock_vars,
                claims: (0..2)
                    .map(|_| RingSwitchClaim {
                        suffix_point: rng.ext_vec(qflock_vars),
                        s_hat_v: None,
                    })
                    .collect(),
            };
            let coordinates = rng.ext_vec(192);
            let rs_outputs: Vec<_> = (ring.claims.iter())
                .map(|claim| ring_switch::deferred_weight(&claim.suffix_point, rng.ext(), &coordinates))
                .collect();
            let mut claims: Vec<_> = [
                (offset, qflock_vars),
                ((lanes - 1) * lane_block, lane_vars),
                (8, 3),
                (0, 0),
            ]
            .into_iter()
            .map(|(offset, vars)| StackClaim::Point {
                offset,
                low_point: rng.ext_vec(vars),
                value: rng.ext(),
            })
            .collect();
            for stride_log in [0, 1, 3, qflock_vars - 1, qflock_vars] {
                claims.push(StackClaim::Strided {
                    offset,
                    slot: (1 << stride_log) - 1,
                    stride_log,
                    point: rng.ext_vec(qflock_vars - stride_log),
                    value: rng.ext(),
                });
            }
            let lambdas = rng.ext_vec(claims.len());
            // Oracle: the dense weight written out naively, one eq entry at a
            // time, so it shares no code with the fused build under test.
            let mut expected = vec![F192::ZERO; stack.len()];
            ring_switch::combine_deferred_chunk(&rs_outputs, 0, &mut expected[offset..offset + qflock_len]);
            for (claim, &lambda) in claims.iter().zip(&lambdas) {
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
                    expected[base + (j << stride_log)] += w;
                }
            }
            // The weight, filled chunk by chunk as the opening reads it.
            let weight = StackWeight::new(
                stack.len(),
                lane_block,
                &claims,
                &lambdas,
                std::slice::from_ref(&ring),
                &rs_outputs,
            );
            let chunk = lane_block.min(INITIAL_BASIS_CHUNK);
            let mut actual = vec![F192::ZERO; stack.len()];
            for (i, out) in actual.chunks_exact_mut(chunk).enumerate() {
                weight.fill(i * chunk, out);
            }
            assert_eq!(actual, expected, "lane_vars={lane_vars}, lanes={lanes}");
        }
    }

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        rings: Vec<RingSwitchOpen>,
        /// The verifier's copy of each ring's one claim.
        ring_verify: Vec<RingSwitchClaim>,
        fs: ProofTranscript,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_flock region (a random bit-witness packed by pack) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_flock, one
    /// ring-switched claim with plain eq prefix weights, and on the filler past
    /// it, rings whose points are prefixes of its point (two of one length),
    /// sharing its pass, and one whose point is not.
    ///
    /// q_flock is kept SMALL (2^8 words) so the succinct verifier's residual
    /// cube sits entirely above the q_flock coords (the production regime:
    /// shared tensor prefix folded once, y coords all selector-indicator,
    /// nonempty E-valued selector prefix from ris); the crossing regime is
    /// exercised by `stacked_open_residual_crosses_qflock`.
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

        // One strided claim into the q_flock region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
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
        let rings: Vec<RingSwitchOpen> = regions
            .iter()
            .map(|(offset, suffix_point)| RingSwitchOpen {
                offset: *offset,
                qflock_vars: suffix_point.len(),
                claims: vec![RingSwitchClaim {
                    suffix_point: suffix_point.clone(),
                    // Exercise the fold path (no precompute).
                    s_hat_v: None,
                }],
            })
            .collect();
        // The verifier's copy of the same claims: the slices ride the statement,
        // bound by the caller, as flock binds its family.
        let ring_verify = regions
            .iter()
            .map(|(offset, suffix_point)| RingSwitchClaim {
                suffix_point: suffix_point.clone(),
                s_hat_v: Some(fold_1b_rows(
                    &stack[*offset..*offset + (1 << suffix_point.len())],
                    &eq_table(suffix_point),
                )),
            })
            .collect();

        let pc = test_config_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_flock coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let mut ps = ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &rings);

        Instance {
            vc: pc,
            log_n,
            root: cm.root,
            point_claims,
            rings,
            ring_verify,
            fs: ps.into_proof(),
        }
    }

    fn verifier_claims(claims: &[RingSwitchClaim]) -> Vec<RingSwitchVerifyClaim<'_>> {
        claims
            .iter()
            .map(|claim| RingSwitchVerifyClaim {
                suffix_point: &claim.suffix_point,
                s_hat_v: claim.s_hat_v.as_deref().unwrap().try_into().unwrap(),
            })
            .collect()
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        ring_claims: &[RingSwitchClaim],
        fs: &ProofTranscript,
    ) -> bool {
        let rings: Vec<RingSwitchVerify<'_>> = (inst.rings.iter().zip(ring_claims))
            .map(|(ring, claim)| RingSwitchVerify {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: verifier_claims(std::slice::from_ref(claim)),
            })
            .collect();
        let mut vs = VerifierState::from_label(DOMAIN, fs);
        verify_opening_batch_mixed_whir_stacked(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            &inst.root,
            point_claims,
            &rings,
        )
        .is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &inst.fs),
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
            !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
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
            !verify_instance(&inst, &bad_points, &inst.ring_verify, &inst.fs),
            "tampered Strided value accepted"
        );

        // Wrong ring-switched slices: rejected by the ring-switch binding. A wrong
        // point is rejected by the weight, shared pass or not.
        for r in 0..inst.ring_verify.len() {
            let mut bad_ring = inst.ring_verify.clone();
            bad_ring[r].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "tampered ring-switch slice {r} accepted"
            );
            let mut bad_ring = inst.ring_verify.clone();
            bad_ring[r].suffix_point[0] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "moved ring-switch point {r} accepted"
            );
        }

        // Every scalar the opening sends rides the stream, all of them WHIR's:
        // tampering any of them must be rejected.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // Shape tamper: a truncated stream must return false, not panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring_verify, &short_fs),
            "short stream accepted"
        );
    }

    /// Residual cube crossing INTO the q_flock slice (case split = n_ris in the
    /// verifier closure): q_flock occupies half a 2^14 stack (qflock_vars = 13),
    /// and the fallback config's residual cube (yr_log_n = 3) is wider than
    /// the single selector coordinate, so some q_flock coords are covered by
    /// binary y bits and the tensor finish runs with a nonempty suffix.
    #[test]
    fn stacked_open_residual_crosses_qflock() {
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
        let s_hat_v = fold_1b_rows(qflock, &eq_table(&suffix_point));
        let claims = vec![RingSwitchClaim {
            suffix_point,
            // Exercise the precomputed path (transcript must be identical).
            s_hat_v: Some(s_hat_v),
        }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let ring = RingSwitchOpen {
            offset: qflock_offset,
            qflock_vars,
            claims,
        };
        let mut ps = ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(
            &mut ps,
            log_n,
            &stack,
            &pd,
            &pc,
            &point_claims,
            std::slice::from_ref(&ring),
        );
        let fs = ps.into_proof();

        let ring_v = RingSwitchVerify {
            offset: qflock_offset,
            qflock_vars,
            claims: verifier_claims(&ring.claims),
        };
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                std::slice::from_ref(&ring_v)
            )
            .is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_claims = ring.claims.clone();
        bad_claims[0].s_hat_v.as_mut().unwrap()[7] += F192::ONE;
        let bad_ring = RingSwitchVerify {
            offset: ring.offset,
            qflock_vars: ring.qflock_vars,
            claims: verifier_claims(&bad_claims),
        };
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                std::slice::from_ref(&bad_ring)
            )
            .is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
