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
//! - **ring-switched claims** (one region per packed sub-block, each
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
//! the WHIR verifier with a
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

use super::ring_switch::{self, RingFamily, RingSwitch, SliceClaim};
use super::verifier::OpeningVerifier;
use super::whir::{ProverConfig, ProverData, VerifierConfig, WhirError, recursive_verifier_with_basis_succinct};
use basis::StackWeight;
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::Transmitter;
use primitives::field::{F64, F192, powers};

mod basis;

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

    /// The claim's weight `eq(full claim point, x)` at a point `x` of the stack cube.
    ///
    /// A plain claim's full point is its low point then its offset's bits.
    ///
    /// A strided claim's is its slot's bits, its point, then its offset's bits.
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
pub fn open(
    ps: &mut impl Transmitter,
    log_n: usize,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    rings: &[RingSwitch],
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
    let claims: Vec<&SliceClaim> = rings.iter().flat_map(|ring| &ring.claims).collect();
    for ring in rings {
        for claim in &ring.claims {
            assert_eq!(
                claim.suffix_point.len(),
                ring.qflock_vars,
                "ring-switch suffix point must have qflock_vars coords"
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
    let rs_outputs: Vec<_> = (claims.iter().zip(powers(family.gamma_rs(), n_rs)))
        .map(|(claim, scale)| ring_switch::deferred_weight(&claim.suffix_point, scale, &coordinate_weights))
        .collect();
    drop(span);

    // 3. Combined target and lifted stack weight b_stack: each claim's share of
    //    the family's weight scattered at its q_flock slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let target = family.share(&mut Native, rings).target(&mut Native)
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value());

    // The lifted weight is filled one chunk at a time:
    //
    //     first pass:  each chunk is filled, then feeds the first lane rounds' sums while hot
    //     first fold:  each chunk is filled again, then folded by those rounds' challenges
    //
    // On a small pool the first pass also writes each chunk out, and the first fold reads it back rather than filling
    // it again.
    let lane_block = 1usize << (log_n - config.initial_k());
    let weight = tracing::info_span!(
        "Stack weight setup",
        stack_words = stack.len(),
        lane_block,
        point_claims = point_claims.len(),
        ring_claims = n_rs,
    ).in_scope(|| StackWeight::new(stack.len(), lane_block, point_claims, lambdas_pd, rings, &rs_outputs));
    #[cfg(any(not(leanvm_basis_staged), leanvm_basis_check))]
    let fill = |start: usize, dst: &mut [F192]| weight.fill(start, dst);
    // Keep this boundary identical: setup remains outside Basis. The staged diagnostic
    // changes only the schedule inside it, and keeps the same weights for the first fold.
    let (initial, basis) = tracing::info_span!(
        "Basis",
        stack_words = stack.len(),
        witness_bytes = size_of_val(stack),
        weight_bytes = stack.len() * size_of::<F192>(),
        lane_block,
        lanes = stack.len() / lane_block,
        initial_k = config.initial_k(),
        staged = cfg!(leanvm_basis_staged),
    ).in_scope(|| {
        #[cfg(not(leanvm_basis_staged))]
        {
            super::whir::initial_rounds_virtual(stack, lane_block, config.initial_k(), &fill)
        }
        #[cfg(leanvm_basis_staged)]
        {
            let basis = super::whir::Basis::Dense(weight.materialize(stack.len()));
            let initial = tracing::info_span!("Basis staged grid")
                .in_scope(|| super::whir::initial_rounds(stack, lane_block, config.initial_k(), &basis));
            (initial, basis)
        }
    });
    #[cfg(all(leanvm_basis_staged, leanvm_basis_check))]
    if let super::whir::Basis::Dense(kept) = &basis {
        tracing::info_span!("Basis staged reference check").in_scope(|| {
            initial.assert_matches_virtual(stack, lane_block, config.initial_k(), &fill, kept);
        });
    }
    // Diagnostic builds only: capture after the timed Basis span, never from a measured invocation.
    #[cfg(leanvm_basis_staged)]
    if let Some(directory) = std::env::var_os("ARM_ATTRIBUTION_BASIS_DIR") {
        use std::io::{BufWriter, Write};
        let super::whir::Basis::Dense(kept) = &basis else {
            unreachable!("the staged diagnostic keeps its weight");
        };
        let directory = std::path::Path::new(&directory);
        std::fs::create_dir_all(directory).expect("create Basis capture directory");
        // The CLI also proves during warmup; the last completed opening replaces that capture.
        let create = |name: &str| {
            BufWriter::with_capacity(
                1 << 20,
                std::fs::File::create(directory.join(name)).expect("create Basis capture file"),
            )
        };
        let mut shape = create("shape.bin");
        for value in [stack.len(), lane_block, config.initial_k()] {
            shape.write_all(&(value as u64).to_le_bytes()).expect("write Basis shape");
        }
        shape.flush().expect("flush Basis shape");
        let mut witness = create("witness.bin");
        for value in stack {
            witness.write_all(&value.0.to_le_bytes()).expect("write Basis witness");
        }
        witness.flush().expect("flush Basis witness");
        let mut weights = create("weight.bin");
        for value in kept {
            for coefficient in [value.c0, value.c1, value.c2] {
                weights.write_all(&coefficient.to_le_bytes()).expect("write Basis weight");
            }
        }
        weights.flush().expect("flush Basis weight");
        eprintln!(
            "basis_capture words={} lane_block={} initial_k={} directory={}",
            stack.len(), lane_block, config.initial_k(), directory.display(),
        );
    }

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    super::whir::recursive_prover_with_prepared_basis(
        config,
        log_n,
        stack,
        basis,
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        Some(initial),
        ps,
    );
}

/// Verifier mirror of [`open`].
///
/// It replays the ring switch succinctly, recomputes the combined target, then drives the succinct WHIR verifier with one terminal evaluation of the lifted weight.
/// `log_n` is the committed stack's log size in `F64` words, and `root` the L0 commitment's root.
/// The family takes the batching challenge's power one, and point claim `i` its power `i + 1`.
///
/// The verifier is the native one or the recursion machine's rows, which run the same steps.
///
/// # Errors
///
/// Returns a statement whose regions or claims leave the committed cube, then the WHIR verifier's refusal.
pub fn verify<V: OpeningVerifier>(
    v: &mut V,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    root: V::Root,
    point_claims: &[StackClaim<V::E>],
    rings: &[RingSwitch<V::E>],
) -> Result<(), WhirError> {
    check_statement(log_n, point_claims, rings)?;

    // The family: every claim arrives with its 64 slices, bound upstream by the caller, so nothing is read here.
    // Then the one batching challenge, the family taking its first power.
    let family = RingFamily::draw(v);
    let lambda = v.sample();
    let lambdas = v.powers(lambda, 1 + point_claims.len());
    let share = family.share(v, rings);
    let target = v.scope("target", |v| {
        let family_target = share.target(v);
        (point_claims.iter().zip(&lambdas[1..]))
            .fold(family_target, |acc, (claim, &g)| v.mul_add(g, claim.value(), acc))
    });

    // The lifted weight, evaluated once at the terminal sumcheck point.
    let weight_at = |v: &mut V, x: &[V::E]| {
        let family_weight = share.weight_at(v, x);
        (point_claims.iter().zip(&lambdas[1..])).fold(family_weight, |acc, (claim, &g)| {
            let eq = claim.eq_at(v, x);
            v.mul_add(g, eq, acc)
        })
    };
    v.scope("whir", |v| {
        recursive_verifier_with_basis_succinct(v, config, log_n, n_lanes, target, root, weight_at)
    })
}

/// The statement's invariants: a ring-switched claim, and every region and claim an aligned slice of the committed cube.
fn check_statement<E: Copy>(
    log_n: usize,
    point_claims: &[StackClaim<E>],
    rings: &[RingSwitch<E>],
) -> Result<(), WhirError> {
    let cube = 1usize << log_n;
    if rings.iter().all(|ring| ring.claims.is_empty()) {
        return Err(WhirError::NoRingClaim);
    }
    for (index, ring) in rings.iter().enumerate() {
        let len = 1usize << ring.qflock_vars;
        let spans = ring
            .claims
            .iter()
            .all(|claim| claim.suffix_point.len() == ring.qflock_vars);
        if ring.qflock_vars > log_n || !ring.offset.is_multiple_of(len) || ring.offset + len > cube || !spans {
            return Err(WhirError::Region { index });
        }
    }
    if let Some(index) = point_claims.iter().position(|claim| claim.range().1 > cube) {
        return Err(WhirError::PointClaim { index });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::tests::s_hat_v_reference;
    use crate::whir::config::tests::{default_config, test_config_for};
    use crate::whir::{INITIAL_BASIS_CHUNK, commit, inner_product_base_ext};
    use basis::StackWeight;
    use fiat_shamir::merkle::Hash;
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
            // The weight reads only the points, so the slices are any 64 values.
            let ring = RingSwitch {
                offset,
                qflock_vars,
                claims: (0..2)
                    .map(|_| SliceClaim {
                        suffix_point: rng.ext_vec(qflock_vars),
                        s_hat_v: rng.ext_vec(F64::DEGREE),
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
        rings: Vec<RingSwitch>,
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
        open(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &rings);

        Instance {
            vc: pc,
            log_n,
            root: cm.root,
            point_claims,
            rings,
            fs: ps.into_proof(),
        }
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        rings: &[RingSwitch],
        fs: &ProofTranscript,
    ) -> bool {
        let mut vs = VerifierState::from_label(DOMAIN, fs);
        verify(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            inst.root,
            point_claims,
            rings,
        )
        .is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
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

        // Wrong ring-switched slices: rejected by the ring-switch binding. A wrong
        // point is rejected by the weight, shared pass or not.
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

        // Every scalar the opening sends rides the stream, all of them WHIR's:
        // tampering any of them must be rejected.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.rings, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // Shape tamper: a truncated stream must return false, not panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.rings, &short_fs),
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
        let s_hat_v = s_hat_v_reference(qflock, &suffix_point);
        let claims = vec![SliceClaim { suffix_point, s_hat_v }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let ring = RingSwitch {
            offset: qflock_offset,
            qflock_vars,
            claims,
        };
        let mut ps = ProverState::from_label(DOMAIN);
        open(
            &mut ps,
            log_n,
            &stack,
            &pd,
            &pc,
            &point_claims,
            std::slice::from_ref(&ring),
        );
        let fs = ps.into_proof();

        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                cm.root,
                &point_claims,
                std::slice::from_ref(&ring)
            )
            .is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_ring = ring.clone();
        bad_ring.claims[0].s_hat_v[7] += F192::ONE;
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                cm.root,
                &point_claims,
                std::slice::from_ref(&bad_ring)
            )
            .is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
