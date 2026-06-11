//! End-to-end prove → verify roundtrip of the front-loaded batched AIR
//! sumcheck with a univariate skip round (plan_spec.md "Protocol spec").
//!
//! Three real tables of unequal heights run through a shared transcript:
//!   execution    n = 13  (2 shift columns, analytic padding: non_padded = 2^12)
//!   poseidon16   n = 10  (degree-split AIR)
//!   extension_op n = 9
//! The per-table claims s_t are brute-forced independently (naive loop over
//! every row with `eval_extension`), and the verifier's final identity
//!
//!   final_target == Σ_t ê(r0) · eq(eq_factor_t[..n_t−K], natural_prefix_t)
//!                         · C_t(col_evals_t)
//!
//! is checked in full — this test pins the convention T5 copies into
//! verify_execution.rs. Adversarial variants tamper one transcript coefficient
//! of the skip round (must be rejected at the round-0 window identity) and one
//! linear-round coefficient (must be rejected by the final identity; with c0
//! elision the per-round checks absorb wire tampering by construction).

use backend::*;
use lean_vm::{ALL_TABLES, EF, ExtraDataForBuses, F, LOG_MAX_BUS_WIDTH, Table, delegate_to_inner};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{
    AirSumcheckSession, SkipSession, UniskipAirPoint, compute_shifted_columns, natural_prefix_for_session,
    prove_batched_air_sumcheck_uniskip, verify_batched_air_sumcheck_uniskip,
};

struct TableData {
    table: Table,
    log_n: usize,
    non_padded: usize,
    /// flat columns followed by shift columns, materialized over all 2^log_n rows
    cols: Vec<ArenaVec<F>>,
}

fn build_table_data(table: Table, log_n: usize, non_padded: usize, rng: &mut StdRng) -> TableData {
    let n_rows = 1usize << log_n;
    let n_flat = table.n_columns();
    let mut flat: Vec<ArenaVec<F>> = Vec::with_capacity(n_flat);
    for _ in 0..n_flat {
        let mut col: Vec<F> = (0..non_padded).map(|_| rng.random()).collect();
        // Padding rows all repeat one fixed row (the analytic-padding model).
        let pad: F = rng.random();
        col.resize(n_rows, pad);
        flat.push(col.into_iter().collect());
    }
    let refs: Vec<&[F]> = flat.iter().map(|c| c.as_slice()).collect();
    let shift = compute_shifted_columns(table.n_shift_columns(), &refs);
    let mut cols = flat;
    cols.extend(shift);
    TableData {
        table,
        log_n,
        non_padded,
        cols,
    }
}

/// Independent reference: s_t = Σ_x eq(eq_factor_t, x) · C_t(row x), naive.
fn brute_force_sum(td: &TableData, eq_factor: &[EF], extra: &ExtraDataForBuses<EF>) -> EF {
    let eq_table = eval_eq(eq_factor);
    let mut sum = EF::ZERO;
    for x in 0..1usize << td.log_n {
        let row: Vec<EF> = td.cols.iter().map(|c| EF::from(c[x])).collect();
        macro_rules! eval_row {
            ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &row, extra) }};
        }
        let c = delegate_to_inner!(&td.table => eval_row);
        sum += eq_table[x] * c;
    }
    sum
}

/// What the cheating prover perturbs on the wire.
#[derive(Clone, Copy)]
enum Tamper {
    None,
    /// Add 1 to skip-poly coefficient `i` before sending.
    SkipCoeff(usize),
    /// Add 1 to combined coefficient `i` (i ≥ 1; c0 is elided) of linear round `r`.
    LinearCoeff(usize, usize),
}

/// Builds sessions, runs the (optionally tampered) prover, then verifies the
/// transcript including the full final identity. Returns Ok(()) iff accepted.
fn roundtrip(k: usize, tamper: Tamper) -> Result<(), String> {
    let mut rng = StdRng::seed_from_u64(7 * k as u64 + 1);
    let tables: Vec<TableData> = vec![
        build_table_data(Table::execution(), 13, 1 << 12, &mut rng),
        build_table_data(Table::extension_op(), 9, 1 << 9, &mut rng),
        build_table_data(Table::poseidon16(), 10, 1 << 10, &mut rng),
    ];
    assert_eq!(
        tables.iter().map(|t| t.table).collect::<Vec<_>>(),
        ALL_TABLES.to_vec(),
        "session order convention"
    );
    let n_max = tables.iter().map(|t| t.log_n).max().unwrap();
    let total_constraints: usize = tables.iter().map(|t| t.table.n_constraints()).sum();
    let max_full_degree = tables.iter().map(|t| t.table.degree_air() + 1).max().unwrap();

    // ---------------- prover ----------------
    let mut prover_state = ProverState::<EF, _>::new(get_poseidon16().clone(), Default::default());
    prover_state.duplex(); // fresh state has a stale rate; production absorbs a commitment first
    let air_alpha: EF = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(total_constraints);
    prover_state.duplex();
    let logup_alphas: Vec<EF> = prover_state.sample_vec(LOG_MAX_BUS_WIDTH);
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);
    prover_state.duplex();
    let gkr_point: Vec<EF> = prover_state.sample_vec(n_max);
    let eq_top = gkr_point[n_max - k..].to_vec();

    // Per-table eq factors (suffixes of the shared gkr point), claims, extra data.
    let mut sums = Vec::new();
    let mut alpha_offset = 0;
    let mut extras_for_final = Vec::new();
    let mut sessions: Vec<Box<dyn SkipSession<EF> + '_>> = Vec::new();
    for td in &tables {
        let eq_factor = gkr_point[n_max - td.log_n..].to_vec();
        let alpha_slice = air_alpha_powers[alpha_offset..alpha_offset + td.table.n_constraints()].to_vec();
        alpha_offset += td.table.n_constraints();
        let extra = ExtraDataForBuses::new(&logup_alphas_eq_poly, alpha_slice.clone());
        let s_t = brute_force_sum(td, &eq_factor, &extra);
        sums.push(s_t);
        extras_for_final.push(ExtraDataForBuses::new(&logup_alphas_eq_poly, alpha_slice));

        let col_refs: Vec<&[F]> = td.cols.iter().map(|c| c.as_slice()).collect();
        let packed = MleGroupRef::<EF>::Base(col_refs).pack();
        macro_rules! make_session {
            ($t:expr) => {{
                let s = AirSumcheckSession::new(packed, eq_factor.clone(), s_t, *$t, extra, td.non_padded);
                Box::new(s) as Box<dyn SkipSession<EF> + '_>
            }};
        }
        sessions.push(delegate_to_inner!(&td.table => make_session));
    }

    let point = match tamper {
        Tamper::None => prove_batched_air_sumcheck_uniskip(&mut prover_state, &mut sessions, k),
        _ => prove_tampered(&mut prover_state, &mut sessions, k, tamper),
    };

    // Per-table column openings (transcript-sent, as in prove_execution.rs).
    for session in &sessions {
        prover_state.add_extension_scalars(&session.final_column_evals());
    }

    // Prover-side sanity on the honest path: the final identity holds locally.
    if matches!(tamper, Tamper::None) {
        let final_sum: EF = sessions.iter().map(|s| s.sum()).fold(EF::ZERO, |a, b| a + b);
        let e_hat_r0 = e_hat_at(&eq_top, point.r0);
        let mut check = EF::ZERO;
        for (idx, (td, session)) in tables.iter().zip(&sessions).enumerate() {
            let eq_factor = &gkr_point[n_max - td.log_n..];
            let prefix = natural_prefix_for_session(&point, td.log_n);
            let eq_val =
                MultilinearPoint(eq_factor[..td.log_n - k].to_vec()).eq_poly_outside(&MultilinearPoint(prefix.clone()));
            let col_evals = session.final_column_evals();
            macro_rules! eval_c {
                ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &col_evals, &extras_for_final[idx]) }};
            }
            let c_eval = delegate_to_inner!(&td.table => eval_c);
            check += e_hat_r0 * eq_val * c_eval;
        }
        assert_eq!(check, final_sum, "prover-side final identity");
    }

    // ---------------- verifier ----------------
    let mut verifier_state =
        VerifierState::<EF, _>::new(prover_state.into_proof(), get_poseidon16().clone(), Default::default())
            .map_err(|e| format!("{e:?}"))?;
    verifier_state.duplex();
    let air_alpha_v: EF = verifier_state.sample();
    let air_alpha_powers_v: Vec<EF> = air_alpha_v.powers().collect_n(total_constraints);
    verifier_state.duplex();
    let logup_alphas_v: Vec<EF> = verifier_state.sample_vec(LOG_MAX_BUS_WIDTH);
    let logup_alphas_eq_poly_v = eval_eq(&logup_alphas_v);
    verifier_state.duplex();
    let gkr_point_v: Vec<EF> = verifier_state.sample_vec(n_max);
    assert_eq!(gkr_point_v, gkr_point);
    let eq_top_v = gkr_point_v[n_max - k..].to_vec();

    let table_n_vars: Vec<usize> = tables.iter().map(|t| t.log_n).collect();
    let table_degrees: Vec<usize> = tables.iter().map(|t| t.table.degree_air()).collect();

    let (point_v, final_target): (UniskipAirPoint<EF>, EF) = verify_batched_air_sumcheck_uniskip(
        &mut verifier_state,
        k,
        &table_n_vars,
        &table_degrees,
        &sums,
        &eq_top_v,
        max_full_degree,
    )
    .map_err(|e| format!("uniskip verify: {e:?}"))?;

    // Final identity (the formula T5 installs in verify_execution.rs).
    let e_hat_r0 = e_hat_at(&eq_top_v, point_v.r0);
    let mut alpha_offset = 0;
    let mut my_final = EF::ZERO;
    for td in &tables {
        let n_cols_total = td.table.n_columns() + td.table.n_shift_columns();
        let col_evals = verifier_state
            .next_extension_scalars_vec(n_cols_total)
            .map_err(|e| format!("{e:?}"))?;
        let alpha_slice = air_alpha_powers_v[alpha_offset..alpha_offset + td.table.n_constraints()].to_vec();
        alpha_offset += td.table.n_constraints();
        let extra = ExtraDataForBuses::new(&logup_alphas_eq_poly_v, alpha_slice);
        macro_rules! eval_c {
            ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &col_evals, &extra) }};
        }
        let c_eval = delegate_to_inner!(&td.table => eval_c);

        let eq_factor = &gkr_point_v[n_max - td.log_n..];
        let prefix = natural_prefix_for_session(&point_v, td.log_n);
        let eq_val = MultilinearPoint(eq_factor[..td.log_n - k].to_vec()).eq_poly_outside(&MultilinearPoint(prefix));
        my_final += e_hat_r0 * eq_val * c_eval;
    }
    if my_final != final_target {
        return Err("final identity mismatch".to_string());
    }
    Ok(())
}

/// Cheating-prover replica of `prove_batched_air_sumcheck_uniskip`: identical
/// schedule, but perturbs one wire coefficient. Sessions consume the challenges
/// of the tampered transcript (the natural cheating model).
fn prove_tampered<'a>(
    prover_state: &mut impl FSProver<EF>,
    sessions: &mut [Box<dyn SkipSession<EF> + 'a>],
    k: usize,
    tamper: Tamper,
) -> UniskipAirPoint<EF> {
    let n_max = sessions.iter().map(|s| s.initial_n_vars()).max().unwrap();
    let max_full_degree = sessions.iter().map(|s| s.bare_degree() + 1).max().unwrap();
    let d_max = sessions.iter().map(|s| s.bare_degree()).max().unwrap();
    let n_skip_coeffs = ((1usize << k) - 1) * d_max + 1;
    let weights: Vec<EF> = sessions
        .iter()
        .map(|s| EF::from_usize(1 << (n_max - s.initial_n_vars())))
        .collect();
    let eq_top = sessions[0].skip_eq_top(k);

    let skip_polys: Vec<DensePolynomial<EF>> = sessions.iter_mut().map(|s| s.compute_skip_poly(k)).collect();
    let mut combined_skip = EF::zero_vec(n_skip_coeffs);
    for (poly, &w_t) in skip_polys.iter().zip(&weights) {
        for (acc, &c) in combined_skip.iter_mut().zip(&poly.coeffs) {
            *acc += w_t * c;
        }
    }
    if let Tamper::SkipCoeff(i) = tamper {
        combined_skip[i] += EF::ONE;
    }
    prover_state.add_extension_scalars(&combined_skip);
    let r0: EF = prover_state.sample();
    let lagrange_weights = lagrange_weights_at::<F, EF>(k, r0);
    let e_hat_r0 = e_hat_at(&eq_top, r0);
    for (session, poly) in sessions.iter_mut().zip(&skip_polys) {
        session.process_skip_challenge(k, r0, &lagrange_weights, e_hat_r0, poly);
    }

    let n_linear = n_max - k;
    let mut linear_challenges = Vec::with_capacity(n_linear);
    for r in 0..n_linear {
        let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
        let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];
        for (idx, session) in sessions.iter_mut().enumerate() {
            let n_own = session.initial_n_vars() - k;
            if r < n_own {
                let bare = session.compute_bare_round_poly();
                let full = expand_bare_to_full(&bare.coeffs, session.eq_alpha());
                for (acc, &c) in combined_coeffs.iter_mut().zip(&full) {
                    *acc += weights[idx] * c;
                }
                bare_polys[idx] = Some(bare);
            } else {
                combined_coeffs[0] += session.sum() * EF::from_usize(1 << (n_linear - r - 1));
            }
        }
        if let Tamper::LinearCoeff(tr, i) = tamper
            && tr == r
        {
            assert!(i >= 1, "c0 is elided; tamper a sent coefficient");
            combined_coeffs[i] += EF::ONE;
        }
        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        linear_challenges.push(challenge);
        for (idx, session) in sessions.iter_mut().enumerate() {
            if let Some(bare) = &bare_polys[idx] {
                session.process_challenge(challenge, bare);
            }
        }
    }
    UniskipAirPoint {
        r0,
        lagrange_weights,
        linear_challenges,
    }
}

#[test]
fn test_uniskip_e2e_roundtrip() {
    for k in [3, 4] {
        roundtrip(k, Tamper::None).unwrap_or_else(|e| panic!("k={k}: {e}"));
    }
}

#[test]
fn test_uniskip_e2e_rejects_tampered_skip_coeff() {
    for i in [0, 7] {
        let err = roundtrip(4, Tamper::SkipCoeff(i)).expect_err("tampered skip coeff must be rejected");
        assert!(err.contains("uniskip verify"), "expected round-0 rejection, got: {err}");
    }
}

#[test]
fn test_uniskip_e2e_rejects_tampered_linear_coeff() {
    // With c0 elision the per-round identity absorbs wire perturbations; the
    // corruption must surface at the final identity.
    for (r, i) in [(0, 1), (4, 3)] {
        let err = roundtrip(4, Tamper::LinearCoeff(r, i)).expect_err("tampered linear coeff must be rejected");
        assert!(!err.is_empty());
    }
}
