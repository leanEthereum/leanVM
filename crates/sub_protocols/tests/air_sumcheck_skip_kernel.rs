//! Correctness + go/no-go timing tests for the univariate skip-round kernel
//! (`SkipSession` on `AirSumcheckSession`). See plan_spec.md (pw13, h1) T2.

use std::time::Instant;

use backend::*;
use lean_vm::{EF, ExecutionTable, ExtensionOpPrecompile, ExtraDataForBuses, F, LOG_MAX_BUS_WIDTH, Poseidon16Precompile};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{AirSumcheckSession, OuterSumcheckSession, SkipSession, UNIVARIATE_SKIP_K, skip_block_of_x};

fn random_cols(rng: &mut StdRng, n_cols: usize, n_rows: usize) -> Vec<ArenaVec<F>> {
    (0..n_cols)
        .map(|_| ArenaVec::from_iter((0..n_rows).map(|_| rng.random())))
        .collect()
}

/// Pads rows `>= non_padded` with copies of one fixed row (the production
/// padding shape: identical rows, so the padded blocks are constraint-constant).
fn pad_cols(cols: &mut [ArenaVec<F>], non_padded: usize) {
    let n_rows = cols[0].len();
    for col in cols.iter_mut() {
        let pad_value = col[non_padded - 1];
        for i in non_padded..n_rows {
            col[i] = pad_value;
        }
    }
}

fn brute_force_sum<A>(air: &A, extra: &A::ExtraData, cols: &[ArenaVec<F>], eq_factor: &[EF]) -> EF
where
    A: Air,
    A::ExtraData: AlphaPowers<EF>,
{
    let eq = eval_eq(eq_factor);
    let n_rows = cols[0].len();
    let mut point = vec![F::ZERO; cols.len()];
    let mut sum = EF::ZERO;
    for row in 0..n_rows {
        for (c, col) in cols.iter().enumerate() {
            point[c] = col[row];
        }
        sum += eq[row] * SumcheckComputation::<EF>::eval_base(air, &point, extra);
    }
    sum
}

/// Runs the full per-x / extended-node / aggregate identity battery for one AIR.
fn check_skip_identities<A>(air: A, n: usize, k: usize, n_cols_total: usize, non_padded: Option<usize>, seed: u64)
where
    A: Air + Copy + std::fmt::Debug + Air<ExtraData = ExtraDataForBuses<EF>>,
{
    let mut rng = StdRng::seed_from_u64(seed);
    let n_rows = 1usize << n;
    let mut cols = random_cols(&mut rng, n_cols_total, n_rows);
    if let Some(np) = non_padded {
        pad_cols(&mut cols, np);
    }
    let eq_factor: Vec<EF> = (0..n).map(|_| rng.random()).collect();
    let alpha: EF = rng.random();
    let alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints());
    let logup_alphas: Vec<EF> = (0..LOG_MAX_BUS_WIDTH).map(|_| rng.random()).collect();
    let extra = ExtraDataForBuses::new(&eval_eq(&logup_alphas), alpha_powers.clone());

    let sum = brute_force_sum(&air, &extra, &cols, &eq_factor);

    let col_refs: Vec<&[F]> = cols.iter().map(|c| c.as_slice()).collect();
    let packed = MleGroupRef::<EF>::Base(col_refs.clone()).pack();
    let extra_session = ExtraDataForBuses::new(&eval_eq(&logup_alphas), alpha_powers.clone());
    let mut session = AirSumcheckSession::new(
        packed,
        eq_factor.clone(),
        sum,
        air,
        extra_session,
        non_padded.unwrap_or(n_rows),
    );

    let skip_poly = session.compute_skip_poly(k);
    let degree = SumcheckComputation::<EF>::degree(&air);
    assert!(skip_poly.coeffs.len() <= ((1 << k) - 1) * degree + 1, "degree bound");

    let window = 1usize << k;
    let rest = 1usize << (n - k);
    let eq_rest = eval_eq(&eq_factor[..n - k]);
    let e_hat = eval_eq(&eq_factor[n - k..]);

    // (a) per-window-node identity: v'(node_x) == Σ_j eq_rest[j] · C(row = (j << k) | x).
    let mut point = vec![F::ZERO; n_cols_total];
    let mut aggregate = EF::ZERO;
    for x in 0..window {
        let mut direct = EF::ZERO;
        for j in 0..rest {
            let row = (j << k) | x;
            for (c, col) in cols.iter().enumerate() {
                point[c] = col[row];
            }
            direct += eq_rest[j] * SumcheckComputation::<EF>::eval_base(&air, &point, &extra);
        }
        let from_poly = skip_poly.evaluate(EF::from_usize(x));
        assert_eq!(from_poly, direct, "window node x={x}");
        aggregate += e_hat[x] * from_poly;
    }
    assert_eq!(aggregate, session.sum(), "Σ ê·v' == claim");

    // extended-node spot checks (validates the Lagrange extension + degree-split path
    // independently of the interpolation): nodes window, window+1, and the last one.
    let nodes = skip_all_nodes::<F>(k, degree);
    let lags = lagrange_coeffs_for_targets::<F>(k, &nodes[window..]);
    for &z_idx in &[window, window + 1, nodes.len() - 1] {
        let lag = &lags[z_idx - window];
        let mut direct = EF::ZERO;
        for j in 0..rest {
            for (c, col) in cols.iter().enumerate() {
                let mut v = F::ZERO;
                for (x, &l) in lag.iter().enumerate() {
                    v += col[(j << k) | x] * l;
                }
                point[c] = v;
            }
            direct += eq_rest[j] * SumcheckComputation::<EF>::eval_base(&air, &point, &extra);
        }
        assert_eq!(skip_poly.evaluate(EF::from(nodes[z_idx])), direct, "extended node {z_idx}");
    }

    // (b) bind r0 and compare the post-skip session against brute force.
    let r0: EF = rng.random();
    let lagrange_at_r0 = lagrange_weights_at::<F, EF>(k, r0);
    let e_hat_r0 = e_hat_at(&session.skip_eq_top(k), r0);
    {
        // ê(r0) must interpolate the window values of ê.
        let direct: EF = e_hat
            .iter()
            .zip(&lagrange_at_r0)
            .map(|(&e, &l)| e * l)
            .fold(EF::ZERO, |a, b| a + b);
        assert_eq!(e_hat_r0, direct);
    }
    session.process_skip_challenge(k, r0, &lagrange_at_r0, e_hat_r0, &skip_poly);

    let folded: Vec<Vec<EF>> = cols
        .iter()
        .map(|col| {
            (0..rest)
                .map(|j| {
                    lagrange_at_r0
                        .iter()
                        .enumerate()
                        .map(|(x, &l)| l * col[(j << k) | x])
                        .fold(EF::ZERO, |a, b| a + b)
                })
                .collect()
        })
        .collect();

    // sum invariant: sum == missing · Σ_j eq(eq_factor[..n−k], j) · C(folded(j)).
    let mut point_ef = vec![EF::ZERO; n_cols_total];
    let mut expected_sum = EF::ZERO;
    for j in 0..rest {
        for (c, fc) in folded.iter().enumerate() {
            point_ef[c] = fc[j];
        }
        expected_sum += eq_rest[j] * SumcheckComputation::<EF>::eval_extension(&air, &point_ef, &extra);
    }
    assert_eq!(session.sum(), e_hat_r0 * expected_sum, "post-skip sum invariant");

    // next-round bare poly vs brute force (validates layout + eq bookkeeping):
    // bare(z) = missing · Σ_{j_hi} eq(eq_factor[..n−k−1], j_hi) · C(lerp(folded(2j_hi), folded(2j_hi+1), z)).
    let bare = session.compute_bare_round_poly();
    let eq_hi = eval_eq(&eq_factor[..n - k - 1]);
    for z in 0..=degree {
        let z_ef = EF::from_usize(z);
        let mut direct = EF::ZERO;
        for j_hi in 0..rest / 2 {
            for (c, fc) in folded.iter().enumerate() {
                let v0 = fc[2 * j_hi];
                let v1 = fc[2 * j_hi + 1];
                point_ef[c] = v0 + (v1 - v0) * z_ef;
            }
            direct += eq_hi[j_hi] * SumcheckComputation::<EF>::eval_extension(&air, &point_ef, &extra);
        }
        assert_eq!(
            bare.evaluate(z_ef),
            e_hat_r0 * direct,
            "post-skip bare round poly at z={z}"
        );
    }

    // (c) full pipeline: run all remaining rounds, then check final_column_evals
    // against the direct tensor-weighted MLE evaluation of the original columns.
    let mut challenges = Vec::new();
    let mut bare_poly = bare;
    loop {
        let c: EF = rng.random();
        session.process_challenge(c, &bare_poly);
        challenges.push(c);
        if challenges.len() == n - k {
            break;
        }
        bare_poly = session.compute_bare_round_poly();
    }
    let final_evals = session.final_column_evals();
    for (c, col) in cols.iter().enumerate() {
        let mut direct = EF::ZERO;
        for (row, &v) in col.iter().enumerate() {
            let mut weight = lagrange_at_r0[row & (window - 1)];
            for (r, &ch) in challenges.iter().enumerate() {
                let bit = (row >> (k + r)) & 1;
                weight *= if bit == 1 { ch } else { EF::ONE - ch };
            }
            direct += weight * v;
        }
        assert_eq!(final_evals[c], direct, "final column eval col={c}");
    }
}

#[test]
fn test_skip_block_map() {
    assert_eq!(skip_block_of_x(0b0011, 4), 0b1100);
    assert_eq!(skip_block_of_x(0b0001, 4), 0b1000);
    assert_eq!(skip_block_of_x(0b101, 3), 0b101);
    assert_eq!(skip_block_of_x(0b110, 3), 0b011);
    for k in 1..=5 {
        for x in 0..1usize << k {
            assert_eq!(skip_block_of_x(skip_block_of_x(x, k), k), x);
        }
    }
}

#[test]
fn test_skip_poseidon_degree_split() {
    // Degree-split path (low_degree_air = (3, 20)), K=3 and K=4.
    let air = Poseidon16Precompile::<false>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 11, 4, n_cols, None, 1);
    check_skip_identities(air, 11, 3, n_cols, None, 2);
}

#[test]
fn test_skip_poseidon_with_bus() {
    // BUS=true exercises the eval_bus_virtual constraints in the AIR.
    let air = Poseidon16Precompile::<true>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 10, 4, n_cols, None, 3);
}

#[test]
fn test_skip_execution_with_shift_cols() {
    // Generic (non-degree-split) path with shift columns, K=3 and K=4.
    let air = ExecutionTable::<false>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 10, 4, n_cols, None, 4);
    check_skip_identities(air, 10, 3, n_cols, None, 5);
}

#[test]
fn test_skip_extension_op() {
    let air = ExtensionOpPrecompile::<false>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 9, 4, n_cols, None, 6);
}

#[test]
fn test_skip_with_padding() {
    // n > pivot so that padded_n_rows < 2^n and the analytic padding term is active:
    // n = 13, pivot = 12, non_padded = 2^12 → half the blocks are pure padding.
    let air = Poseidon16Precompile::<false>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 13, 4, n_cols, Some(1 << 12), 7);
}

#[test]
fn test_skip_unpacked_fallback() {
    // n − K ≤ packing_log_width → scalar fallback path.
    // AVX-512: w = 4, so n=8, K=4 (boundary) and n=9, K=5 both fall back.
    let air = ExtensionOpPrecompile::<false>;
    let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
    check_skip_identities(air, 8, 4, n_cols, None, 8);
    check_skip_identities(air, 9, 5, n_cols, None, 9);
}

/// h4 (iteration 2): the finite-difference extension must produce the SAME
/// polynomial, bit for bit, as the reference Lagrange-dot extension — exact
/// field arithmetic evaluating the same unique degree-bounded polynomial.
/// Covers all three kernels (generic, degree-split, unpacked fallback), the
/// padding path, and K ∈ {3, 4, 5}.
#[test]
fn test_fd_extension_matches_lagrange() {
    fn check<A>(air: A, n: usize, k: usize, non_padded: Option<usize>, seed: u64)
    where
        A: Air + Copy + std::fmt::Debug + Air<ExtraData = ExtraDataForBuses<EF>>,
    {
        let mut rng = StdRng::seed_from_u64(seed);
        let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
        let n_rows = 1usize << n;
        let mut cols = random_cols(&mut rng, n_cols, n_rows);
        if let Some(np) = non_padded {
            pad_cols(&mut cols, np);
        }
        let eq_factor: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let alpha: EF = rng.random();
        let logup_alphas: Vec<EF> = (0..LOG_MAX_BUS_WIDTH).map(|_| rng.random()).collect();
        let col_refs: Vec<&[F]> = cols.iter().map(|c| c.as_slice()).collect();
        let packed = MleGroupRef::<EF>::Base(col_refs).pack();
        let extra = ExtraDataForBuses::new(
            &eval_eq(&logup_alphas),
            alpha.powers().collect_n(Air::n_constraints(&air)),
        );
        let mut session = AirSumcheckSession::new(
            packed,
            eq_factor,
            EF::ZERO,
            air,
            extra,
            non_padded.unwrap_or(n_rows),
        );
        // compute_skip_poly does not advance the session: both paths run on
        // identical state.
        let lagrange = session.compute_skip_poly_forced(k, true);
        let fd = session.compute_skip_poly_forced(k, false);
        assert_eq!(fd.coeffs, lagrange.coeffs, "{air:?} n={n} k={k} pad={non_padded:?}");
    }

    // degree-split kernel (poseidon), K ∈ {3, 4, 5}:
    check(Poseidon16Precompile::<false>, 11, 3, None, 21);
    check(Poseidon16Precompile::<false>, 11, 4, None, 22);
    check(Poseidon16Precompile::<false>, 11, 5, None, 23);
    check(Poseidon16Precompile::<true>, 10, 4, None, 24);
    // generic kernel (execution, with shift cols), K ∈ {3, 4}:
    check(ExecutionTable::<false>, 10, 3, None, 25);
    check(ExecutionTable::<false>, 10, 4, None, 26);
    // extension_op:
    check(ExtensionOpPrecompile::<false>, 9, 4, None, 27);
    // padding path (n > pivot):
    check(Poseidon16Precompile::<false>, 13, 4, Some(1 << 12), 28);
    // unpacked fallback (n − k ≤ packing_log_width):
    check(ExtensionOpPrecompile::<false>, 8, 4, None, 29);
    check(ExtensionOpPrecompile::<false>, 9, 5, None, 30);
}

/// GO/NO-GO timing gate (plan_spec T2, kill condition a): the skip round must
/// be cheaper than the legacy rounds 0..K−1 it replaces, on production-shaped
/// data. Extended for h4 (plan_spec iteration 2, U1): also times the
/// finite-difference extension against the reference Lagrange-dot extension —
/// FD must win on the combined workload. Run with:
///   cargo test --release -p sub_protocols --test air_sumcheck_skip_kernel -- --ignored --nocapture
#[test]
#[ignore]
fn skip_kernel_timing() {
    let k = UNIVARIATE_SKIP_K;

    fn time_table<A>(air: A, n: usize, k: usize, label: &str) -> (f64, f64, f64, f64)
    where
        A: Air + Copy + std::fmt::Debug + Air<ExtraData = ExtraDataForBuses<EF>>,
    {
        let mut rng = StdRng::seed_from_u64(42);
        let n_cols = Air::n_columns(&air) + Air::n_shift_columns(&air);
        let n_rows = 1usize << n;
        let cols = random_cols(&mut rng, n_cols, n_rows);
        let eq_factor: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let alpha: EF = rng.random();
        let logup_alphas: Vec<EF> = (0..LOG_MAX_BUS_WIDTH).map(|_| rng.random()).collect();
        let col_refs: Vec<&[F]> = cols.iter().map(|c| c.as_slice()).collect();

        fn make<'a, A>(
            cols_refs: Vec<&'a [F]>,
            air: A,
            eq_factor: &[EF],
            logup_alphas: &[EF],
            alpha: EF,
            n_rows: usize,
        ) -> AirSumcheckSession<'a, EF, A>
        where
            A: Air + Copy + std::fmt::Debug + Air<ExtraData = ExtraDataForBuses<EF>>,
        {
            let packed = MleGroupRef::<EF>::Base(cols_refs).pack();
            let extra = ExtraDataForBuses::new(
                &eval_eq(logup_alphas),
                alpha.powers().collect_n(Air::n_constraints(&air)),
            );
            AirSumcheckSession::new(packed, eq_factor.to_vec(), EF::ZERO, air, extra, n_rows)
        }

        // h4: FD vs Lagrange extension, compute_skip_poly only (the delta is
        // confined to it). Lagrange first (warms the gather paths for FD too).
        let mut s_skip = make(col_refs.clone(), air, &eq_factor, &logup_alphas, alpha, n_rows);
        let t_lag0 = Instant::now();
        let _lag_poly = s_skip.compute_skip_poly_forced(k, true);
        let t_lagrange = t_lag0.elapsed().as_secs_f64() * 1e3;

        let t0 = Instant::now();
        let skip_poly = s_skip.compute_skip_poly_forced(k, false);
        let t_fd = t0.elapsed().as_secs_f64() * 1e3;

        // Full skip path (FD poly + fold), for the original skip-vs-legacy gate.
        let r0: EF = rng.random();
        let lw = lagrange_weights_at::<F, EF>(k, r0);
        let e_hat_r0 = e_hat_at(&s_skip.skip_eq_top(k), r0);
        let t_fold0 = Instant::now();
        s_skip.process_skip_challenge(k, r0, &lw, e_hat_r0, &skip_poly);
        let t_skip = t_fd + t_fold0.elapsed().as_secs_f64() * 1e3;

        // Legacy path: K rounds.
        let mut s_legacy = make(col_refs.clone(), air, &eq_factor, &logup_alphas, alpha, n_rows);
        let t1 = Instant::now();
        for round in 0..k {
            let poly = s_legacy.compute_bare_round_poly();
            s_legacy.process_challenge(EF::from_usize(5 + round), &poly);
        }
        let t_legacy = t1.elapsed().as_secs_f64() * 1e3;

        println!(
            "{label}: skip-poly FD {t_fd:8.2} ms vs Lagrange {t_lagrange:8.2} ms | skip(FD) {t_skip:8.2} ms vs legacy rounds 0..{k} {t_legacy:8.2} ms"
        );
        (t_skip, t_legacy, t_fd, t_lagrange)
    }

    let (p_skip, p_legacy, p_fd, p_lag) = time_table(Poseidon16Precompile::<true>, 18, k, "poseidon16 2^18x110");
    let (e_skip, e_legacy, e_fd, e_lag) = time_table(ExecutionTable::<true>, 20, k, "execution  2^20x22 ");

    let fd_total = p_fd + e_fd;
    let lag_total = p_lag + e_lag;
    println!(
        "h4 gate: FD {fd_total:.2} ms vs Lagrange {lag_total:.2} ms -> {}",
        if fd_total < lag_total { "PASS" } else { "FAIL" }
    );

    let skip_total = p_skip + e_skip;
    let legacy_total = p_legacy + e_legacy;
    println!(
        "combined: skip {skip_total:.2} ms vs legacy {legacy_total:.2} ms -> {}",
        if skip_total < legacy_total { "PASS" } else { "FAIL" }
    );
    assert!(fd_total < lag_total, "h4 FD-vs-Lagrange timing gate FAILED");
    assert!(skip_total < legacy_total, "GO/NO-GO timing gate FAILED");
}
