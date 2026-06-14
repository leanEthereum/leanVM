//! T2' (h6' C3a) — pins the poseidon degree census: the constraint composition
//! restricted to any fold line `C(lo + z*diff)` has true degree ≤ 7, although
//! `degree_air()` declares 8. Therefore the z=8 evaluation pass the prover used
//! to run is provably redundant (its interpolated top coefficient is zero), and
//! `degree_z() = 7` removes it without changing a single wire byte.
//!
//! The census is STRUCTURAL: it holds for any committed column values, and is
//! checked here on a real (witness-consistent) Poseidon8 trace.

use backend::*;
use lean_vm::{
    EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_8_COL_ADDR_LEFT_HI, POSEIDON_8_COL_ADDR_LEFT_LO,
    POSEIDON_8_COL_FLAG_OUT4, POSEIDON_8_COL_INPUT_START, POSEIDON_8_COL_MULTIPLICITY, POSEIDON_8_COL_OUT_LO,
    POSEIDON_8_COL_ROUND_START, Poseidon8Precompile, compute_poseidon8_witness, fill_trace_poseidon_8,
    num_cols_poseidon_8,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

fn build_real_poseidon_trace(log_n_rows: usize, rng: &mut StdRng) -> Vec<ArenaVec<F>> {
    let n_rows = 1 << log_n_rows;
    let n_cols = num_cols_poseidon_8();
    let mut trace: Vec<ArenaVec<F>> = (0..n_cols).map(|_| ArenaVec::filled(F::ZERO, n_rows)).collect();
    for t in trace.iter_mut().skip(POSEIDON_8_COL_INPUT_START).take(WIDTH) {
        *t = ArenaVec::from_iter((0..n_rows).map(|_| rng.random()));
    }
    trace[POSEIDON_8_COL_MULTIPLICITY] = ArenaVec::filled(F::ONE, n_rows);
    trace[POSEIDON_8_COL_FLAG_OUT4] = ArenaVec::filled(F::ONE, n_rows);
    trace[POSEIDON_8_COL_ADDR_LEFT_LO] = ArenaVec::filled(F::ZERO, n_rows);
    trace[POSEIDON_8_COL_ADDR_LEFT_HI] = ArenaVec::filled(F::from_usize(HALF_DIGEST_LEN), n_rows);
    #[allow(clippy::needless_range_loop)]
    for row in 0..n_rows {
        let input: [F; WIDTH] = std::array::from_fn(|i| trace[POSEIDON_8_COL_INPUT_START + i][row]);
        let (aux, perm_state) = compute_poseidon8_witness(input);
        for i in 0..WIDTH / 2 {
            trace[POSEIDON_8_COL_OUT_LO + i][row] = perm_state[i] + input[i];
        }
        for (i, v) in aux.iter().enumerate() {
            trace[POSEIDON_8_COL_ROUND_START + i][row] = *v;
        }
    }
    fill_trace_poseidon_8(&mut trace);
    trace
}

#[test]
fn poseidon_fold_line_degree_census() {
    let log_n_rows = 8usize;
    let n_rows = 1usize << log_n_rows;
    let mut rng = StdRng::seed_from_u64(42);
    let trace = build_real_poseidon_trace(log_n_rows, &mut rng);

    let air = Poseidon8Precompile::<false>;
    assert_eq!(air.degree_air(), 8);
    assert_eq!(air.degree_z(), 7);

    let alpha: EF = rng.random();
    let alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints());
    let extra_data = ExtraDataForBuses::new(&[], alpha_powers);

    for trial in 0..32 {
        // Random fold pair (i0, i1) — the fold line is `point + z*diff`.
        let i0 = (rng.random::<u64>() as usize) % n_rows;
        let mut i1 = (rng.random::<u64>() as usize) % n_rows;
        if i1 == i0 {
            i1 = (i1 + 1) % n_rows;
        }
        let lo: Vec<EF> = trace.iter().map(|c| EF::from(c[i0])).collect();
        let diff: Vec<EF> = trace.iter().map(|c| EF::from(c[i1]) - EF::from(c[i0])).collect();

        // Evaluate s(z) = C(lo + z*diff) at z = 0..=8 (the OLD point set).
        let evals9: Vec<(F, EF)> = (0..=8u64)
            .map(|z| {
                let zf = EF::from_u64(z);
                let point: Vec<EF> = lo.iter().zip(&diff).map(|(l, d)| *l + zf * *d).collect();
                (
                    F::from_u64(z),
                    <Poseidon8Precompile<false> as SumcheckComputation<EF>>::eval_extension(&air, &point, &extra_data),
                )
            })
            .collect();

        // (a) Census: the 9-point interpolant's top coefficient is EXACTLY zero.
        let poly9 = DensePolynomial::lagrange_interpolation(&evals9).unwrap();
        assert!(poly9.coeffs.len() <= 9, "trial {trial}: unexpected degree blowup");
        if poly9.coeffs.len() == 9 {
            assert_eq!(
                poly9.coeffs[8],
                EF::ZERO,
                "trial {trial}: poseidon fold-line composition has a non-zero z^8 coefficient — census violated"
            );
        }

        // (b) Old/new bare-poly equality: the degree-≤7 interpolant through the
        // NEW point set z = 0..=7 is the SAME polynomial (so the prover's
        // message coefficients are bit-identical).
        let poly8 = DensePolynomial::lagrange_interpolation(&evals9[..8]).unwrap();
        for k in 0..8 {
            let a = poly8.coeffs.get(k).copied().unwrap_or(EF::ZERO);
            let b = poly9.coeffs.get(k).copied().unwrap_or(EF::ZERO);
            assert_eq!(
                a, b,
                "trial {trial}: coefficient {k} differs between 8- and 9-point interpolants"
            );
        }
        // ...and it still passes through the omitted 9th point.
        assert_eq!(
            poly8.evaluate(EF::from_u64(8)),
            evals9[8].1,
            "trial {trial}: degree-7 interpolant fails at z=8"
        );
    }
}
