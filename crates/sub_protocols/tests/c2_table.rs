//! C2 per-pair table equality test: verifies the C2 path produces identical
//! round polynomials vs the fresh-eval path, including padding rows and the
//! phase-1 → phase-2 transition. The bare round polynomials must be identical
//! elements every round (this is what makes C2 transcript-invariant), and the
//! final column evaluations must agree.
//!
//! Run in the dev profile to also exercise the in-session dual-compute
//! debug_assert (C2 accumulators vs fresh accumulators, every round).

use backend::*;
use lean_vm::{
    EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_8_COL_ADDR_LEFT_HI, POSEIDON_8_COL_ADDR_LEFT_LO,
    POSEIDON_8_COL_FLAG_OUT4, POSEIDON_8_COL_INPUT_START, POSEIDON_8_COL_MULTIPLICITY, POSEIDON_8_COL_OUT_LO,
    POSEIDON_8_COL_ROUND_START, Poseidon8Precompile, compute_poseidon8_witness, fill_trace_poseidon_8,
    num_cols_poseidon_8,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{AirSumcheckSession, OuterSumcheckSession};

/// Valid rows for `[0, non_padded)`; rows `[non_padded, 2^log_n_rows)` are
/// copies of row `non_padded - 1` (the production padding convention the C2
/// implicit tail relies on).
fn build_padded_poseidon_trace(log_n_rows: usize, non_padded: usize, rng: &mut StdRng) -> Vec<ArenaVec<F>> {
    let n_rows = 1 << log_n_rows;
    assert!(non_padded >= 1 && non_padded <= n_rows);
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
    for row in 0..non_padded {
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
    // Production padding: every row past the last real one repeats it.
    let last = non_padded - 1;
    for col in trace.iter_mut() {
        let v = col[last];
        for row in non_padded..n_rows {
            col[row] = v;
        }
    }
    trace
}

fn run_equality_case(log_n_rows: usize, non_padded: usize, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let trace = build_padded_poseidon_trace(log_n_rows, non_padded, &mut rng);

    let air = Poseidon8Precompile::<false>;
    let alpha: EF = rng.random();
    let alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints());

    let eq_factor: Vec<EF> = (0..log_n_rows).map(|_| rng.random()).collect();
    let sum: EF = rng.random(); // shared by both sessions; bare polys stay comparable

    let make_session = |c2: bool| {
        let cols: Vec<&[F]> = trace.iter().map(|c| c.as_slice()).collect();
        let packed = MleGroupRef::<EF>::Base(cols).pack();
        let extra = ExtraDataForBuses::new(&[], alpha_powers.clone());
        let mut s = AirSumcheckSession::new(packed, eq_factor.clone(), sum, air, extra, non_padded);
        s.set_c2_enabled_for_tests(c2);
        s
    };
    let mut s_c2 = make_session(true);
    let mut s_ref = make_session(false);

    for round in 0..log_n_rows {
        let p_c2 = s_c2.compute_bare_round_poly();
        let p_ref = s_ref.compute_bare_round_poly();
        assert_eq!(
            p_c2.coeffs, p_ref.coeffs,
            "bare round-poly mismatch at round {round} (n={log_n_rows}, non_padded={non_padded})"
        );
        let challenge: EF = rng.random();
        s_c2.process_challenge(challenge, &p_c2);
        s_ref.process_challenge(challenge, &p_ref);
    }
    assert_eq!(
        s_c2.final_column_evals(),
        s_ref.final_column_evals(),
        "final column evals mismatch (n={log_n_rows}, non_padded={non_padded})"
    );
}

/// Padding + straddles: 9000 of 2^14 rows -> padded to 12288 = 3 * 2^12; the
/// unpacked rounds walk 24 -> 12 -> 6 -> 3 -> ceil(3/2)=2 -> 1, exercising the
/// odd straddle pair (i1 lands on the implicit padding tail).
#[test]
fn c2_equality_padded_straddle() {
    run_equality_case(14, 9000, 7);
}

/// Half-full table: 4000 of 2^13 -> padded to 4096 = one chunk; analytic
/// padding contribution active from round 0.
#[test]
fn c2_equality_half_table() {
    run_equality_case(13, 4000, 11);
}

/// Full table (no padding at all): the active region equals the iteration
/// domain in every round.
#[test]
fn c2_equality_full_table() {
    run_equality_case(13, 1 << 13, 23);
}
