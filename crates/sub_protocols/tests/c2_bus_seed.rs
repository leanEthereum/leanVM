//! C2 bus-only seeding test: on every valid row, the bus-only accumulator
//! must equal the full constraint accumulator (non-bus gates vanish row-wise).

use backend::*;
use lean_vm::{
    EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_8_COL_ADDR_LEFT_HI, POSEIDON_8_COL_ADDR_LEFT_LO,
    POSEIDON_8_COL_FLAG_OUT4, POSEIDON_8_COL_INPUT_START, POSEIDON_8_COL_MULTIPLICITY, POSEIDON_8_COL_OUT_LO,
    POSEIDON_8_COL_ROUND_START, Poseidon8Precompile, compute_poseidon8_witness, fill_trace_poseidon_8,
    num_cols_poseidon_8,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

#[test]
fn busonly_equals_full_on_valid_rows() {
    let log_n_rows = 10usize;
    let n_rows = 1usize << log_n_rows;
    let non_padded = 900usize;
    let mut rng = StdRng::seed_from_u64(99);

    // Witness-consistent trace, production padding (rows >= non_padded repeat
    // the last real row).
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
    let last = non_padded - 1;
    for col in trace.iter_mut() {
        let v = col[last];
        for row in non_padded..n_rows {
            col[row] = v;
        }
    }

    // Production-shaped bus data: 2^LOG_MAX_BUS_WIDTH eq-table entries.
    let air = Poseidon8Precompile::<true>;
    let alpha: EF = rng.random();
    let alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints());
    let bus_point: Vec<EF> = (0..4).map(|_| rng.random()).collect();
    let logup_alphas_eq: Vec<EF> = eval_eq(&bus_point).to_vec();
    let extra = ExtraDataForBuses::new(&logup_alphas_eq, alpha_powers);

    let mut mismatches = 0usize;
    for row in 0..n_rows {
        let point: Vec<EF> = trace.iter().map(|c| EF::from(c[row])).collect();
        let full = {
            let mut folder = ConstraintFolder::new(&point[..air.n_columns()], &point[air.n_columns()..], &extra);
            Air::eval(&air, &mut folder, &extra);
            folder.accumulator
        };
        let bus_only = {
            let mut folder = ConstraintFolder::new(&point[..air.n_columns()], &point[air.n_columns()..], &extra);
            Air::eval_bus_only(&air, &mut folder, &extra);
            folder.accumulator
        };
        if full != bus_only {
            mismatches += 1;
            if mismatches <= 3 {
                eprintln!("row {row}: full = {full:?}, bus_only = {bus_only:?}");
            }
        }
    }
    assert_eq!(mismatches, 0, "bus-only != full on {mismatches} of {n_rows} rows");
}
