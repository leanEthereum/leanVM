use std::collections::BTreeMap;

use crate::*;
use backend::{Proof, RawProof, VerifierState};
use lean_vm::*;
use sub_protocols::*;
use utils::{ToUsize, from_end, get_poseidon16};

#[derive(Debug, Clone)]
pub struct ProofVerificationDetails {
    pub bytecode_evaluation: Evaluation<EF>,
    pub sorted_table_perm: Vec<usize>,
}

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof: Proof<F>,
) -> Result<(ProofVerificationDetails, RawProof<F>), ProofError> {
    if bytecode.log_size() > MAX_BYTECODE_LOG_SIZE {
        return Err(ProofError::TooBigBytecode {
            current_log_size: bytecode.log_size(),
            max_log_size: MAX_BYTECODE_LOG_SIZE,
        });
    }
    if public_input.len() != bytecode.public_input_size {
        return Err(ProofError::InvalidProof);
    }
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone())?;
    verifier_state.observe_scalars(public_input);
    verifier_state.observe_scalars(&fiat_shamir_domain_sep(bytecode));
    let dims = verifier_state
        .next_base_scalars_vec(2 + N_TABLES)?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>();
    let log_inv_rate = dims[0];
    let log_memory = dims[1];
    let table_n_vars: BTreeMap<Table, VarCount> = (0..N_TABLES).map(|i| (ALL_TABLES[i], dims[i + 2])).collect();
    check_rate(log_inv_rate)?;
    if log_memory < log2_strict_usize(bytecode.public_input_size) {
        return Err(ProofError::InvalidProof);
    }
    let whir_config = default_whir_config(log_inv_rate);
    for (table, &log_n_rows) in &table_n_vars {
        if log_n_rows < MIN_LOG_N_ROWS_PER_TABLE {
            return Err(ProofError::InvalidProof);
        }
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
    }
    // check memory is bigger than any other table
    if log_memory < (*table_n_vars.values().max().unwrap()).max(bytecode.log_size()) {
        return Err(ProofError::InvalidProof);
    }

    let public_memory = padd_with_zero_to_next_power_of_two(public_input);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    if bytecode.log_size() < MIN_BYTECODE_LOG_SIZE {
        return Err(ProofError::InvalidProof);
    }

    let parsed_commitment = stacked_pcs_parse_commitment(
        &whir_config,
        &mut verifier_state,
        log_memory,
        bytecode.log_size(),
        &table_n_vars,
    )?;

    let logup_c = verifier_state.sample();
    verifier_state.duplex();
    let logup_alphas = verifier_state.sample_vec(LOG_MAX_BUS_WIDTH);
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = verify_generic_logup(
        &mut verifier_state,
        logup_c,
        &logup_alphas,
        &logup_alphas_eq_poly,
        log_memory,
        &bytecode.instructions_multilinear,
        &table_n_vars,
    )?;
    let gkr_point = &logup_statements.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        let log_n = table_n_vars[&table];
        committed_statements.insert(
            table,
            vec![(
                MultilinearPoint(from_end(gkr_point, log_n).to_vec()),
                logup_statements.columns_values[&table].clone(),
                BTreeMap::new(),
            )],
        );
    }

    let air_alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(total_air_constraints());

    struct TableVerifyData {
        table: Table,
        extra_data: ExtraDataForBuses<EF>,
    }
    let mut verify_data: Vec<TableVerifyData> = Vec::new();
    let mut initial_sum = EF::ZERO;
    let mut alpha_offset = 0;

    for table in ALL_TABLES {
        let n_constraints = table.n_constraints();
        let bus_numerator_value = logup_statements.bus_numerators_values[&table];
        let bus_denominator_value = logup_statements.bus_denominators_values[&table];
        let signed_numerator = bus_numerator_value
            * match table.bus_interactions()[0].direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            };
        initial_sum += air_alpha_powers[alpha_offset] * signed_numerator
            + air_alpha_powers[alpha_offset + 1] * (logup_c - bus_denominator_value);

        let alpha_slice = air_alpha_powers[alpha_offset..alpha_offset + n_constraints].to_vec();
        verify_data.push(TableVerifyData {
            table,
            extra_data: ExtraDataForBuses::new(logup_alphas_eq_poly.clone(), alpha_slice),
        });

        alpha_offset += n_constraints;
    }

    let max_full_degree = ALL_TABLES.iter().map(|t| t.degree_air() + 1).max().unwrap();

    let n_max = *table_n_vars.values().max().unwrap();
    let Evaluation {
        point: sumcheck_air_point,
        value: claimed_air_final_value,
    } = sumcheck_verify(&mut verifier_state, n_max, max_full_degree, initial_sum, None)?;

    let mut my_air_final_value = EF::ZERO;
    for vd in &verify_data {
        let n_cols_total = vd.table.n_columns() + vd.table.n_shift_columns();
        let col_evals = verifier_state.next_extension_scalars_vec(n_cols_total)?;

        macro_rules! eval_constraint {
            ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &col_evals, &vd.extra_data) }};
        }
        let constraint_eval = delegate_to_inner!(&vd.table => eval_constraint);

        let bus_point = from_end(gkr_point, table_n_vars[&vd.table]);
        let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, table_n_vars[&vd.table]);
        my_air_final_value += back_loaded_table_contribution(
            bus_point,
            &sumcheck_air_point.0,
            &natural_ordering_point,
            constraint_eval,
        );

        macro_rules! split {
            ($t:expr) => {{ columns_evals_flat_and_shift($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(&vd.table => split);

        committed_statements.get_mut(&vd.table).unwrap().push(claim);
    }

    if my_air_final_value != claimed_air_final_value {
        return Err(ProofError::InvalidProof);
    }

    let public_memory_random_point =
        MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(public_memory.len())));
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);

    let previous_statements = vec![
        SparseStatement::new(
            parsed_commitment.num_variables,
            logup_statements.memory_and_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_memory_acc),
            ],
        ),
        SparseStatement::new(
            parsed_commitment.num_variables,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
        SparseStatement::new(
            parsed_commitment.num_variables,
            logup_statements.bytecode_and_acc_point,
            vec![SparseValue::new(
                (2 << log_memory) >> bytecode.log_size(),
                logup_statements.value_bytecode_acc,
            )],
        ),
    ];

    let global_statements_base = stacked_pcs_global_statements(
        parsed_commitment.num_variables,
        log_memory,
        bytecode.log_size(),
        bytecode.ending_pc,
        previous_statements,
        &table_n_vars,
        &committed_statements,
    );

    // sanity check (not necessary for soundness)
    let num_whir_statements = global_statements_base.iter().map(|s| s.values.len()).sum::<usize>();
    assert_eq!(num_whir_statements, total_whir_statements());

    WhirConfig::new(&whir_config, parsed_commitment.num_variables).verify(
        &mut verifier_state,
        &parsed_commitment,
        global_statements_base,
    )?;

    let sorted_table_perm: Vec<usize> = sort_tables_by_height(&table_n_vars)
        .into_iter()
        .map(|(t, _)| t.index())
        .collect();
    Ok((
        ProofVerificationDetails {
            bytecode_evaluation: logup_statements.bytecode_evaluation.unwrap(),
            sorted_table_perm,
        },
        verifier_state.into_raw_proof(),
    ))
}

fn back_loaded_table_contribution<EF: ExtensionField<PF<EF>>>(
    bus_point: &[EF],
    sumcheck_air_point: &[EF],
    natural_ordering_point: &[EF],
    constraint_eval: EF,
) -> EF {
    let n_t = bus_point.len();
    let n_max = sumcheck_air_point.len();
    let suffix_start = n_max - n_t;
    assert_eq!(natural_ordering_point.len(), n_t);
    let eq_val =
        MultilinearPoint(bus_point.to_vec()).eq_poly_outside(&MultilinearPoint(natural_ordering_point.to_vec()));
    let k_t: EF = sumcheck_air_point[..suffix_start].iter().copied().product();
    k_t * eq_val * constraint_eval
}
