from snark_lib import *
from whir import *
from hashing import *

N_TABLES = N_TABLES_PLACEHOLDER

LOGUP_GKR_N_VARS_TO_SEND_COEFFS = LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER
LOGUP_GKR_N_COEFFS_SENT = 2**LOGUP_GKR_N_VARS_TO_SEND_COEFFS

MIN_LOG_N_ROWS_PER_TABLE = MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MAX_LOG_N_ROWS_PER_TABLE = MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MIN_LOG_MEMORY_SIZE = MIN_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_LOG_MEMORY_SIZE = MAX_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_BUS_WIDTH = MAX_BUS_WIDTH_PLACEHOLDER
TOTAL_NUM_AIR_CONSTRAINTS = TOTAL_NUM_AIR_CONSTRAINTS_PLACEHOLDER
N_AIR_CONSTRAINTS = N_AIR_CONSTRAINTS_PLACEHOLDER  # n_constraints per table_index

LOGUP_MEMORY_DOMAINSEP = LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER
LOGUP_BYTECODE_DOMAINSEP = LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER
EXECUTION_TABLE_INDEX = EXECUTION_TABLE_INDEX_PLACEHOLDER

ONE_BUSES_DOMSEPS = ONE_BUSES_DOMSEPS_PLACEHOLDER  # [[_; num_buses]; N_TABLES]
ONE_BUSES_DATA_COLS = ONE_BUSES_DATA_COLS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_DATA_OFFSETS = ONE_BUSES_DATA_OFFSETS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_NEW_COLS = ONE_BUSES_NEW_COLS_PLACEHOLDER  # [[[_; n_new]; num_buses]; N_TABLES]

NUM_COLS_AIR = NUM_COLS_AIR_PLACEHOLDER

AIR_DEGREES = AIR_DEGREES_PLACEHOLDER  # [_; N_TABLES]
MAX_AIR_FULL_DEGREE = MAX_AIR_FULL_DEGREE_PLACEHOLDER
N_AIR_COLUMNS = N_AIR_COLUMNS_PLACEHOLDER  # [_; N_TABLES]
N_AIR_SHIFT_COLUMNS = N_AIR_SHIFT_COLUMNS_PLACEHOLDER  # [_; N_TABLES] — by convention, shift column j of table t is column j
AIR_ALPHA_OFFSETS = AIR_ALPHA_OFFSETS_PLACEHOLDER  # [_; N_TABLES], # AIR_ALPHA_OFFSETS[t] = sum(N_AIR_CONSTRAINTS[k] for k in range(t))

N_INSTRUCTION_COLUMNS = N_INSTRUCTION_COLUMNS_PLACEHOLDER
N_COMMITTED_EXEC_COLUMNS = N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER

LOG_GUEST_BYTECODE_LEN = LOG_GUEST_BYTECODE_LEN_PLACEHOLDER
COL_PC = COL_PC_PLACEHOLDER
TOTAL_WHIR_STATEMENTS = TOTAL_WHIR_STATEMENTS_PLACEHOLDER
STARTING_PC = STARTING_PC_PLACEHOLDER
ENDING_PC = ENDING_PC_PLACEHOLDER
BYTECODE_POINT_N_VARS = LOG_GUEST_BYTECODE_LEN + log2_ceil(N_INSTRUCTION_COLUMNS)
BYTECODE_ZERO_EVAL = BYTECODE_ZERO_EVAL_PLACEHOLDER
BYTECODE_CLAIM_SIZE = (BYTECODE_POINT_N_VARS + 1) * DIM
BYTECODE_CLAIM_SIZE_PADDED = next_multiple_of(BYTECODE_CLAIM_SIZE, DIGEST_LEN)
INNER_PUBLIC_MEMORY_LOG_SIZE = 3  # public input = 1 hash digest = 8 field elements
PUB_INPUT_SIZE = DIGEST_LEN  # the public input is a single digest


def recursion(inner_public_memory, bytecode_hash_domsep):
    proof_transcript_size_buf = Array(1)
    hint_witness("proof_transcript_size", proof_transcript_size_buf)
    proof_transcript = Array(proof_transcript_size_buf[0])
    hint_witness("proof_transcript", proof_transcript)
    fs: Mut = fs_new(proof_transcript)

    fs = fs_observe(fs, inner_public_memory, PUB_INPUT_SIZE)  # observe public input (the data digest)
    fs = fs_observe(fs, bytecode_hash_domsep, DIGEST_LEN)  # observe hash(bytecode hash, domain sep)

    # table dims
    debug_assert(N_TABLES + 1 < DIGEST_LEN)
    fs, dims = fs_receive_chunks(fs, 1)
    for i in unroll(N_TABLES + 2, 8):
        assert dims[i] == 0
    whir_log_inv_rate = dims[0]
    log_memory = dims[1]
    table_log_heights = dims + 2

    assert MIN_WHIR_LOG_INV_RATE <= whir_log_inv_rate
    assert whir_log_inv_rate <= MAX_WHIR_LOG_INV_RATE

    table_heights = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        table_log_height = table_log_heights[i]
        assert table_log_height <= MAX_LOG_N_ROWS_PER_TABLE[i]
        assert MIN_LOG_N_ROWS_PER_TABLE <= table_log_height
        table_heights[i] = two_exp(table_log_height)

    sorted_tables = Array(N_TABLES) # sorted_tables[0] is the index of the biggest table, sorted_tables[1] is the index of the second biggest table, etc
    hint_witness("table_sort_perm", sorted_tables)
    # Force table_sort_perm to be a permutation of {0..N_TABLES-1}
    perm_seen = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        p = sorted_tables[i]
        assert p < N_TABLES
        perm_seen[p] = i
    
    for i in unroll(0, N_TABLES - 1):
        height_curr = table_log_heights[sorted_tables[i]]
        height_next = table_log_heights[sorted_tables[i + 1]]
        assert height_next <= height_curr
        if height_curr == height_next:
            assert sorted_tables[i] < sorted_tables[i + 1]

    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert LOG_GUEST_BYTECODE_LEN <= log_memory

    log_max_table_height = table_log_heights[sorted_tables[0]]  # largest table's log height
    assert log_max_table_height <= log_memory
    log_n_cycles = table_log_heights[EXECUTION_TABLE_INDEX]

    log_bytecode_padded = maximum(LOG_GUEST_BYTECODE_LEN, log_max_table_height)

    stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode_padded, table_heights)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    n_vars_logup_gkr = compute_total_gkr_n_vars(log_memory, log_bytecode_padded, table_heights)

    n_buses_per_table = Array(N_TABLES) # indexed by table_index
    n_cols_per_table = Array(N_TABLES) # indexed by table_index
    for i in unroll(0, N_TABLES):
        n_buses_per_table[i] = len(ONE_BUSES_DOMSEPS[i]) + 1 # + 1 for the precompile bus interraction (the rest is memory / bytecode interractions)
        n_cols_per_table[i] = NUM_COLS_AIR[i]

    gkr_table_base_offset = Array(N_TABLES)
    stacked_table_base_offset = Array(N_TABLES)
    gkr_cumul: Mut = two_exp(log_memory) + two_exp(log_bytecode_padded)
    stacked_cumul: Mut = two_exp(log_memory) * 2 + two_exp(log_bytecode_padded)
    for sorted_pos in unroll(0, N_TABLES):
        ti = sorted_tables[sorted_pos]
        gkr_table_base_offset[ti] = gkr_cumul
        stacked_table_base_offset[ti] = stacked_cumul
        n_rows = table_heights[ti]
        gkr_cumul += n_rows * n_buses_per_table[ti]
        stacked_cumul += n_rows * n_cols_per_table[ti]

    num_oods = get_num_oods(whir_log_inv_rate, stacked_n_vars)
    num_ood_at_commitment = num_oods[0]
    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs, num_ood_at_commitment)

    fs, logup_c = fs_sample_ef(fs)

    fs = fs_duplex(fs)
    fs, logup_alphas = fs_sample_many_ef(fs, log2_ceil(MAX_BUS_WIDTH))

    logup_alphas_eq_poly = compute_eq_mle_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))

    # LOGUP

    fs, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs, n_vars_logup_gkr)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, n_vars_logup_gkr - log_memory, point_gkr)

    fs, value_acc = fs_receive_ef_inlined(fs, 1)
    fs, value_memory = fs_receive_ef_inlined(fs, 1)

    retrieved_numerators_value: Mut = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (n_vars_logup_gkr - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(LOGUP_MEMORY_DOMAINSEP, value_index, value_memory, logup_alphas_eq_poly)
    retrieved_denominators_value: Mut = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory)
    )

    bytecode_section_offset = two_exp(log_memory)

    bytecode_and_acc_point = point_gkr + (n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        bytecode_section_offset / 2**LOG_GUEST_BYTECODE_LEN, n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        bytecode_section_offset / two_exp(log_bytecode_padded), n_vars_logup_gkr - log_bytecode_padded, point_gkr
    )
    # Build padded claim data: [point | value | zero padding]
    bytecode_claim = Array(BYTECODE_CLAIM_SIZE_PADDED)
    copy_many_ef(bytecode_and_acc_point, bytecode_claim, LOG_GUEST_BYTECODE_LEN)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        bytecode_claim + LOG_GUEST_BYTECODE_LEN * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    hint_witness("bytecode_value_hint", bytecode_claim + BYTECODE_POINT_N_VARS * DIM)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        bytecode_claim[k] = 0
    bytecode_value = bytecode_claim + BYTECODE_POINT_N_VARS * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)):
        bytecode_value_corrected = mul_extension_ret(
            bytecode_value_corrected, one_minus_self_extension_ret(logup_alphas + i * DIM)
        )

    fs, value_bytecode_acc = fs_receive_ef_inlined(fs, 1)
    retrieved_numerators_value = sub_extension_ret(
        retrieved_numerators_value, mul_extension_ret(bytecode_multilinear_location_prefix, value_bytecode_acc)
    )

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point, LOG_GUEST_BYTECODE_LEN)
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_multilinear_location_prefix,
            sub_extension_ret(
                logup_c,
                add_extension_ret(
                    bytecode_value_corrected,
                    add_extension_ret(
                        mul_extension_ret(bytecode_index_value, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM),
                        mul_base_extension_ret(
                            LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
                        ),
                    ),
                ),
            ),
        ),
    )
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_padded_multilinear_location_prefix,
            mle_of_zeros_then_ones_pow2(
                point_gkr + (n_vars_logup_gkr - log_bytecode_padded) * DIM,
                LOG_GUEST_BYTECODE_LEN,
                log_bytecode_padded,
            ),
        ),
    )

    # Per-table data accumulators (indexed by table_index).
    bus_numerators_values = Array(N_TABLES * DIM)
    bus_denominators_values = Array(N_TABLES * DIM)
    pcs_points = DynArray([])
    pcs_values = DynArray([])
    pcs_values_shift = DynArray([])
    for table_index in unroll(0, N_TABLES):
        pcs_points.push(DynArray([]))
        pcs_values.push(DynArray([]))
        pcs_values[table_index].push(DynArray([]))
        pcs_values_shift.push(DynArray([]))
        pcs_values_shift[table_index].push(DynArray([]))
        for _ in unroll(0, NUM_COLS_AIR[table_index]):
            pcs_values[table_index][0].push(DynArray([]))
            pcs_values_shift[table_index][0].push(DynArray([]))

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        offset: Mut = gkr_table_base_offset[table_index]

        inner_point = point_gkr + (n_vars_logup_gkr - log_n_rows) * DIM
        pcs_points[table_index].push(inner_point)

        # Bus (data flow between tables — Multiplicity::Column)
        prefix = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

        fs, eval_on_selector = fs_receive_ef_inlined(fs, 1)
        retrieved_numerators_value = add_extension_ret(
            retrieved_numerators_value, mul_extension_ret(prefix, eval_on_selector)
        )

        fs, eval_on_data = fs_receive_ef_inlined(fs, 1)
        retrieved_denominators_value = add_extension_ret(
            retrieved_denominators_value, mul_extension_ret(prefix, eval_on_data)
        )

        copy_5(eval_on_selector, bus_numerators_values + table_index * DIM)
        copy_5(eval_on_data, bus_denominators_values + table_index * DIM)

        offset += n_rows

        # Multiplicity::One buses (bytecode lookup + memory lookups).
        for one_bus_idx in unroll(0, len(ONE_BUSES_DOMSEPS[table_index])):
            domsep = ONE_BUSES_DOMSEPS[table_index][one_bus_idx]
            n_new = len(ONE_BUSES_NEW_COLS[table_index][one_bus_idx])
            n_data = len(ONE_BUSES_DATA_COLS[table_index][one_bus_idx])

            fs, new_evals = fs_receive_ef_inlined(fs, n_new)

            for i in unroll(0, n_new):
                new_col = ONE_BUSES_NEW_COLS[table_index][one_bus_idx][i]
                debug_assert(len(pcs_values[table_index][0][new_col]) == 0)
                pcs_values[table_index][0][new_col].push(new_evals + i * DIM)

            data_evals = Array(n_data * DIM)
            for i in unroll(0, n_data):
                data_col = ONE_BUSES_DATA_COLS[table_index][one_bus_idx][i]
                data_ofs = ONE_BUSES_DATA_OFFSETS[table_index][one_bus_idx][i]
                src = pcs_values[table_index][0][data_col][0]
                if data_ofs == 0:
                    copy_5(src, data_evals + i * DIM)
                if data_ofs != 0:
                    copy_5(add_base_extension_ret(data_ofs, src), data_evals + i * DIM)

            pref = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)
            retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
            fingerp = fingerprint_n(domsep, data_evals, n_data, logup_alphas_eq_poly)
            retrieved_denominators_value = add_extension_ret(
                retrieved_denominators_value,
                mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
            )
            offset += n_rows

    # Final logup adjustment (padding)
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mle_of_zeros_then_ones(point_gkr, gkr_cumul, n_vars_logup_gkr),
    )

    copy_5(retrieved_numerators_value, numerators_value)
    copy_5(retrieved_denominators_value, denominators_value)

    memory_and_acc_point = point_gkr + (n_vars_logup_gkr - log_memory) * DIM

    # END OF LOGUP

    # VERIFY BUS AND AIR — back-loaded batched sumcheck

    fs, air_alpha = fs_sample_ef(fs)
    air_alpha_powers = powers_const(air_alpha, TOTAL_NUM_AIR_CONSTRAINTS)

    initial_sum: Mut = ZERO_VEC_PTR
    for table_index in unroll(0, N_TABLES):
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]
        bus_numerator_value = bus_numerators_values + table_index * DIM
        bus_denominator_value = bus_denominators_values + table_index * DIM

        signed_numerator: Mut = bus_numerator_value
        if table_index != EXECUTION_TABLE_INDEX:
            signed_numerator = opposite_extension_ret(signed_numerator)
        bus_final_value: Mut = mul_extension_ret(air_alpha_powers + alpha_offset * DIM, signed_numerator)
        bus_final_value = add_extension_ret(
            bus_final_value,
            mul_extension_ret(
                air_alpha_powers + (alpha_offset + 1) * DIM,
                sub_extension_ret(logup_c, bus_denominator_value),
            ),
        )
        initial_sum = add_extension_ret(initial_sum, bus_final_value)

    n_max = log_max_table_height
    # Batched AIR sumcheck:
    fs, all_challenges, batched_air_final_value = sumcheck_verify_reversed(fs, n_max, initial_sum, MAX_AIR_FULL_DEGREE)

    check_sum: Mut = ZERO_VEC_PTR
    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        n_flat_columns = N_AIR_COLUMNS[table_index]
        n_shift_columns = N_AIR_SHIFT_COLUMNS[table_index]
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]

        fs, inner_evals = fs_receive_ef_inlined(fs, n_flat_columns + n_shift_columns)

        air_constraints_eval = evaluate_air_constraints(
            table_index, inner_evals, air_alpha_powers + alpha_offset * DIM, logup_alphas_eq_poly
        )

        bus_point = pcs_points[table_index][0]
        eq_val = poly_eq_extension_dynamic_ret(bus_point, all_challenges, log_n_rows)

        k_t = product_first_n(all_challenges + log_n_rows * DIM, n_max - log_n_rows)

        contribution = mul_extension_ret(k_t, mul_extension_ret(eq_val, air_constraints_eval))
        check_sum = add_extension_ret(check_sum, contribution)

        pcs_points[table_index].push(all_challenges)
        pcs_values[table_index].push(DynArray([]))
        pcs_values_shift[table_index].push(DynArray([]))
        last_index = len(pcs_values[table_index]) - 1
        for _ in unroll(0, total_num_cols):
            pcs_values[table_index][last_index].push(DynArray([]))
            pcs_values_shift[table_index][last_index].push(DynArray([]))
        for i in unroll(0, n_flat_columns):
            pcs_values[table_index][last_index][i].push(inner_evals + i * DIM)
        if n_shift_columns != 0:
            evals_shift = inner_evals + n_flat_columns * DIM
            for i in unroll(0, n_shift_columns):
                pcs_values_shift[table_index][last_index][i].push(evals_shift + i * DIM)

    # verify that the AIR-batched sumcheck is valid
    copy_5(check_sum, batched_air_final_value)

    fs, public_memory_random_point = fs_sample_many_ef(fs, INNER_PUBLIC_MEMORY_LOG_SIZE)
    poly_eq_public_mem = compute_eq_mle_extension(public_memory_random_point, INNER_PUBLIC_MEMORY_LOG_SIZE)
    public_memory_eval = Array(DIM)
    dot_product_be(inner_public_memory, poly_eq_public_mem, public_memory_eval, 2**INNER_PUBLIC_MEMORY_LOG_SIZE)

    # WHIR BASE
    fs = fs_duplex(fs)
    combination_randomness_gen: Mut
    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers: Mut = powers(
        combination_randomness_gen, num_ood_at_commitment + TOTAL_WHIR_STATEMENTS
    )
    whir_sum: Mut = Array(DIM)
    dot_product_ee_dynamic(whir_base_ood_evals, combination_randomness_powers, whir_sum, num_ood_at_commitment)
    curr_randomness: Mut = combination_randomness_powers + num_ood_at_commitment * DIM

    whir_sum = add_extension_ret(mul_extension_ret(value_memory, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_acc, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(public_memory_eval, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_bytecode_acc, curr_randomness), whir_sum)
    curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
        if table_index == EXECUTION_TABLE_INDEX:
            whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(STARTING_PC), curr_randomness), whir_sum)
            curr_randomness += DIM
            whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(ENDING_PC), curr_randomness), whir_sum)
            curr_randomness += DIM
        debug_assert(len(pcs_points[table_index]) == len(pcs_values[table_index]))
        for i in unroll(0, len(pcs_values[table_index])):
            # next_mle-weighted (shift) values come first
            for j in unroll(0, len(pcs_values_shift[table_index][i])):
                if len(pcs_values_shift[table_index][i][j]) == 1:
                    whir_sum = add_extension_ret(
                        mul_extension_ret(pcs_values_shift[table_index][i][j][0], curr_randomness),
                        whir_sum,
                    )
                    curr_randomness += DIM
            # eq-weighted (up) values
            for j in unroll(0, len(pcs_values[table_index][i])):
                debug_assert(len(pcs_values[table_index][i][j]) < 2)
                if len(pcs_values[table_index][i][j]) == 1:
                    whir_sum = add_extension_ret(
                        mul_extension_ret(pcs_values[table_index][i][j][0], curr_randomness),
                        whir_sum,
                    )
                    curr_randomness += DIM

    folding_randomness_global: Mut
    s: Mut
    final_value: Mut
    end_sum: Mut
    fs, folding_randomness_global, s, final_value, end_sum = whir_open(
        fs,
        stacked_n_vars,
        whir_log_inv_rate,
        whir_base_root,
        whir_base_ood_points,
        combination_randomness_powers,
        whir_sum,
    )

    curr_randomness = combination_randomness_powers + num_ood_at_commitment * DIM

    eq_memory_and_acc_point = poly_eq_extension_dynamic_ret(
        folding_randomness_global + (stacked_n_vars - log_memory) * DIM,
        memory_and_acc_point,
        log_memory,
    )
    prefix_memory = multilinear_location_prefix(0, stacked_n_vars - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    prefix_acc_memory = multilinear_location_prefix(1, stacked_n_vars - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_acc_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    eq_pub_mem = Array(DIM)
    poly_eq_ee(
        folding_randomness_global + (stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE) * DIM,
        public_memory_random_point,
        eq_pub_mem,
        INNER_PUBLIC_MEMORY_LOG_SIZE,
    )
    prefix_pub_mem = multilinear_location_prefix(
        0, stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE, folding_randomness_global
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness += DIM

    bytecode_acc_layout_offset = two_exp(log_memory) * 2  # memory + acc_memory

    eq_bytecode_acc = Array(DIM)
    poly_eq_ee(
        folding_randomness_global + (stacked_n_vars - LOG_GUEST_BYTECODE_LEN) * DIM,
        bytecode_and_acc_point,
        eq_bytecode_acc,
        LOG_GUEST_BYTECODE_LEN,
    )
    prefix_bytecode_acc = multilinear_location_prefix(
        bytecode_acc_layout_offset / 2**LOG_GUEST_BYTECODE_LEN,
        stacked_n_vars - LOG_GUEST_BYTECODE_LEN,
        folding_randomness_global,
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_bytecode_acc), eq_bytecode_acc),
    )
    curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        table_offset = stacked_table_base_offset[table_index]

        if table_index == EXECUTION_TABLE_INDEX:
            prefix_pc_start = multilinear_location_prefix(
                table_offset + COL_PC * two_exp(log_n_cycles),
                stacked_n_vars,
                folding_randomness_global,
            )
            s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_start))
            curr_randomness += DIM

            prefix_pc_end = multilinear_location_prefix(
                table_offset + (COL_PC + 1) * two_exp(log_n_cycles) - 1,
                stacked_n_vars,
                folding_randomness_global,
            )
            s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_end))
            curr_randomness += DIM

        column_prefixes = compute_column_prefixes(
            table_offset / n_rows,
            stacked_n_vars - log_n_rows,
            folding_randomness_global,
            total_num_cols,
        )
        for i in unroll(0, len(pcs_points[table_index])):
            point = pcs_points[table_index][i]
            inner_folding = folding_randomness_global + (stacked_n_vars - log_n_rows) * DIM
            n_shift_columns = N_AIR_SHIFT_COLUMNS[table_index]

            # next_mle (shift) values
            if n_shift_columns != 0:
                next_factor = next_mle(point, inner_folding, log_n_rows)
                for j in unroll(0, total_num_cols):
                    if len(pcs_values_shift[table_index][i][j]) == 1:
                        prefix = column_prefixes + j * DIM
                        s = add_extension_ret(
                            s,
                            mul_extension_ret(mul_extension_ret(curr_randomness, prefix), next_factor),
                        )
                        curr_randomness += DIM
            # eq (flat) values
            eq_factor = poly_eq_extension_dynamic_ret(point, inner_folding, log_n_rows)
            for j in unroll(0, total_num_cols):
                if len(pcs_values[table_index][i][j]) == 1:
                    prefix = column_prefixes + j * DIM
                    s = add_extension_ret(
                        s,
                        mul_extension_ret(mul_extension_ret(curr_randomness, prefix), eq_factor),
                    )
                    curr_randomness += DIM

    copy_5(mul_extension_ret(s, final_value), end_sum)

    return bytecode_claim


def multilinear_location_prefix(offset, n_vars, point):
    bits = checked_decompose_bits_small_value(offset, n_vars)
    res = poly_eq_base_extension(bits, point, n_vars)
    return res


def compute_column_prefixes(first_col_offset, n_vars, point, n_cols: Const):
    K = log2_ceil(n_cols)
    debug_assert(0 < K)
    debug_assert(K <= n_vars)
    high_n_vars = n_vars - K

    # low factor: eq(., point[high_n_vars:]) for every K-bit pattern
    low_eq = compute_eq_mle_extension(point + high_n_vars * DIM, K)

    # high factors for q = floor(first_col_offset / 2^K) and for the last column's q (q or q+1)
    bits_first = checked_decompose_bits_small_value(first_col_offset, n_vars)
    bits_last = checked_decompose_bits_small_value(first_col_offset + n_cols - 1, n_vars)
    high_eq_lo = poly_eq_base_extension_or_one(bits_first, point, high_n_vars)
    high_eq_hi = poly_eq_base_extension_or_one(bits_last, point, high_n_vars)

    # column_prefixes[w]        = eq(q,   point_high) * low_eq[w]   for w in [0, 2^K)
    # column_prefixes[2^K + w]  = eq(q+1, point_high) * low_eq[w]   for w in [0, 2^K)
    column_prefixes = Array(2 ** (K + 1) * DIM)
    for w in unroll(0, 2**K):
        mul_extension(high_eq_lo, low_eq + w * DIM, column_prefixes + w * DIM)
        mul_extension(high_eq_hi, low_eq + w * DIM, column_prefixes + (2**K + w) * DIM)

    # r = first_col_offset mod 2^K (low K bits; big-endian bits, index n_vars-1 is the LSB)
    r: Mut = bits_first[n_vars - 1]
    for i in unroll(1, K):
        r += bits_first[n_vars - 1 - i] * 2**i

    # Column j lands at index r + j < 2^K + n_cols <= 2^(K+1).

    return column_prefixes + r * DIM


def fingerprint_2(table_index, data_1, data_2, logup_alphas_eq_poly):
    buff = Array(DIM * 2)
    copy_5(data_1, buff)
    copy_5(data_2, buff + DIM)
    res: Mut = dot_product_ee_ret(buff, logup_alphas_eq_poly, 2)
    res = add_extension_ret(
        res, mul_base_extension_ret(table_index, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
    )
    return res


@inline
def fingerprint_n(domsep, data_evals, n, logup_alphas_eq_poly):
    res: Mut = dot_product_ee_ret(data_evals, logup_alphas_eq_poly, n)
    res = add_extension_ret(
        res,
        mul_base_extension_ret(domsep, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
    )
    return res


def verify_gkr_quotient(fs: Mut, n_vars):
    fs, nums = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)
    fs, denoms = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)

    initial_quotients = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT):
        div_extension(nums + k * DIM, denoms + k * DIM, initial_quotients + k * DIM)
    debug_assert(NUM_REPEATED_ONES <= LOGUP_GKR_N_COEFFS_SENT)
    debug_assert(LOGUP_GKR_N_COEFFS_SENT % NUM_REPEATED_ONES == 0)
    quotient: Mut = ZERO_VEC_PTR
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES):
        quotient = add_extension_ret(
            quotient, sum_continuous_ef(initial_quotients + k * NUM_REPEATED_ONES * DIM, NUM_REPEATED_ONES)
        )

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    fs, initial_point = fs_sample_many_ef(fs, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)
    points[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = initial_point

    point_poly_eq = compute_eq_mle_extension(initial_point, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)

    first_claim_num = dot_product_ee_ret(nums, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    first_claim_den = dot_product_ee_ret(denoms, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    claims_num[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_num
    claims_den[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_den

    for i in range(LOGUP_GKR_N_VARS_TO_SEND_COEFFS, n_vars):
        fs, points[i], claims_num[i], claims_den[i] = verify_gkr_quotient_step(
            fs, i, points[i - 1], claims_num[i - 1], claims_den[i - 1]
        )

    return (
        fs,
        quotient,
        points[n_vars - 1],
        claims_num[n_vars - 1],
        claims_den[n_vars - 1],
    )


def verify_gkr_quotient_step(fs: Mut, n_vars, point, claim_num, claim_den):
    fs = fs_duplex(fs)
    fs, alpha = fs_sample_ef(fs)
    alpha_mul_claim_den = mul_extension_ret(alpha, claim_den)
    num_plus_alpha_mul_claim_den = add_extension_ret(claim_num, alpha_mul_claim_den)
    postponed_point = Array((n_vars + 1) * DIM)
    fs, postponed_value = sumcheck_verify_reversed_helper(fs, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point)
    fs, inner_evals = fs_receive_ef_inlined(fs, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = poly_eq_extension_dynamic_ret(point, postponed_point, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    fs, beta = fs_sample_ef(fs)

    point_poly_eq = compute_eq_mle_extension(beta, 1)
    new_claim_num = dot_product_ee_ret(inner_evals, point_poly_eq, 2)
    new_claim_den = dot_product_ee_ret(inner_evals + 2 * DIM, point_poly_eq, 2)

    copy_5(beta, postponed_point + n_vars * DIM)

    return fs, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = two_exp(log_memory + 1)  # memory + acc_memory
    total += two_exp(log_bytecode_padded)
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total += n_rows * NUM_COLS_AIR[table_index]
    debug_assert(30 - 24 < MIN_LOG_N_ROWS_PER_TABLE)  # cf log2_ceil
    return MIN_LOG_N_ROWS_PER_TABLE + log2_ceil_runtime(total / 2**MIN_LOG_N_ROWS_PER_TABLE)


def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = two_exp(log_memory)
    total += two_exp(log_bytecode_padded)
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        # +1 for the Multiplicity::Column bus, plus one block per Multiplicity::One bus.
        n_buses = len(ONE_BUSES_DOMSEPS[table_index]) + 1
        total += n_rows * n_buses
    return log2_ceil_runtime(total)


def evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, logup_alphas_eq_poly):
    res: Imu
    debug_assert(table_index < N_TABLES)
    match table_index:
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
    return res


EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
