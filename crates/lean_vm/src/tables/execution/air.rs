use crate::{EF, ExecutionTable, ExtraDataForBuses, LOGUP_MEMORY_DOMAINSEP, eval_bus_data_only, eval_bus_virtual};
use backend::*;

pub const N_RUNTIME_COLUMNS: usize = 5;
pub const N_INSTRUCTION_COLUMNS: usize = 12;
pub const N_TOTAL_EXECUTION_COLUMNS: usize = N_INSTRUCTION_COLUMNS + N_RUNTIME_COLUMNS;

// Committed columns (IMPORTANT: they must be the first columns)
// ADDR_A/B/C are virtual (temporary) — derived from committed columns below.
pub const EXEC_COL_PC: usize = 0;
pub const EXEC_COL_FP: usize = 1;
pub const EXEC_COL_VALUE_A: usize = 2;
pub const EXEC_COL_VALUE_B: usize = 3;
pub const EXEC_COL_VALUE_C: usize = 4;

// Decoded instruction columns
pub const EXEC_COL_OPERAND_A: usize = 5;
pub const EXEC_COL_OPERAND_B: usize = 6;
pub const EXEC_COL_OPERAND_C: usize = 7;
pub const EXEC_COL_FLAG_A: usize = 8;
pub const EXEC_COL_FLAG_B: usize = 9;
pub const EXEC_COL_FLAG_C: usize = 10;
pub const EXEC_COL_FLAG_C_FP: usize = 11;
pub const EXEC_COL_FLAG_AB_FP: usize = 12;
pub const EXEC_COL_FLAG_MUL: usize = 13;
pub const EXEC_COL_FLAG_JUMP: usize = 14;
pub const EXEC_COL_AUX_1: usize = 15;
pub const EXEC_COL_AUX_2: usize = 16;

// Temporary columns (stored to avoid duplicate computations; NOT committed)
pub const N_TEMPORARY_EXEC_COLUMNS: usize = 7;
pub const EXEC_COL_ADDR_A: usize = 17;
pub const EXEC_COL_ADDR_B: usize = 18;
pub const EXEC_COL_ADDR_C: usize = 19;
pub const EXEC_COL_FLAG_PRECOMPILE: usize = 20;
pub const EXEC_COL_NU_A: usize = 21;
pub const EXEC_COL_NU_B: usize = 22;
pub const EXEC_COL_NU_C: usize = 23;

impl<const BUS: bool> Air for ExecutionTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        N_TOTAL_EXECUTION_COLUMNS
    }
    fn degree_air(&self) -> usize {
        5
    }
    // C2 not profitable: 14-constraint eval is too cheap to amortize the cache overhead.
    fn c2_table_profitable(&self) -> bool {
        false
    }
    fn n_shift_columns(&self) -> usize {
        2
    }
    fn n_constraints(&self) -> usize {
        13
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flat = builder.flat();
        let shift = builder.shift();

        let pc_shift = shift[EXEC_COL_PC];
        let fp_shift = shift[EXEC_COL_FP];

        let (operand_a, operand_b, operand_c) = (
            flat[EXEC_COL_OPERAND_A],
            flat[EXEC_COL_OPERAND_B],
            flat[EXEC_COL_OPERAND_C],
        );
        let (flag_a, flag_b, flag_c) = (flat[EXEC_COL_FLAG_A], flat[EXEC_COL_FLAG_B], flat[EXEC_COL_FLAG_C]);
        let flag_c_fp = flat[EXEC_COL_FLAG_C_FP];
        let flag_ab_fp = flat[EXEC_COL_FLAG_AB_FP];
        let flag_mul = flat[EXEC_COL_FLAG_MUL];
        let flag_jump = flat[EXEC_COL_FLAG_JUMP];
        let aux_1 = flat[EXEC_COL_AUX_1];
        let aux_2 = flat[EXEC_COL_AUX_2];

        let (value_a, value_b, value_c) = (flat[EXEC_COL_VALUE_A], flat[EXEC_COL_VALUE_B], flat[EXEC_COL_VALUE_C]);
        let pc = flat[EXEC_COL_PC];
        let fp = flat[EXEC_COL_FP];

        let one_minus_flag_a_and_flag_ab_fp = -(flag_a + flag_ab_fp - AB::F::ONE);
        let one_minus_flag_b_and_flag_ab_fp = -(flag_b + flag_ab_fp - AB::F::ONE);
        let one_minus_flag_c_and_flag_c_fp = -(flag_c + flag_c_fp - AB::F::ONE);

        let nu_a = flag_a * operand_a + one_minus_flag_a_and_flag_ab_fp * value_a + flag_ab_fp * (fp + operand_a);
        let nu_b = flag_b * operand_b + one_minus_flag_b_and_flag_ab_fp * value_b + flag_ab_fp * (fp + operand_b);
        let nu_c = flag_c * operand_c + one_minus_flag_c_and_flag_c_fp * value_c + flag_c_fp * (fp + operand_c);

        let fp_plus_operand_a = fp + operand_a;
        let fp_plus_operand_b = fp + operand_b;
        let fp_plus_operand_c = fp + operand_c;
        let pc_plus_one = pc + AB::F::ONE;
        let nu_a_minus_one = nu_a - AB::F::ONE;

        let flag_add = aux_1 * AB::F::TWO - aux_1 * aux_1;
        let flag_deref = (aux_1 * (aux_1 - AB::F::ONE)).halve();
        let flag_precompile = -(flag_add + flag_mul + flag_deref + flag_jump - AB::F::ONE);

        // Virtual addresses: closed-form expressions of committed columns.
        let addr_a = one_minus_flag_a_and_flag_ab_fp * fp_plus_operand_a;
        let addr_b = one_minus_flag_b_and_flag_ab_fp * fp_plus_operand_b + flag_deref * (value_a + operand_b);
        let addr_c = one_minus_flag_c_and_flag_c_fp * fp_plus_operand_c;

        if BUS {
            eval_bus_virtual::<AB, EF>(builder, extra_data, flag_precompile, aux_2, &[nu_a, nu_b, nu_c]);
            // Deferred memory-bus claims (order must match verifier's initial_sum loop).
            eval_bus_data_only::<AB, EF>(builder, extra_data, LOGUP_MEMORY_DOMAINSEP, &[addr_a, value_a]);
            eval_bus_data_only::<AB, EF>(builder, extra_data, LOGUP_MEMORY_DOMAINSEP, &[addr_b, value_b]);
            eval_bus_data_only::<AB, EF>(builder, extra_data, LOGUP_MEMORY_DOMAINSEP, &[addr_c, value_c]);
        } else {
            builder.declare_values(&[flag_precompile]);
            builder.declare_values(&[nu_a, nu_b, nu_c, aux_2]);
            builder.declare_values(&[addr_a, addr_b, addr_c]);
        }

        builder.assert_zero(flag_add * (nu_b - (nu_a + nu_c)));
        builder.assert_zero(flag_mul * (nu_b - nu_a * nu_c));

        // DEREF: result in value_B, compared to nu_C
        builder.assert_zero(flag_deref * (value_b - nu_c));

        let jump_and_condition = flag_jump * nu_a;

        builder.assert_zero(jump_and_condition * nu_a_minus_one);
        builder.assert_zero(jump_and_condition * (pc_shift - nu_b));
        builder.assert_zero(jump_and_condition * (fp_shift - nu_c));
        let not_jump_and_condition = -(jump_and_condition - AB::F::ONE);
        builder.assert_zero(not_jump_and_condition * (pc_shift - pc_plus_one));
        builder.assert_zero(not_jump_and_condition * (fp_shift - fp));
    }
}

pub const fn instr_idx(col_index_in_air: usize) -> usize {
    col_index_in_air - N_RUNTIME_COLUMNS
}
