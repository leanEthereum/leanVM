use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;

mod air;
pub use air::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExecutionTable<const BUS: bool>;

impl<const BUS: bool> TableT for ExecutionTable<BUS> {
    fn name(&self) -> &'static str {
        "execution"
    }

    fn table(&self) -> Table {
        Table::execution()
    }

    fn is_execution_table(&self) -> bool {
        true
    }

    fn n_columns_total(&self) -> usize {
        N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS
    }

    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let bytecode_lookup = BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::One,
            domainsep: BusData::Constant(LOGUP_BYTECODE_DOMAINSEP),
            data: (0..N_INSTRUCTION_COLUMNS)
                .map(|i| BusData::Column(N_RUNTIME_COLUMNS + i))
                .chain(std::iter::once(BusData::Column(EXEC_COL_PC)))
                .collect(),
            deferred_claim: false,
        };
        let precompile_bus = BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::Column(EXEC_COL_FLAG_PRECOMPILE),
            domainsep: BusData::Column(EXEC_COL_AUX_2),
            data: vec![
                BusData::Column(EXEC_COL_NU_A),
                BusData::Column(EXEC_COL_NU_B),
                BusData::Column(EXEC_COL_NU_C),
            ],
            deferred_claim: false,
        };
        // Convention shared with the other tables: the unique Multiplicity::Column bus
        // comes first; everything that follows is Multiplicity::One.
        let mut buses = vec![precompile_bus, bytecode_lookup];
        // Deferred-claim memory buses (virtual address columns, order: A, B, C).
        buses.extend(memory_lookups_consecutive_with_claim(
            EXEC_COL_ADDR_A,
            EXEC_COL_VALUE_A,
            1,
            true,
        ));
        buses.extend(memory_lookups_consecutive_with_claim(
            EXEC_COL_ADDR_B,
            EXEC_COL_VALUE_B,
            1,
            true,
        ));
        buses.extend(memory_lookups_consecutive_with_claim(
            EXEC_COL_ADDR_C,
            EXEC_COL_VALUE_C,
            1,
            true,
        ));
        buses
    }

    fn padding_row(&self, _zero_vec_ptr: usize, _null_hash_ptr: usize, ending_pc: usize, mem0: F) -> Vec<F> {
        let mut padding_row = vec![F::ZERO; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS];
        padding_row[EXEC_COL_PC] = F::from_usize(ending_pc);
        padding_row[EXEC_COL_FLAG_JUMP] = F::ONE;
        padding_row[EXEC_COL_FLAG_A] = F::ONE;
        padding_row[EXEC_COL_OPERAND_A] = F::ONE;
        padding_row[EXEC_COL_FLAG_B] = F::ONE;
        padding_row[EXEC_COL_OPERAND_B] = F::from_usize(ending_pc); // jump dest = ending_pc (nu_b)
        padding_row[EXEC_COL_FLAG_C_FP] = F::ONE; // this is kind of arbitrary
        padding_row[EXEC_COL_NU_A] = F::ONE; // we always jump here (self-loop, so condition = nu_a = 1)
        padding_row[EXEC_COL_NU_B] = F::from_usize(ending_pc); // nu_b = jump dest = ending_pc
        // Virtual addresses evaluate to 0 on padding rows, so VALUE_* must = memory[0].
        padding_row[EXEC_COL_VALUE_A] = mem0;
        padding_row[EXEC_COL_VALUE_B] = mem0;
        padding_row[EXEC_COL_VALUE_C] = mem0;
        padding_row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        _: F,
        _: F,
        _: F,
        _: PrecompileCompTimeArgs<usize>,
        _: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        unreachable!()
    }
}

#[cfg(test)]
mod h9_layout_tests {
    use super::*;

    /// Padding row: virtual addresses all zero, VALUE_* = mem0.
    #[test]
    fn padding_row_satisfies_virtual_addresses() {
        let mem0 = F::from_usize(424242);
        let row = ExecutionTable::<true>.padding_row(999, 998, 7, mem0);
        assert_eq!(row.len(), N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS);
        assert_eq!(N_TOTAL_EXECUTION_COLUMNS, 17);
        assert_eq!(N_TEMPORARY_EXEC_COLUMNS, 7);

        let f = |i: usize| row[i];
        let one = F::ONE;
        let aux_1 = f(EXEC_COL_AUX_1);
        let flag_deref = (aux_1 * (aux_1 - one)).halve();
        let addr_a = (one - f(EXEC_COL_FLAG_A) - f(EXEC_COL_FLAG_AB_FP)) * (f(EXEC_COL_FP) + f(EXEC_COL_OPERAND_A));
        let addr_b = (one - f(EXEC_COL_FLAG_B) - f(EXEC_COL_FLAG_AB_FP)) * (f(EXEC_COL_FP) + f(EXEC_COL_OPERAND_B))
            + flag_deref * (f(EXEC_COL_VALUE_A) + f(EXEC_COL_OPERAND_B));
        let addr_c = (one - f(EXEC_COL_FLAG_C) - f(EXEC_COL_FLAG_C_FP)) * (f(EXEC_COL_FP) + f(EXEC_COL_OPERAND_C));
        assert_eq!(addr_a, F::ZERO);
        assert_eq!(addr_b, F::ZERO);
        assert_eq!(addr_c, F::ZERO);
        // temporaries mirror the closed forms on the padding row
        assert_eq!(f(EXEC_COL_ADDR_A), F::ZERO);
        assert_eq!(f(EXEC_COL_ADDR_B), F::ZERO);
        assert_eq!(f(EXEC_COL_ADDR_C), F::ZERO);
        // bus pushes are (0, mem0)
        assert_eq!(f(EXEC_COL_VALUE_A), mem0);
        assert_eq!(f(EXEC_COL_VALUE_B), mem0);
        assert_eq!(f(EXEC_COL_VALUE_C), mem0);
        // memory buses reference the temporary addr columns + committed value columns
        let buses = ExecutionTable::<true>.bus_interactions();
        let mem_groups = memory_lookup_groups(&buses);
        assert_eq!(mem_groups.len(), 3);
        for (g, (a, v)) in mem_groups.iter().zip([
            (EXEC_COL_ADDR_A, EXEC_COL_VALUE_A),
            (EXEC_COL_ADDR_B, EXEC_COL_VALUE_B),
            (EXEC_COL_ADDR_C, EXEC_COL_VALUE_C),
        ]) {
            assert_eq!(g.idx_col, a);
            assert_eq!(g.value_cols, vec![v]);
        }
    }
}
