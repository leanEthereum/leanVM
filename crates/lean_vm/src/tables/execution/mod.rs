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
                .chain(std::iter::once(BusData::Column(COL_PC)))
                .collect(),
        };
        let precompile_bus = BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::Column(COL_IS_PRECOMPILE),
            domainsep: BusData::Column(COL_PRECOMPILE_DOMAINSEP),
            data: vec![
                BusData::Column(COL_EXEC_NU_A),
                BusData::Column(COL_EXEC_NU_B),
                BusData::Column(COL_EXEC_NU_C),
            ],
        };
        // Convention shared with the other tables: the unique Multiplicity::Column bus
        // comes first; everything that follows is Multiplicity::One.
        let mut buses = vec![precompile_bus, bytecode_lookup];
        buses.extend(memory_lookups_consecutive(COL_MEM_ADDRESS_A, COL_MEM_VALUE_A, 1));
        buses.extend(memory_lookups_consecutive(COL_MEM_ADDRESS_B, COL_MEM_VALUE_B, 1));
        buses.extend(memory_lookups_consecutive(COL_MEM_ADDRESS_C, COL_MEM_VALUE_C, 1));
        buses
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, ending_pc: usize) -> Vec<F> {
        let mut padding_row = vec![F::ZERO; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS];
        padding_row[COL_PC] = F::from_usize(ending_pc);
        padding_row[COL_JUMP] = F::ONE;
        padding_row[COL_FLAG_A] = F::ONE;
        padding_row[COL_OPERAND_A] = F::ONE;
        padding_row[COL_FLAG_B] = F::ONE;
        padding_row[COL_OPERAND_B] = F::from_usize(ending_pc); // jump dest = ending_pc (nu_b)
        padding_row[COL_FLAG_C_FP] = F::ONE; // this is kind of arbitrary
        padding_row[COL_EXEC_NU_A] = F::ONE; // we always jump here (self-loop, so condition = nu_a = 1)
        padding_row[COL_EXEC_NU_B] = F::from_usize(ending_pc); // nu_b = jump dest = ending_pc
        padding_row[COL_MEM_ADDRESS_A] = F::from_usize(zero_vec_ptr);
        padding_row[COL_MEM_ADDRESS_B] = F::from_usize(zero_vec_ptr);
        padding_row[COL_MEM_ADDRESS_C] = F::from_usize(zero_vec_ptr);
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
