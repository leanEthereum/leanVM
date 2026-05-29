use crate::{execution::memory::MemoryAccess, tables::extension_op::exec::exec_multi_row, *};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_extension_op;

// aux_2 encoding: see `tables/mod.rs`.
pub(crate) const EXT_OP_FLAG_BE: usize = 4;
pub(crate) const EXT_OP_FLAG_ADD: usize = 8;
pub(crate) const EXT_OP_FLAG_DOT_PRODUCT: usize = 16;
pub(crate) const EXT_OP_FLAG_EQ: usize = 32;
pub const EXT_OP_LEN_MULTIPLIER: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum ExtensionOp {
    Add,
    DotProduct,
    Eq,
}

impl ExtensionOp {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "add" => Some(Self::Add),
            "dot_product" => Some(Self::DotProduct),
            "poly_eq" => Some(Self::Eq),
            _ => None,
        }
    }

    pub(crate) const fn flag(self) -> usize {
        match self {
            Self::Add => EXT_OP_FLAG_ADD,
            Self::DotProduct => EXT_OP_FLAG_DOT_PRODUCT,
            Self::Eq => EXT_OP_FLAG_EQ,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct ExtensionOpMode {
    pub op: ExtensionOp,
    pub flag_be: bool,
}

impl ExtensionOpMode {
    pub fn from_name(name: &str) -> Option<Self> {
        let (prefix, suffix) = name.rsplit_once('_')?;
        let flag_be = match suffix {
            "ee" => false,
            "be" => true,
            _ => return None,
        };
        Some(Self {
            op: ExtensionOp::from_name(prefix)?,
            flag_be,
        })
    }

    pub const fn flag_encoding(self) -> usize {
        self.op.flag() + self.flag_be as usize * EXT_OP_FLAG_BE
    }

    pub const fn name(self) -> &'static str {
        match (self.op, self.flag_be) {
            (ExtensionOp::Add, false) => "add_ee",
            (ExtensionOp::Add, true) => "add_be",
            (ExtensionOp::DotProduct, false) => "dot_product_ee",
            (ExtensionOp::DotProduct, true) => "dot_product_be",
            (ExtensionOp::Eq, false) => "poly_eq_ee",
            (ExtensionOp::Eq, true) => "poly_eq_be",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct ExtensionOpPrecompile<const BUS: bool>;

impl<const BUS: bool> TableT for ExtensionOpPrecompile<BUS> {
    fn name(&self) -> &'static str {
        "extension_op"
    }

    fn table(&self) -> Table {
        Table::extension_op()
    }

    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_MULTIPLICITY_EXTENSION_OP),
            domainsep: BusData::Column(COL_DOMAINSEP_EXTENSION_OP),
            data: vec![
                BusData::Column(COL_IDX_A),
                BusData::Column(COL_IDX_B),
                BusData::Column(COL_IDX_RES),
            ],
        }];
        buses.extend(memory_lookups_consecutive(COL_IDX_A, COL_V_A, DIMENSION));
        buses.extend(memory_lookups_consecutive(COL_IDX_B, COL_V_B, DIMENSION));
        buses.extend(memory_lookups_consecutive(COL_IDX_RES, COL_RES, DIMENSION));
        buses
    }

    fn n_columns_total(&self) -> usize {
        self.n_columns() + 2 // +2 for COL_MULTIPLICITY_EXTENSION_OP and COL_DOMAINSEP_EXTENSION_OP (non-AIR, used in bus logup)
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; self.n_columns_total()];
        row[COL_FLAG_START] = F::ONE;
        row[COL_LEN] = F::ONE;
        row[COL_DOMAINSEP_EXTENSION_OP] = F::from_usize(EXT_OP_LEN_MULTIPLIER);
        row[COL_IDX_A] = F::from_usize(zero_vec_ptr);
        row[COL_IDX_B] = F::from_usize(zero_vec_ptr);
        row[COL_IDX_RES] = F::from_usize(zero_vec_ptr);
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::ExtensionOp { size, mode } = args else {
            unreachable!("ExtensionOp table called with non-ExtensionOp args");
        };
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        exec_multi_row(arg_a, arg_b, arg_c, size, mode.flag_be, mode.op, ctx.memory, trace)
    }
}
