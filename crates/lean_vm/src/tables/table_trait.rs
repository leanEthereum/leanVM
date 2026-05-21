use crate::execution::memory::MemoryAccess;
use crate::{EF, F, InstructionContext, LOGUP_MEMORY_DOMAINSEP, PrecompileCompTimeArgs, RunnerError, Table};
use backend::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::VarCount;

pub type ColIndex = usize;

/// Each entry: (point, eval, eval at 'shifted-down' column).
pub type CommittedStatements =
    BTreeMap<Table, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>)>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusDirection {
    Pull,
    Push,
}

impl BusDirection {
    pub fn to_field_flag(self) -> F {
        match self {
            BusDirection::Pull => F::NEG_ONE,
            BusDirection::Push => F::ONE,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusData {
    Column(ColIndex),
    ColumnPlusConstant(ColIndex, usize),
    Constant(usize),
}

impl BusData {
    pub fn column(self) -> Option<ColIndex> {
        match self {
            Self::Column(c) | Self::ColumnPlusConstant(c, _) => Some(c),
            Self::Constant(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusMultiplicity {
    One,
    Column(ColIndex),
}

#[derive(Debug)]
pub struct BusInteraction {
    pub direction: BusDirection,
    pub multiplicity: BusMultiplicity,
    pub domainsep: BusData,
    pub data: Vec<BusData>,
}

impl BusInteraction {
    pub fn is_memory_lookup(&self) -> bool {
        matches!(self.domainsep, BusData::Constant(LOGUP_MEMORY_DOMAINSEP))
    }
}

pub fn memory_lookups_consecutive(idx_col: ColIndex, values_start: ColIndex, n: usize) -> Vec<BusInteraction> {
    (0..n)
        .map(|i| BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::One,
            domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
            data: vec![
                BusData::ColumnPlusConstant(idx_col, i),
                BusData::Column(values_start + i),
            ],
        })
        .collect()
}

pub fn memory_lookup_groups(buses: &[BusInteraction]) -> Vec<MemoryLookupGroup> {
    let mut groups: Vec<MemoryLookupGroup> = Vec::new();
    let mut i = 0;
    while i < buses.len() {
        if !buses[i].is_memory_lookup() {
            i += 1;
            continue;
        }
        let (idx_col, first_ofs) = match buses[i].data[0] {
            BusData::ColumnPlusConstant(c, ofs) => (c, ofs),
            _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
        };
        if first_ofs != 0 {
            let value_col = match buses[i].data[1] {
                BusData::Column(c) => c,
                _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
            };
            groups.push(MemoryLookupGroup {
                start_bus: i,
                idx_col,
                value_cols: vec![value_col],
            });
            i += 1;
            continue;
        }
        let mut value_cols = Vec::new();
        let start = i;
        let mut expected_ofs = 0;
        while i < buses.len() && buses[i].is_memory_lookup() {
            let ok = matches!(
                buses[i].data[0],
                BusData::ColumnPlusConstant(c, ofs) if c == idx_col && ofs == expected_ofs
            );
            if !ok {
                break;
            }
            let value_col = match buses[i].data[1] {
                BusData::Column(c) => c,
                _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
            };
            value_cols.push(value_col);
            i += 1;
            expected_ofs += 1;
        }
        groups.push(MemoryLookupGroup {
            start_bus: start,
            idx_col,
            value_cols,
        });
    }
    groups
}

#[derive(Debug)]
pub struct MemoryLookupGroup {
    pub start_bus: usize,
    pub idx_col: ColIndex,
    pub value_cols: Vec<ColIndex>,
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub columns: Vec<Vec<F>>,
    pub non_padded_n_rows: usize,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            columns: vec![Vec::new(); air.n_columns_total()],
            non_padded_n_rows: 0, // filled later
            log_n_rows: 0,        // filled later
        }
    }
}

pub fn sort_tables_by_height(tables_log_heights: &BTreeMap<Table, usize>) -> Vec<(Table, usize)> {
    let mut tables_heights_sorted = tables_log_heights.clone().into_iter().collect::<Vec<_>>();
    tables_heights_sorted.sort_by_key(|&(_, h)| Reverse(h));
    tables_heights_sorted
}

#[derive(Debug, Default)]
pub struct ExtraDataForBuses<EF: ExtensionField<PF<EF>>> {
    // GKR quotient challenges
    pub logup_alphas_eq_poly: Vec<EF>,
    pub logup_alphas_eq_poly_packed: Vec<EFPacking<EF>>,
    pub alpha_powers: Vec<EF>,
}
impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn new(logup_alphas_eq_poly: Vec<EF>, alpha_powers: Vec<EF>) -> Self {
        let logup_alphas_eq_poly_packed = logup_alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
        Self {
            logup_alphas_eq_poly,
            logup_alphas_eq_poly_packed,
            alpha_powers,
        }
    }
}

impl AlphaPowersMut<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        &mut self.alpha_powers
    }
}

impl AlphaPowers<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers(&self) -> &[EF] {
        &self.alpha_powers
    }
}

impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn transmute_bus_data<NewEF: 'static>(&self) -> &Vec<NewEF> {
        if TypeId::of::<NewEF>() == TypeId::of::<EF>() {
            unsafe { transmute::<&Vec<EF>, &Vec<NewEF>>(&self.logup_alphas_eq_poly) }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe { transmute::<&Vec<EFPacking<EF>>, &Vec<NewEF>>(&self.logup_alphas_eq_poly_packed) }
        }
    }
}

/// Convention: The "AIR" columns are at the start (both for base and extension columns).
/// (Some columns may not appear in the AIR)
pub trait TableT: Air {
    fn name(&self) -> &'static str;
    fn table(&self) -> Table;
    fn bus_interactions(&self) -> Vec<BusInteraction>;
    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize, ending_pc: usize) -> Vec<F>;
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError>;

    // number of columns committed + potentially some virtual columns (useful to keep in memory for logup)
    fn n_columns_total(&self) -> usize {
        self.n_columns()
    }

    fn is_execution_table(&self) -> bool {
        false
    }
}
