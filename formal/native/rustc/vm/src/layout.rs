//! Phase 1: the announced sizes and the layout (`NativeVm/Model/Layout.lean`), with the forms, the
//! instruction tables as data (`data.rs`, generated from `tablesW`), the placements and
//! `stackOffsets`.

use crate::data::{FORMS, GLOBAL_COLUMN_BASES, KECCAK_OUTPUT, KECCAK_SLOT, PADDING, TABLES, TERMS, TUPLES};
use crate::field::{EW, ONE, ZERO, eq_eval_fn, selector_point, shr};
use crate::transcript::{TState, require};

/// A run of a constant array: its first index and length.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

/// `TermW`: a monomial of `degree ≤ 2` columns (`cols[..degree]`, sorted) and its coefficient.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct TermW {
    pub degree: usize,
    pub cols: [usize; 2],
    pub coeff: EW,
}

impl TermW {
    #[inline(always)]
    fn cols(&self) -> &[usize] {
        self.cols.get(..self.degree).unwrap_or(&[])
    }
}

/// `TableW`: an instruction's table as data, its padding row a run of `PADDING`; its tuples are
/// the bus blocks' (`PUSH_BLOCKS`, `PULL_BLOCKS`, `COUNT_BLOCKS`, `busBlocks`).
#[derive(Clone, Copy)]
#[repr(C)]
pub struct TableW {
    pub opcode: usize,
    pub width: usize,
    pub n_constraints: usize,
    pub padding: Span,
}

impl TableW {
    /// `padding`.
    #[inline(always)]
    pub fn padding(&self) -> &'static [EW] {
        PADDING.get(self.padding.start..self.padding.start + self.padding.len).unwrap_or(&[])
    }
}

/// A bus block's fixed part (`BusBlockW` but its `logRows` and `rows`, which are its owner's):
/// its owner and the tuple it flushes, an index of `TUPLES`.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Block {
    pub owner: usize,
    pub tuple: usize,
}

/// `keccakSlotTable`'s `none`.
pub const NO_SLOT: u8 = 255;
/// `nTables`.
pub const N_TABLES: usize = 6;
/// `columnCount`.
pub const COLUMN_COUNT: usize = 158;
/// `busBits`.
pub const BUS_BITS: usize = 4;
/// `opJump`, `opKeccak`.
pub const OP_JUMP: usize = 4;
pub const OP_KECCAK: usize = 5;
/// `qkeccak`, `memory0`, `memory1`, `memoryFinalCounters`, `bytecodeFinalCounters`.
pub const QKECCAK: usize = 4;
pub const MEMORY_0: usize = 0;
pub const MEMORY_1: usize = 1;
pub const MEMORY_FINAL_COUNTERS: usize = 2;
pub const BYTECODE_FINAL_COUNTERS: usize = 3;
/// `qkeccakSlotBits`.
pub const QKECCAK_SLOT_BITS: usize = 6;
/// `tableLogFloors`.
pub const TABLE_LOG_FLOORS: [usize; N_TABLES] = [0, 0, 0, 0, 0, 9];
/// `Whir.minLogStack`, `Whir.maxLogStack`.
pub const MIN_LOG_STACK: usize = 16;
pub const MAX_LOG_STACK: usize = 30;
/// `formCap`: the most terms of a bus form.
pub const FORM_CAP: usize = 148;

/// A form of `data.rs` (`FormW`), by its index in `FORMS`.
#[inline(never)]
pub fn form_terms(form: usize) -> &'static [TermW] {
    match FORMS.get(form) {
        Some(span) => TERMS.get(span.start..span.start + span.len).unwrap_or(&[]),
        None => &[],
    }
}

/// A tuple's forms, as a run of `FORMS`.
#[inline(always)]
pub fn tuple_forms(tuple: usize) -> core::ops::Range<usize> {
    match TUPLES.get(tuple) {
        Some(span) => span.start..span.start + span.len,
        None => 0..0,
    }
}

/// `FormW.evaluate`: `Σ c · Π column(i)` on a row, a missing column `0`.
#[inline(never)]
pub fn evaluate(terms: &[TermW], row: &[EW]) -> EW {
    terms.iter().fold(ZERO, |sum, t| {
        sum + t.cols().iter().fold(t.coeff, |acc, &i| acc * row.get(i).copied().unwrap_or(ZERO))
    })
}

/// A form of at most `FORM_CAP` terms, in insertion order.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct FormBuf {
    pub len: usize,
    pub terms: [TermW; FORM_CAP],
}

impl FormBuf {
    #[inline(always)]
    pub fn terms(&self) -> &[TermW] {
        self.terms.get(..self.len).unwrap_or(&[])
    }

    /// The empty form.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// `FormW.const value`.
    #[inline(always)]
    pub fn set_const(&mut self, value: EW) {
        self.terms[0] = TermW { degree: 0, cols: [0, 0], coeff: value };
        self.len = 1;
    }

    /// `addTerm`: add `c` into the coefficient of `t`'s monomial, appending it if it is new.
    #[inline(never)]
    fn add_term(&mut self, t: &TermW, c: EW) -> Option<()> {
        let n = self.len;
        let terms = self.terms.get_mut(..n)?;
        match terms.iter_mut().find(|u| u.degree == t.degree && u.cols().iter().zip(t.cols()).all(|(a, b)| a == b)) {
            Some(u) => u.coeff = u.coeff + c,
            None => {
                let slot = self.terms.get_mut(n)?;
                *slot = TermW { degree: t.degree, cols: t.cols, coeff: ZERO + c };
                self.len = n + 1;
            }
        }
        Some(())
    }

    /// `FormW.addScaled`: add `weight · other`.
    #[inline(never)]
    pub fn add_scaled(&mut self, other: &[TermW], weight: EW) -> Option<()> {
        for t in other {
            self.add_term(t, weight * t.coeff)?;
        }
        Some(())
    }
}

/// `constraintsW`: a table's constraints on a row, `jumpConstraints` for `JUMP`; their count.
#[inline(never)]
pub fn constraints_w(opcode: usize, row: &[EW], out: &mut [EW; 2]) -> usize {
    if opcode == OP_JUMP {
        let at = |i: usize| row.get(i).copied().unwrap_or(ZERO);
        let (condition, inverse, flag) = (at(5), at(12), at(13));
        out[0] = flag + condition * inverse;
        out[1] = condition * (flag + ONE);
        2
    } else {
        0
    }
}

/// `keccakSlotTable[c]`.
#[inline(always)]
fn slot_of(c: usize) -> Option<usize> {
    match KECCAK_SLOT.get(c) {
        Some(&s) if s != NO_SLOT => Some(s as usize),
        _ => None,
    }
}

/// `keccakOutputTable[c]`.
#[inline(always)]
fn is_output(c: usize) -> bool {
    KECCAK_OUTPUT.get(c).copied().unwrap_or(false)
}

/// `Placement`: the coordinates a point fills, and the selector of the rest.
#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct Placement {
    pub variable_count: usize,
    pub index: u64,
}

/// `Option Placement` in memory: `present` `0` for none.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct PlacementAt {
    pub present: u64,
    pub placement: Placement,
}

impl PlacementAt {
    #[inline(always)]
    pub fn get(&self) -> Option<Placement> {
        if self.present != 0 { Some(self.placement) } else { None }
    }
}

/// `stackPoint`: `point ++ selectorPoint (index >>> variableCount) (stackLog - variableCount)` into
/// `out`; its length.
#[inline(never)]
pub fn stack_point(p: Placement, point: &[EW], stack_log: usize, out: &mut [EW]) -> Option<usize> {
    let tail = stack_log.saturating_sub(p.variable_count);
    let n = point.len().checked_add(tail)?;
    let (head, rest) = out.get_mut(..n)?.split_at_mut_checked(point.len())?;
    for (slot, &x) in head.iter_mut().zip(point) {
        *slot = x;
    }
    selector_point(shr(p.index, p.variable_count), rest);
    Some(n)
}

/// `eqAbove`: `eqEval (selectorPoint (index >>> vc) (|point| - vc)) (point.extract vc |point|)`.
#[inline(always)]
pub fn eq_above(p: Placement, point: &[EW]) -> EW {
    let above = point.get(p.variable_count..).unwrap_or(&[]);
    let selector = shr(p.index, p.variable_count);
    eq_eval_fn(above.len(), |k| crate::field::bit_e(selector, k), above)
}

/// `insertionSort` (`swapDown` for each element in turn) of `order` by `lt`.
#[inline(never)]
fn insertion_sort(order: &mut [usize], lt: impl Fn(usize, usize) -> bool) {
    for i in 0..order.len() {
        // `swapDown lt acc i`.
        let mut j = i;
        while j > 0 {
            let (a, b) = match (order.get(j), order.get(j - 1)) {
                (Some(&a), Some(&b)) => (a, b),
                _ => break,
            };
            if !lt(a, b) {
                break;
            }
            order.swap(j, j - 1);
            j -= 1;
        }
    }
}

/// `log2Ceil`: the bit length of `value - 1`.
#[inline(always)]
pub fn log2_ceil(value: u64) -> usize {
    crate::field::bit_length(value.saturating_sub(1))
}

/// The most sizes `stackOffsets` takes: a bus side's three framework blocks and its blocks, or the
/// committed columns.
pub const MAX_SIZES: usize = COLUMN_COUNT;

/// `stackOffsets`: blocks of `2^size` end to end, largest first, ties by index; the offsets into
/// `offsets`, and the log-size of the total.
#[inline(never)]
pub fn stack_offsets(sizes: &[usize], offsets: &mut [u64]) -> Option<usize> {
    let n = sizes.len();
    require(n <= MAX_SIZES && offsets.len() >= n)?;
    let size = |i: usize| sizes.get(i).copied().unwrap_or(0);
    let mut order = [0usize; MAX_SIZES];
    let order = order.get_mut(..n)?;
    for (i, slot) in order.iter_mut().enumerate() {
        *slot = i;
    }
    insertion_sort(order, |i, j| size(j) < size(i) || (size(i) == size(j) && i < j));
    let mut acc = 0u64;
    for &i in order.iter() {
        *offsets.get_mut(i)? = acc;
        acc = acc.checked_add(1u64.checked_shl(u32::try_from(size(i)).ok()?)?)?;
    }
    Some(log2_ceil(acc))
}

/// `LayoutW`, its bus blocks kept as the tables' heights and rows they are built from
/// (`busBlocks`, `LayoutAt`).
#[repr(C)]
pub struct LayoutW {
    pub log_memory: usize,
    pub log_bytecode: usize,
    pub stack_log: usize,
    pub table_log_heights: [usize; N_TABLES],
    pub rows: [u64; N_TABLES],
    pub placements: [PlacementAt; COLUMN_COUNT],
}

impl LayoutW {
    /// `LayoutW.placement`.
    #[inline(never)]
    pub fn placement(&self, column: usize) -> Placement {
        self.placements.get(column).and_then(PlacementAt::get).unwrap_or_default()
    }

    /// A bus block's `logRows` and `rows`, its owner's (`busBlocks`).
    #[inline(always)]
    pub fn block_rows(&self, owner: usize) -> (usize, u64) {
        (
            self.table_log_heights.get(owner).copied().unwrap_or(0),
            self.rows.get(owner).copied().unwrap_or(0),
        )
    }
}

/// `columnKappas`: every column's log-size.
#[inline(never)]
fn column_kappas(log_memory: usize, log_bytecode: usize, heights: &[usize; N_TABLES]) -> [usize; COLUMN_COUNT] {
    let mut kappas = [0; COLUMN_COUNT];
    let head = [log_memory, log_memory, log_memory, log_bytecode, heights[OP_KECCAK] + QKECCAK_SLOT_BITS];
    for (slot, k) in kappas.iter_mut().zip(head) {
        *slot = k;
    }
    let mut c = head.len();
    for table in &TABLES {
        let h = heights.get(table.opcode).copied().unwrap_or(0);
        for _ in 0..table.width {
            if let Some(slot) = kappas.get_mut(c) {
                *slot = h;
            }
            c += 1;
        }
    }
    kappas
}

/// `placementsOf`: the committed columns stacked, a column with a `q_keccak` slot inside
/// `q_keccak`'s block, an output lane nowhere; and the stack's log-size.
#[inline(never)]
fn placements_of(kappas: &[usize; COLUMN_COUNT], placements: &mut [PlacementAt; COLUMN_COUNT]) -> Option<usize> {
    let mut block_cols = [0usize; COLUMN_COUNT];
    let mut block_sizes = [0usize; COLUMN_COUNT];
    let mut n = 0;
    for (c, &kappa) in kappas.iter().enumerate() {
        if slot_of(c).is_none() && !is_output(c) {
            *block_cols.get_mut(n)? = c;
            *block_sizes.get_mut(n)? = kappa;
            n += 1;
        }
    }
    let mut block_offsets = [0u64; COLUMN_COUNT];
    let total_log = stack_offsets(block_sizes.get(..n)?, &mut block_offsets)?;
    let mut offsets = [0u64; COLUMN_COUNT];
    for (&c, &o) in block_cols.get(..n)?.iter().zip(&block_offsets) {
        *offsets.get_mut(c)? = o;
    }
    for (column, (slot, &kappa)) in placements.iter_mut().zip(kappas).enumerate() {
        *slot = match slot_of(column) {
            Some(s) => {
                let index = offsets[QKECCAK].checked_add((s as u64).checked_shl(u32::try_from(kappa).ok()?)?)?;
                PlacementAt { present: 1, placement: Placement { variable_count: kappa, index } }
            }
            None if is_output(column) => PlacementAt { present: 0, placement: Placement::default() },
            None => PlacementAt { present: 1, placement: Placement { variable_count: kappa, index: offsets[column] } },
        };
    }
    Some(MIN_LOG_STACK.max(total_log))
}

/// `log2Strict`.
#[inline(always)]
fn log2_strict(value: u64) -> Option<usize> {
    if value > 0 && value & (value - 1) == 0 { Some(crate::field::bit_length(value) - 1) } else { None }
}

/// `buildLayout bytecode logMemory tableRows` into `layout`; `None` where the Rust errs.
#[inline(never)]
fn build_layout(bytecode_len: u64, log_memory: u64, table_rows: &[u64; N_TABLES], layout: &mut LayoutW) -> Option<()> {
    let log_length = log2_strict(bytecode_len)?;
    require(
        BUS_BITS <= log_length
            && (1..=30).contains(&log_memory)
            && table_rows.iter().all(|&rows| rows <= 1 << 30)
            && log_length - BUS_BITS <= 30,
    )?;
    layout.log_memory = log_memory as usize;
    layout.log_bytecode = log_length - BUS_BITS;
    for t in 0..N_TABLES {
        layout.table_log_heights[t] = log2_ceil(table_rows[t]).max(TABLE_LOG_FLOORS[t]);
        layout.rows[t] = table_rows[t];
    }
    let kappas = column_kappas(layout.log_memory, layout.log_bytecode, &layout.table_log_heights);
    layout.stack_log = placements_of(&kappas, &mut layout.placements)?;
    Some(())
}

/// **Phase 1** (`readAnnouncedSizes`): the memory log-size, the tables' row counts and the WHIR
/// rate exponent, checked; the layout into `layout`, and the rate exponent.
#[inline(never)]
pub fn read_announced_sizes(t: &mut TState, bytecode_len: u64, layout: &mut LayoutW) -> Option<usize> {
    let mut announced = [ZERO; 2 + N_TABLES];
    t.read_scalars(&mut announced)?;
    require(announced.iter().all(|a| a.c1 == 0))?;
    let log_memory = announced[0].c0;
    let table_rows: [u64; N_TABLES] = core::array::from_fn(|i| announced[1 + i].c0);
    let log_inverse_rate = announced[1 + N_TABLES].c0;
    require((1..=4).contains(&log_inverse_rate))?;
    build_layout(bytecode_len, log_memory, &table_rows, layout)?;
    require((MIN_LOG_STACK..=MAX_LOG_STACK).contains(&layout.stack_log))?;
    Some(log_inverse_rate as usize)
}

/// `globalColumnBasesW[t]`.
#[inline(always)]
pub fn global_column_base(t: usize) -> usize {
    GLOBAL_COLUMN_BASES.get(t).copied().unwrap_or(0)
}
