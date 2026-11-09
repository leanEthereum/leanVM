//! The instruction tables, their bus flushes, and where every committed column sits in the stack.

use crate::bytecode::Bytecode;
use crate::field::{E, GEN, ONE, ZERO};
use crate::hash::{STATE_LANES, keccak_f};
use crate::keccak::KeccakShape;
use crate::multilinear::{Placement, log2_ceil, log2_strict, stack_offsets};
use crate::{VerifierError, require};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Add;

pub const BUS_BITS: usize = 4; // bus communicates tuples of 2^BUS_BITS field elements

/// A monomial of degree at most 2 in a table's columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Monomial {
    One,
    X(usize),
    /// `x_i * x_j`, `i <= j`.
    Xy(usize, usize),
}

/// A polynomial of degree at most 2 in a table's columns.
#[derive(Clone, Debug, Default)]
pub struct Form {
    terms: Vec<(Monomial, E)>, // each monomial once, with its coefficient, in the order first added
}

impl Form {
    fn term(monomial: Monomial, coefficient: E) -> Self {
        Self {
            terms: vec![(monomial, coefficient)],
        }
    }

    pub fn add_scaled(&mut self, other: &Form, weight: E) {
        for &(monomial, coefficient) in &other.terms {
            match self.terms.iter_mut().find(|(m, _)| *m == monomial) {
                Some((_, c)) => *c += weight * coefficient,
                None => self.terms.push((monomial, weight * coefficient)),
            }
        }
    }

    /// `Σ forms`, the empty sum being the zero polynomial.
    fn sum(forms: impl IntoIterator<Item = Form>) -> Form {
        forms.into_iter().fold(Form::default(), |acc, form| acc + form)
    }

    pub fn evaluate(&self, column: &[E]) -> E {
        E::sum(self.terms.iter().map(|&(monomial, c)| match monomial {
            Monomial::One => c,
            Monomial::X(i) => c * column[i],
            Monomial::Xy(i, j) => c * column[i] * column[j],
        }))
    }
}

impl Add for Form {
    type Output = Form;
    fn add(mut self, other: Form) -> Form {
        self.add_scaled(&other, ONE);
        self
    }
}

/// One block of a bus side, always owned by a table. The three blocks no table owns are the framework, on `BusLayout`.
#[derive(Clone, Debug)]
pub struct BusBlock {
    pub log_rows: usize,        // the owner's height: the block spans 2^log_rows rows
    pub rows: u64,              // ...of which the first `rows` flush, the rest being padding rows, whose leaves are 1
    pub coordinates: Vec<Form>, // the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    pub owner: usize,           // whose block it is, by opcode
}

/// The proof system's version, leading the Fiat-Shamir IV's preimage so that no two versions share a
/// transcript. Its length is fixed and Keccak's padding binds the preimage's, so the bytecode that
/// follows needs no length field of its own. Nothing derives it from the constants below: any change
/// to the constraint system bumps it by hand. Mirrored in `formal/Statement/LeanVmVerifier.lean`.
pub const TAG: &[u8] = b"leanvm-v1";

// The columns no instruction table owns. They come first in the global column numbering, the tables after.
pub const NUM_GLOBAL_COLUMNS: usize = 6;
pub const MEMORY_0: usize = 0;
pub const MEMORY_1: usize = 1;
pub const MEMORY_2: usize = 2;
pub const MEMORY_FINAL_COUNTERS: usize = 3;
pub const BYTECODE_FINAL_COUNTERS: usize = 4;
pub const QKECCAK: usize = 5;

pub const K_BITS: usize = 64;

// The Keccak reduction commits a step's state every KECCAK_DEPTH rounds but the output, a lane per
// slot of q_keccak and a word per step: lane l of the state after KECCAK_DEPTH * m rounds is slot 25 m + l.
pub const KECCAK_DEPTH: usize = 12;
pub const KECCAK_MIN_STEPS_LOG: usize = 9; // the reduction is sized for at least one block of 512 steps

pub const MAX_TABLE_LOG: usize = 32;
pub const MIN_STACKED_LOG: usize = 15;
pub const MAX_STACKED_LOG: usize = 28;

pub struct Layout<'a> {
    pub log_memory: usize,
    pub log_bytecode: usize,
    pub bytecode: &'a Bytecode,
    pub tables: Vec<Table>,
    pub push: Vec<BusBlock>,
    pub pull: Vec<BusBlock>,
    pub count: Vec<BusBlock>,
    /// Where each column sits, `None` for a column nothing commits: the `KECCAK` output lanes.
    pub placements: Vec<Option<Placement>>,
    pub stack_log: usize,
    pub table_log_heights: Vec<usize>,
    pub keccak: KeccakShape,
}

pub fn gpow(index: u64) -> E {
    GEN.pow(index)
}

pub fn constant(value: E) -> Form {
    Form::term(Monomial::One, value)
}

fn col(index: usize, exponent: u64) -> Form {
    Form::term(Monomial::X(index), gpow(exponent))
}

fn prod(a: usize, b: usize, exponent: u64) -> Form {
    Form::term(Monomial::Xy(a.min(b), a.max(b)), gpow(exponent))
}

pub const SEP_STATE: E = ONE;
pub const SEP_MEM: E = GEN;
pub const SEP_BYTECODE: E = E::new(4, 0, 0); // GEN^2

#[derive(Clone, Debug, Default)]
pub struct Flushes {
    push: Vec<Vec<Form>>,
    pull: Vec<Vec<Form>>,
}

impl Flushes {
    fn pair(&mut self, push: Vec<Form>, pull: Vec<Form>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    fn state_derived(&mut self, pc: usize, fp: usize, npc: Form, nfp: Form) {
        self.pair(
            vec![constant(SEP_STATE), npc, nfp],
            vec![constant(SEP_STATE), col(pc, 0), col(fp, 0)],
        );
    }

    fn state_step(&mut self, pc: usize, fp: usize) {
        self.state_derived(pc, fp, col(pc, 1), col(fp, 0));
    }

    /// A pull at `count` and a push at `counter`, the same otherwise.
    fn counted(&mut self, prefix: &[Form; 2], counter: Form, count: usize, suffix: &[Form]) {
        let side = |counter: Form| [&prefix[..], &[counter], suffix].concat();
        self.pair(side(counter), side(col(count, 0)));
    }

    fn bytecode(&mut self, pc: usize, count: usize, opcode: usize, operands: Vec<Form>) {
        let suffix = [vec![constant(gpow(opcode as u64))], operands].concat();
        self.counted(&[constant(SEP_BYTECODE), col(pc, 0)], col(count, 1), count, &suffix);
    }

    fn memory(&mut self, address: Form, count: usize, values: &[Form; 3]) {
        self.counted(&[constant(SEP_MEM), address], col(count, 1), count, values);
    }

    /// `memory` when the column `flag` is 1. The push's counter is `count·(1 + flag·(g + 1))`: `g·count` at 1, and
    /// the pull's `count` at 0, so the pair cancels and touches no cell.
    fn memory_if(&mut self, flag: usize, address: Form, count: usize, values: &[Form; 3]) {
        let counter = col(count, 0) + prod(flag, count, 1) + prod(flag, count, 0);
        self.counted(&[constant(SEP_MEM), address], counter, count, values);
    }

    /// The cell's limbs are the named columns, the missing top ones zero.
    fn memory_cols(&mut self, address: Form, count: usize, columns: &[usize]) {
        let values = core::array::from_fn(|limb| columns.get(limb).map_or(constant(ZERO), |&column| col(column, 0)));
        self.memory(address, count, &values);
    }
}

/// One instruction's table: its bus flushes. Its columns are the constants below, its constraints `constraints`.
pub struct Table {
    pub opcode: usize,   // also its index in the table list, so g^opcode is its bytecode tag
    pub padding: Vec<E>, // the row a padding row holds
    pub flushes: Flushes,
}

/// How many constraints each table has: JUMP's two, and none elsewhere.
const N_CONSTRAINTS: [usize; N_TABLES] = [0, 0, 0, 0, 2, 0];

impl Table {
    pub fn n_constraints(&self) -> usize {
        N_CONSTRAINTS[self.opcode]
    }

    /// Its constraints at a row's `columns`, `n_constraints` of them.
    pub fn constraints(&self, columns: &[E]) -> Vec<E> {
        match self.opcode {
            OP_JUMP => jump_constraints(columns).to_vec(),
            _ => Vec::new(),
        }
    }

    pub fn width(&self) -> usize {
        TABLE_WIDTHS[self.opcode]
    }

    fn count_columns(&self) -> &'static [usize] {
        COUNT_COLUMNS[self.opcode]
    }
}

fn flushes_arith(opcode: usize, multiply: bool) -> Flushes {
    use arith::*;
    let (pc, fp, o_a, o_b, o_c, va, vb) = (PC, FP, O_A, O_B, O_C, VA, VB);
    let (cnt_a, cnt_b, cnt_c, cnt_bc) = (CNT_A, CNT_B, CNT_C, CNT_BC);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o_a, 0), col(o_b, 0), col(o_c, 0), constant(ZERO), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, opcode, operands);
    flushes.memory_cols(prod(fp, o_a, 0), cnt_a, &va);
    flushes.memory_cols(prod(fp, o_b, 0), cnt_b, &vb);
    const TOWER_LANES: [&[(usize, usize)]; 3] = [
        &[(0, 0), (1, 2), (2, 1)],
        &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
        &[(0, 2), (1, 1), (2, 0), (2, 2)],
    ];
    let result = if multiply {
        TOWER_LANES.map(|lane| Form::sum(lane.iter().map(|&(j, k)| prod(va[j], vb[k], 0))))
    } else {
        core::array::from_fn(|i| col(va[i], 0) + col(vb[i], 0))
    };
    flushes.memory(prod(fp, o_c, 0), cnt_c, &result);
    flushes
}

fn flushes_set() -> Flushes {
    use set::*;
    let (pc, fp, o, k, cnt, cnt_bc) = (PC, FP, O, K, CNT, CNT_BC);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o, 0), col(k[0], 0), col(k[1], 0), col(k[2], 0), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, OP_SET, operands);
    flushes.memory_cols(prod(fp, o, 0), cnt, &k);
    flushes
}

fn flushes_deref() -> Flushes {
    use deref::*;
    let (pc, fp, o1, o2, o3, f_pc, f_fp, ptr, v3) = (PC, FP, O1, O2, O3, F_PC, F_FP, PTR, V3);
    let (cnt_ptr, cnt_target, cnt_local, cnt_bc) = (CNT_PTR, CNT_TARGET, CNT_LOCAL, CNT_BC);

    let gated = |lane: usize| [col(lane, 0), prod(f_pc, lane, 0), prod(f_fp, lane, 0)];

    // v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp, lane-wise: only the low lane takes the two K-valued sources.
    let store = [
        Form::sum(gated(v3[0]).into_iter().chain([prod(f_pc, pc, 2), prod(f_fp, fp, 0)])),
        Form::sum(gated(v3[1])),
        Form::sum(gated(v3[2])),
    ];
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o1, 0), col(o2, 0), col(o3, 0), col(f_pc, 0), col(f_fp, 0)];
    flushes.bytecode(pc, cnt_bc, OP_DEREF, operands);
    flushes.memory_cols(prod(fp, o1, 0), cnt_ptr, &[ptr]);
    flushes.memory(prod(ptr, o2, 0), cnt_target, &store);
    flushes.memory_cols(prod(fp, o3, 0), cnt_local, &v3);
    flushes
}

fn flushes_jump() -> Flushes {
    use jump::*;
    let (pc, fp, o_c, o_d, o_f, cond, dest, frame, b) = (PC, FP, O_C, O_D, O_F, V_COND, V_PC, V_FP, B);
    let (cnt_c, cnt_d, cnt_f, cnt_bc) = (CNT_C, CNT_D, CNT_F, CNT_BC);
    let mut flushes = Flushes::default();
    // next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    flushes.state_derived(
        pc,
        fp,
        prod(b, dest, 0) + prod(b, pc, 1) + col(pc, 1),
        prod(b, frame, 0) + prod(b, fp, 0) + col(fp, 0),
    );
    let operands = vec![col(o_c, 0), col(o_d, 0), col(o_f, 0), constant(ZERO), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, OP_JUMP, operands);
    flushes.memory_cols(prod(fp, o_c, 0), cnt_c, &[cond]);
    flushes.memory_cols(prod(fp, o_d, 0), cnt_d, &[dest]);
    flushes.memory_cols(prod(fp, o_f, 0), cnt_f, &[frame]);
    flushes
}

fn jump_constraints(columns: &[E]) -> [E; 2] {
    let [condition, inverse, flag] = [jump::V_COND, jump::W, jump::B].map(|index| columns[index]);
    [flag + condition * inverse, condition * (flag + ONE)]
}

/// The lanes each of a sponge state's thirteen cells holds, `(lo, hi)`, in the even layout or the odd one, `None`
/// marking a limb that holds no lane: nine rate cells, lanes 0..16 two to a cell then lane 16 in a low limb (even), or
/// lane 0 in a high limb then lanes 1..17 two to a cell (odd), then the capacity lanes 17..25.
fn keccak_cell_lanes(odd: bool) -> [(Option<usize>, Option<usize>); KECCAK_CELLS] {
    core::array::from_fn(|cell| match (odd, cell) {
        (_, 9..) | (true, 1..) => (Some(2 * cell - 1), Some(2 * cell)),
        (true, _) => (None, Some(0)),
        (false, 8) => (Some(16), None),
        (false, _) => (Some(2 * cell), Some(2 * cell + 1)),
    })
}

/// A cell limb holding lane `even` in the even layout and `odd` in the odd one, as `flag` selects: `a + flag·(a + b)`,
/// a missing lane being the column `missing`, or zero.
fn layout_limb(even: Option<usize>, odd: Option<usize>, flag: usize, missing: Option<usize>) -> Form {
    let (a, b) = (even.or(missing), odd.or(missing));
    if a == b {
        return a.map_or(constant(ZERO), |a| col(a, 0));
    }
    Form::sum(
        [
            a.map(|a| col(a, 0)),
            a.map(|a| prod(flag, a, 0)),
            b.map(|b| prod(flag, b, 0)),
        ]
        .into_iter()
        .flatten(),
    )
}

fn flushes_keccak() -> Flushes {
    use keccak_head::*;
    let (pc, fp, free, o_m) = (PC, FP, FREE, O_M);
    let (o_tail, o_b8, o_cap, o_out) = (O_TAIL, O_B8, O_CAP, O_OUT);
    let (in_odd, out_odd, out_two, out_all) = (ODD_IN, ODD_OUT, OUT_TWO, OUT_ALL);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = o_m
        .into_iter()
        .chain([o_tail, o_b8, o_cap, o_out, in_odd, out_odd, out_two, out_all]);
    flushes.bytecode(pc, KECCAK_CNT_BC, OP_KECCAK, operands.map(|i| col(i, 0)).collect());
    // The thirteen cells read (four addressed ones, the tail run, b8, the cap run), then the thirteen written, each
    // holding its lanes in the layout its flag names: a read cell's free lane is the column `free`, a written one's zero.
    // Output cell 0 is always written, cell 1 when `out_two` is 1, and cells 2..13 when `out_all` is 1.
    let address = |cell: usize| match cell {
        0..4 => prod(fp, o_m[cell], 0),
        4..8 => prod(fp, o_tail, cell as u64 - 4),
        8 => prod(fp, o_b8, 0),
        _ => prod(fp, o_cap, cell as u64 - 9),
    };
    let (even, odd) = (keccak_cell_lanes(false), keccak_cell_lanes(true));
    for (side, lanes, flag, missing) in [(0, KECCAK_IN, in_odd, Some(free)), (1, KECCAK_OUT, out_odd, None)] {
        let lane = |lane: Option<usize>| lane.map(|lane| lanes + lane);
        for cell in 0..KECCAK_CELLS {
            let limb = |e: Option<usize>, o: Option<usize>| layout_limb(lane(e), lane(o), flag, missing);
            let values = [
                limb(even[cell].0, odd[cell].0),
                limb(even[cell].1, odd[cell].1),
                constant(ZERO),
            ];
            let count = KECCAK_CNT + KECCAK_CELLS * side + cell;
            match (side, cell) {
                (0, _) => flushes.memory(address(cell), count, &values),
                (_, 0) => flushes.memory(prod(fp, o_out, 0), count, &values),
                _ => {
                    let flag = if cell == 1 { out_two } else { out_all };
                    flushes.memory_if(flag, prod(fp, o_out, cell as u64), count, &values);
                }
            }
        }
    }
    flushes
}

pub const OP_XOR: usize = 0;
pub const OP_MUL: usize = 1;
pub const OP_SET: usize = 2;
pub const OP_DEREF: usize = 3;
pub const OP_JUMP: usize = 4;
pub const OP_KECCAK: usize = 5;
pub const N_TABLES: usize = 6;

// Each table's local columns, by index. Its count columns, the ones a bus count reads, are those named `cnt*`.

/// XOR's and MUL's columns.
mod arith {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_A: usize = 2;
    pub const O_B: usize = 3;
    pub const O_C: usize = 4;
    pub const VA: [usize; 3] = [5, 6, 7];
    pub const VB: [usize; 3] = [8, 9, 10];
    pub const CNT_A: usize = 11;
    pub const CNT_B: usize = 12;
    pub const CNT_C: usize = 13;
    pub const CNT_BC: usize = 14;
    pub const WIDTH: usize = 15;
    pub const COUNTS: &[usize] = &[CNT_A, CNT_B, CNT_C, CNT_BC];
}

mod set {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    pub const K: [usize; 3] = [3, 4, 5];
    pub const CNT: usize = 6;
    pub const CNT_BC: usize = 7;
    pub const WIDTH: usize = 8;
    pub const COUNTS: &[usize] = &[CNT, CNT_BC];
}

mod deref {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O1: usize = 2;
    pub const O2: usize = 3;
    pub const O3: usize = 4;
    pub const F_PC: usize = 5;
    pub const F_FP: usize = 6;
    pub const PTR: usize = 7;
    pub const V3: [usize; 3] = [8, 9, 10];
    pub const CNT_PTR: usize = 11;
    pub const CNT_TARGET: usize = 12;
    pub const CNT_LOCAL: usize = 13;
    pub const CNT_BC: usize = 14;
    pub const WIDTH: usize = 15;
    pub const COUNTS: &[usize] = &[CNT_PTR, CNT_TARGET, CNT_LOCAL, CNT_BC];
}

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_C: usize = 2;
    pub const O_D: usize = 3;
    pub const O_F: usize = 4;
    pub const V_COND: usize = 5;
    pub const V_PC: usize = 6;
    pub const V_FP: usize = 7;
    pub const CNT_C: usize = 8;
    pub const CNT_D: usize = 9;
    pub const CNT_F: usize = 10;
    pub const CNT_BC: usize = 11;
    pub const W: usize = 12;
    pub const B: usize = 13;
    pub const WIDTH: usize = 14;
    pub const COUNTS: &[usize] = &[CNT_C, CNT_D, CNT_F, CNT_BC];
}

/// KECCAK's columns: these, then the input lanes `in_l`, the output lanes `out_l`, a read count `cnt_c` for each cell
/// read then each written, and `cnt_bc`. The fifty value lanes are not committed in the table: an input lane is one of
/// q_keccak's slots, and the output lanes' claims are the Keccak reduction's claim on the output.
mod keccak_head {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_M: [usize; 4] = [2, 3, 4, 5];
    pub const O_TAIL: usize = 6;
    pub const O_B8: usize = 7;
    pub const O_CAP: usize = 8;
    pub const O_OUT: usize = 9;
    pub const ODD_IN: usize = 10;
    pub const ODD_OUT: usize = 11;
    pub const OUT_TWO: usize = 12;
    pub const OUT_ALL: usize = 13;
    pub const FREE: usize = 14;
}
const KECCAK_CELLS: usize = 13; // a sponge state, read then written
pub const KECCAK_IN: usize = keccak_head::FREE + 1;
pub const KECCAK_OUT: usize = KECCAK_IN + STATE_LANES;
const KECCAK_CNT: usize = KECCAK_OUT + STATE_LANES;
const KECCAK_CNT_BC: usize = KECCAK_CNT + 2 * KECCAK_CELLS;
/// KECCAK's count columns: each cell's, then `cnt_bc`.
const KECCAK_COUNTS: [usize; 2 * KECCAK_CELLS + 1] = {
    let mut counts = [0; 2 * KECCAK_CELLS + 1];
    let mut i = 0;
    while i < counts.len() {
        counts[i] = KECCAK_CNT + i;
        i += 1;
    }
    counts
};

/// The local KECCAK column riding spare slot `k` (`cpu::keccak_value` in the prover): its
/// committed columns in local order, the ones before the value lanes then the read counts
/// after them.
const fn spare_local(k: usize) -> usize {
    if k < KECCAK_IN { k } else { KECCAK_CNT + (k - KECCAK_IN) }
}

/// Slots of the run the committed states occupy, and the ones they leave over.
const QKECCAK_SLOTS: usize = STATE_LANES * (crate::hash::ROUNDS / KECCAK_DEPTH);
const QKECCAK_SPARE: usize = (1 << log2_ceil(QKECCAK_SLOTS as u64)) - QKECCAK_SLOTS;
// The same guard the prover carries (`cpu::layout`): every spare slot needs a committed column
// of the table to put in it, distinct from the others and not one of the value lanes. It holds
// at this depth, not at every divisor of 24, and the two sides must refuse together.
const _: () = {
    let mut k = 0;
    while k < QKECCAK_SPARE {
        let local = spare_local(k);
        assert!(k == 0 || spare_local(k - 1) < local);
        assert!(local < KECCAK_IN || (local >= KECCAK_CNT && local < TABLE_WIDTHS[OP_KECCAK]));
        k += 1;
    }
};

/// The slot of `q_keccak` the global column `column` IS, if it is one: an input lane (slot =
/// lane), or one of the KECCAK table's own columns riding a slot past the committed states.
/// The reduction weighs nothing on those spare slots, so the stack carries those columns
/// there rather than a block of zeros and a block of its own.
fn qkeccak_slot(column: usize) -> Option<usize> {
    let local = column.checked_sub(GLOBAL_COLUMN_BASES[OP_KECCAK])?;
    if let Some(k) = (0..QKECCAK_SPARE).find(|&k| spare_local(k) == local) {
        return Some(QKECCAK_SLOTS + k);
    }
    (KECCAK_IN..KECCAK_OUT).contains(&local).then(|| local - KECCAK_IN)
}

pub fn tables() -> Vec<Table> {
    let table = |opcode: usize, flushes| Table {
        opcode,
        padding: vec![ZERO; TABLE_WIDTHS[opcode]],
        flushes,
    };
    let mut keccak = table(OP_KECCAK, flushes_keccak());
    // A padding row is zero, but for KECCAK's output lanes: a padding row permutes zeros.
    let mut output = [0; STATE_LANES];
    keccak_f(&mut output);
    for (padding, lane) in keccak.padding[KECCAK_OUT..].iter_mut().zip(output) {
        *padding = E::new(lane, 0, 0);
    }
    vec![
        table(OP_XOR, flushes_arith(OP_XOR, false)),
        table(OP_MUL, flushes_arith(OP_MUL, true)),
        table(OP_SET, flushes_set()),
        table(OP_DEREF, flushes_deref()),
        table(OP_JUMP, flushes_jump()),
        keccak,
    ]
}

const TABLE_WIDTHS: [usize; N_TABLES] = [
    arith::WIDTH,
    arith::WIDTH,
    set::WIDTH,
    deref::WIDTH,
    jump::WIDTH,
    KECCAK_CNT_BC + 1,
];
const COUNT_COLUMNS: [&[usize]; N_TABLES] = [
    arith::COUNTS,
    arith::COUNTS,
    set::COUNTS,
    deref::COUNTS,
    jump::COUNTS,
    &KECCAK_COUNTS,
];
pub const GLOBAL_COLUMN_BASES: [usize; N_TABLES] = {
    let mut bases = [NUM_GLOBAL_COLUMNS; N_TABLES];
    let mut table = 1;
    while table < N_TABLES {
        bases[table] = bases[table - 1] + TABLE_WIDTHS[table - 1];
        table += 1;
    }
    bases
};

/// Each table's least log height: 0, but the Keccak reduction's block of steps for KECCAK.
const TABLE_LOG_FLOORS: [usize; N_TABLES] = [0, 0, 0, 0, 0, KECCAK_MIN_STEPS_LOG];

pub fn build_layout<'a>(
    bytecode: &'a Bytecode,
    log_memory: u64,
    table_rows: &[u64],
) -> Result<Layout<'a>, VerifierError> {
    let log_bytecode = log2_strict(bytecode.len() as u64)?;
    require(
        (16..=32).contains(&log_memory)
            && table_rows.iter().all(|&rows| rows <= 1 << MAX_TABLE_LOG)
            && (BUS_BITS..=32 + BUS_BITS).contains(&log_bytecode),
        VerifierError::AnnouncedTableSizes,
    )?;
    let log_bytecode = log_bytecode - BUS_BITS;
    let log_memory = log_memory as usize;
    // A table's height is the least power of two holding its rows.
    let table_log_heights: Vec<usize> = table_rows
        .iter()
        .zip(TABLE_LOG_FLOORS)
        .map(|(&rows, floor)| log2_ceil(rows).max(floor))
        .collect();

    let tables = tables();
    let mut push = Vec::new();
    let mut pull = Vec::new();
    let mut count = Vec::new();
    for ((table, &height), &rows) in tables.iter().zip(&table_log_heights).zip(table_rows) {
        let block = |coordinates: &Vec<Form>| BusBlock {
            log_rows: height,
            rows,
            coordinates: coordinates.clone(),
            owner: table.opcode,
        };
        push.extend(table.flushes.push.iter().map(block));
        pull.extend(table.flushes.pull.iter().map(block));
        count.extend(table.count_columns().iter().map(|&local| block(&vec![col(local, 0)])));
    }

    // Every column's log size, in global order: the framework's, q_keccak's, then each table's block.
    let keccak = KeccakShape {
        log_steps: table_log_heights[OP_KECCAK],
        depth: KECCAK_DEPTH,
    };
    let qkeccak_kappa = keccak.log_steps + keccak.slot_bits();
    let mut kappas = vec![
        log_memory,
        log_memory,
        log_memory,
        log_memory,
        log_bytecode,
        qkeccak_kappa,
    ];
    for table in &tables {
        kappas.extend(vec![table_log_heights[table.opcode]; table.width()]);
    }

    // A column q_keccak carries gets no block of its own: it is one of its slots, 2^height words,
    // whether an input lane or a KECCAK column riding a spare slot (`qkeccak_slot`). An output
    // lane is not committed at all, nothing ever opening it.
    let base = GLOBAL_COLUMN_BASES[OP_KECCAK];
    let outputs = base + KECCAK_OUT..base + KECCAK_OUT + STATE_LANES;
    let blocks: Vec<usize> = (0..kappas.len())
        .filter(|column| qkeccak_slot(*column).is_none() && !outputs.contains(column))
        .collect();
    let block_kappas: Vec<usize> = blocks.iter().map(|&column| kappas[column]).collect();
    let (block_offsets, total_log) = stack_offsets(&block_kappas);
    let mut offsets = vec![None; kappas.len()];
    for (&column, offset) in blocks.iter().zip(block_offsets) {
        offsets[column] = Some(offset);
    }
    let stack_log = MIN_STACKED_LOG.max(total_log); // Floor at the PCS minimum
    let placement = |(column, &kappa): (usize, &usize)| {
        let index = match qkeccak_slot(column) {
            Some(slot) => offsets[QKECCAK]? + ((slot as u64) << kappa),
            None => offsets[column]?,
        };
        Some(Placement {
            variables: kappa,
            index,
        })
    };
    let placements = kappas.iter().enumerate().map(placement).collect();
    Ok(Layout {
        log_memory,
        log_bytecode,
        bytecode,
        tables,
        push,
        pull,
        count,
        placements,
        stack_log,
        table_log_heights,
        keccak,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constraint_counts_match_the_constraints() {
        for table in tables() {
            assert_eq!(
                table.constraints(&vec![ZERO; table.width()]).len(),
                table.n_constraints()
            );
        }
    }
}
