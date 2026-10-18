//! The instruction tables, their bus flushes, and where every committed column sits in the stack.

use crate::bytecode::Bytecode;
use crate::field::{E, GEN, ONE, ZERO};
use crate::hash::{STATE_LANES, step};
use crate::multilinear::{Placement, log2_ceil, log2_strict, stack_offsets};
use crate::{VerifierError, require};
use std::collections::BTreeMap;
use std::ops::Add;

pub const BUS_BITS: usize = 4; // bus communicates tuples of 2^BUS_BITS field elements

/// A polynomial of degree at most 2 in a table's columns.
#[derive(Clone, Debug, Default)]
pub struct Form {
    terms: BTreeMap<Vec<usize>, E>, // monomial -> coefficient; [] is 1, [i] is x_i, [i, j] is x_i*x_j
}

impl Form {
    fn term(monomial: Vec<usize>, coefficient: E) -> Self {
        Self {
            terms: BTreeMap::from([(monomial, coefficient)]),
        }
    }

    pub fn add_scaled(&mut self, other: &Form, weight: E) {
        for (monomial, &coefficient) in &other.terms {
            *self.terms.entry(monomial.clone()).or_default() += weight * coefficient;
        }
    }

    /// `Σ forms`, the empty sum being the zero polynomial.
    fn sum(forms: impl IntoIterator<Item = Form>) -> Form {
        forms.into_iter().fold(Form::default(), |acc, form| acc + form)
    }

    pub fn evaluate(&self, column: &[E]) -> E {
        E::sum(
            self.terms
                .iter()
                .map(|(monomial, &c)| monomial.iter().fold(c, |acc, &index| acc * column[index])),
        )
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

pub const RELATION_LABEL: &[u8] =
    b"leanVM keccak GKR: step, depth 12, packs of 16 in degree 23, lane slots, output claimed by the bus";

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
pub const QKECCAK_SLOT_BITS: usize = 6; // log2_ceil(25 * segments), two segments of 12 rounds
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
    /// Where each column sits, `None` for a column nothing commits: the `SHA3` output lanes.
    pub placements: Vec<Option<Placement>>,
    pub stack_log: usize,
    pub placed: u64, // the words the columns fill, from the bottom of the stack
    pub table_log_heights: Vec<usize>,
}

fn cols<const N: usize>(columns: &[&str], names: [&str; N]) -> [usize; N] {
    names.map(|name| {
        columns
            .iter()
            .position(|&column| column == name)
            .expect("unknown column")
    })
}

pub fn gpow(index: u64) -> E {
    GEN.pow(index)
}

pub fn constant(value: E) -> Form {
    Form::term(vec![], value)
}

fn col(index: usize, exponent: u64) -> Form {
    Form::term(vec![index], gpow(exponent))
}

fn prod(a: usize, b: usize, exponent: u64) -> Form {
    Form::term(vec![a.min(b), a.max(b)], gpow(exponent))
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

    fn counted(&mut self, prefix: [Form; 2], count: usize, suffix: Vec<Form>) {
        let side = |counter: Form| [prefix.to_vec(), vec![counter], suffix.clone()].concat();
        self.pair(side(col(count, 1)), side(col(count, 0)));
    }

    fn bytecode(&mut self, pc: usize, count: usize, opcode: usize, operands: Vec<Form>) {
        let suffix = [vec![constant(gpow(opcode as u64))], operands].concat();
        self.counted([constant(SEP_BYTECODE), col(pc, 0)], count, suffix);
    }

    fn memory(&mut self, address: Form, count: usize, values: [Form; 3]) {
        self.counted([constant(SEP_MEM), address], count, values.to_vec());
    }

    /// The cell's limbs are the named columns, the missing top ones zero.
    fn memory_cols(&mut self, address: Form, count: usize, columns: &[usize]) {
        let values = std::array::from_fn(|limb| columns.get(limb).map_or(constant(ZERO), |&column| col(column, 0)));
        self.memory(address, count, values);
    }
}

/// One instruction's table: its columns, its bus flushes, its constraints.
pub struct Table {
    pub opcode: usize, // also its index in the table list, so g^opcode is its bytecode tag
    pub columns: &'static [&'static str],
    pub padding: Vec<E>, // the row a padding row holds
    pub flushes: Flushes,
    pub constraints: fn(&[E]) -> Vec<E>,
}

impl Table {
    pub fn n_constraints(&self) -> usize {
        (self.constraints)(&vec![ZERO; self.width()]).len()
    }

    pub fn width(&self) -> usize {
        self.columns.len()
    }

    fn count_columns(&self) -> impl Iterator<Item = usize> {
        (0..self.width()).filter(|&i| self.columns[i].starts_with("cnt"))
    }
}

fn flushes_arith(opcode: usize, multiply: bool) -> Flushes {
    let [pc, fp, o_a, o_b, o_c, cnt_a, cnt_b, cnt_c, cnt_bc] = cols(
        ARITH_COLUMNS,
        ["pc", "fp", "o_a", "o_b", "o_c", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"],
    );
    let va = cols(ARITH_COLUMNS, ["va_0", "va_1", "va_2"]);
    let vb = cols(ARITH_COLUMNS, ["vb_0", "vb_1", "vb_2"]);
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
        std::array::from_fn(|i| col(va[i], 0) + col(vb[i], 0))
    };
    flushes.memory(prod(fp, o_c, 0), cnt_c, result);
    flushes
}

fn flushes_set() -> Flushes {
    let [pc, fp, o, cnt, cnt_bc] = cols(SET_COLUMNS, ["pc", "fp", "o", "cnt", "cnt_bc"]);
    let k = cols(SET_COLUMNS, ["k_0", "k_1", "k_2"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o, 0), col(k[0], 0), col(k[1], 0), col(k[2], 0), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, OP_SET, operands);
    flushes.memory_cols(prod(fp, o, 0), cnt, &k);
    flushes
}

fn flushes_deref() -> Flushes {
    let [pc, fp, o1, o2, o3, f_pc, f_fp, ptr] =
        cols(DEREF_COLUMNS, ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr"]);
    let [cnt_ptr, cnt_target, cnt_local, cnt_bc] =
        cols(DEREF_COLUMNS, ["cnt_ptr", "cnt_target", "cnt_local", "cnt_bc"]);
    let v3 = cols(DEREF_COLUMNS, ["v3_0", "v3_1", "v3_2"]);

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
    flushes.memory(prod(ptr, o2, 0), cnt_target, store);
    flushes.memory_cols(prod(fp, o3, 0), cnt_local, &v3);
    flushes
}

fn flushes_jump() -> Flushes {
    let [pc, fp, o_c, o_d, o_f, cond, dest, frame, b] = cols(
        JUMP_COLUMNS,
        ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "b"],
    );
    let [cnt_c, cnt_d, cnt_f, cnt_bc] = cols(JUMP_COLUMNS, ["cnt_c", "cnt_d", "cnt_f", "cnt_bc"]);
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

fn jump_constraints(columns: &[E]) -> Vec<E> {
    let [condition, inverse, flag] = cols(JUMP_COLUMNS, ["v_cond", "w", "b"]).map(|index| columns[index]);
    vec![flag + condition * inverse, condition * (flag + ONE)]
}

/// The lanes each of a sponge state's thirteen cells holds: lanes 0..16 two to a cell, then lane 16 alone (its high
/// lane a literal zero), then the capacity lanes 17..25.
const SHA3_CELL_LANES: [&[usize]; 13] = [
    &[0, 1],
    &[2, 3],
    &[4, 5],
    &[6, 7],
    &[8, 9],
    &[10, 11],
    &[12, 13],
    &[14, 15],
    &[16],
    &[17, 18],
    &[19, 20],
    &[21, 22],
    &[23, 24],
];

fn flushes_sha3() -> Flushes {
    let [pc, fp, cnt_bc] = cols(SHA3_COLUMNS, ["pc", "fp", "cnt_bc"]);
    let o_m = cols(SHA3_COLUMNS, ["o_m0", "o_m1", "o_m2", "o_m3"]);
    let [o_tail, o_cap, o_out] = cols(SHA3_COLUMNS, ["o_tail", "o_cap", "o_out"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = [o_m[0], o_m[1], o_m[2], o_m[3], o_tail, o_cap, o_out];
    flushes.bytecode(pc, cnt_bc, OP_SHA3, operands.map(|i| col(i, 0)).to_vec());
    // The thirteen cells read (four addressed ones, then the consecutive tail and cap runs), then the thirteen
    // written. Each carries its q_keccak lanes and zeros above them.
    let read = |cell: usize| match cell {
        0..4 => prod(fp, o_m[cell], 0),
        4..8 => prod(fp, o_tail, cell as u64 - 4),
        _ => prod(fp, o_cap, cell as u64 - 8),
    };
    for (side, prefix) in ["in", "out"].into_iter().enumerate() {
        for (cell, lanes) in SHA3_CELL_LANES.iter().enumerate() {
            let address = if side == 0 {
                read(cell)
            } else {
                prod(fp, o_out, cell as u64)
            };
            let count = cols(SHA3_COLUMNS, [&format!("cnt_{}", 13 * side + cell)])[0];
            let limbs: Vec<usize> = lanes
                .iter()
                .map(|lane| cols(SHA3_COLUMNS, [&format!("{prefix}_{lane}")])[0])
                .collect();
            flushes.memory_cols(address, count, &limbs);
        }
    }
    flushes
}

pub const OP_XOR: usize = 0;
pub const OP_MUL: usize = 1;
pub const OP_SET: usize = 2;
pub const OP_DEREF: usize = 3;
pub const OP_JUMP: usize = 4;
pub const OP_SHA3: usize = 5;
pub const N_TABLES: usize = 6;

#[rustfmt::skip]
const ARITH_COLUMNS: &[&str] = &["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"];
const SET_COLUMNS: &[&str] = &["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"];
#[rustfmt::skip]
const DEREF_COLUMNS: &[&str] = &["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc"];
#[rustfmt::skip]
const JUMP_COLUMNS: &[&str] = &["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b"];
#[rustfmt::skip]
const SHA3_COLUMNS: &[&str] = &[
    "pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_cap", "o_out",
    // These fifty value lanes are not committed here: an input lane is one of q_keccak's slots,
    // and the output lanes' claims are the Keccak reduction's claim on the output.
    "in_0", "in_1", "in_2", "in_3", "in_4", "in_5", "in_6", "in_7", "in_8", "in_9", "in_10", "in_11", "in_12", "in_13", "in_14", "in_15", "in_16", "in_17", "in_18", "in_19", "in_20", "in_21", "in_22", "in_23", "in_24",
    "out_0", "out_1", "out_2", "out_3", "out_4", "out_5", "out_6", "out_7", "out_8", "out_9", "out_10", "out_11", "out_12", "out_13", "out_14", "out_15", "out_16", "out_17", "out_18", "out_19", "out_20", "out_21", "out_22", "out_23", "out_24",
    // ...and the read counts, committed here like every other column.
    "cnt_0", "cnt_1", "cnt_2", "cnt_3", "cnt_4", "cnt_5", "cnt_6", "cnt_7", "cnt_8", "cnt_9", "cnt_10", "cnt_11", "cnt_12", "cnt_13", "cnt_14", "cnt_15", "cnt_16", "cnt_17", "cnt_18", "cnt_19", "cnt_20", "cnt_21", "cnt_22", "cnt_23", "cnt_24", "cnt_25", "cnt_bc",
];

pub fn tables() -> Vec<Table> {
    // A padding row is zero, but for SHA3's output lanes: a padding step reads zeros, so it writes their step.
    let output = step(&[0; STATE_LANES]);
    let table = |opcode, columns: &'static [&'static str], flushes, constraints| Table {
        opcode,
        columns,
        padding: columns
            .iter()
            .map(|&name| {
                let lane = name.strip_prefix("out_").filter(|_| opcode == OP_SHA3);
                E::new(lane.map_or(0, |lane| output[lane.parse::<usize>().unwrap()]), 0, 0)
            })
            .collect(),
        flushes,
        constraints,
    };
    vec![
        table(OP_XOR, ARITH_COLUMNS, flushes_arith(OP_XOR, false), |_| vec![]),
        table(OP_MUL, ARITH_COLUMNS, flushes_arith(OP_MUL, true), |_| vec![]),
        table(OP_SET, SET_COLUMNS, flushes_set(), |_| vec![]),
        table(OP_DEREF, DEREF_COLUMNS, flushes_deref(), |_| vec![]),
        table(OP_JUMP, JUMP_COLUMNS, flushes_jump(), jump_constraints),
        table(OP_SHA3, SHA3_COLUMNS, flushes_sha3(), |_| vec![]),
    ]
}

const TABLE_WIDTHS: [usize; N_TABLES] = [
    ARITH_COLUMNS.len(),
    ARITH_COLUMNS.len(),
    SET_COLUMNS.len(),
    DEREF_COLUMNS.len(),
    JUMP_COLUMNS.len(),
    SHA3_COLUMNS.len(),
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

/// The global column of a `SHA3` value lane: `prefix` is `in` or `out`.
pub fn sha3_lane(prefix: &str, lane: usize) -> usize {
    GLOBAL_COLUMN_BASES[OP_SHA3] + cols(SHA3_COLUMNS, [&format!("{prefix}_{lane}")])[0]
}

/// Each table's least log height: 0, but the Keccak reduction's block of steps for SHA3.
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
        count.extend(table.count_columns().map(|local| block(&vec![col(local, 0)])));
    }

    // Every column's log size, in global order: the framework's, q_keccak's, then each table's block.
    let qkeccak_kappa = table_log_heights[OP_SHA3] + QKECCAK_SLOT_BITS;
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

    // A SHA3 value lane gets no block of its own: an input lane is committed inside q_keccak, one slot of
    // 2^height words each, and an output lane not at all, nothing ever opening it.
    let limbs: BTreeMap<usize, u64> = (0..25).map(|l| (sha3_lane("in", l), l as u64)).collect();
    let outputs: Vec<usize> = (0..25).map(|l| sha3_lane("out", l)).collect();
    let blocks: Vec<usize> = (0..kappas.len())
        .filter(|column| !limbs.contains_key(column) && !outputs.contains(column))
        .collect();
    let block_kappas: Vec<usize> = blocks.iter().map(|&column| kappas[column]).collect();
    let (block_offsets, total_log) = stack_offsets(&block_kappas);
    let offsets: BTreeMap<usize, u64> = blocks.into_iter().zip(block_offsets).collect();
    let stack_log = MIN_STACKED_LOG.max(total_log); // Floor at the PCS minimum
    let placed = block_kappas.iter().map(|&kappa| 1 << kappa).sum();
    let placement = |(column, &kappa): (usize, &usize)| {
        let index = match limbs.get(&column) {
            Some(slot) => offsets[&QKECCAK] + (slot << kappa),
            None => *offsets.get(&column)?,
        };
        Some(Placement {
            variables: kappa,
            index,
            low: 0,
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
        placed,
        table_log_heights,
    })
}
