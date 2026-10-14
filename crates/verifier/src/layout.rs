//! The instruction tables, their bus flushes, and where every committed column sits in the stack.

use crate::bytecode::Bytecode;
use crate::field::{E, GEN, ONE, ZERO};
use crate::multilinear::{Placement, log2_strict, stack_offsets};
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
    pub log_rows: usize,        // the owner's height: this block flushes 2^log_rows rows
    pub coordinates: Vec<Form>, // the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    pub owner: usize,           // whose block it is, by opcode
}

pub const R1CS_DIGEST: [u8; 32] = [
    0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee, 0x64, 0x57, 0x33,
    0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea,
];

// The columns no instruction table owns. They come first in the global column numbering, the tables after.
pub const NUM_GLOBAL_COLUMNS: usize = 6;
pub const MEMORY_0: usize = 0;
pub const MEMORY_1: usize = 1;
pub const MEMORY_2: usize = 2;
pub const MEMORY_FINAL_COUNTERS: usize = 3;
pub const BYTECODE_FINAL_COUNTERS: usize = 4;
pub const QFLOCK: usize = 5;

pub const BLAKE2S_R1CS_LOG_SIZE: usize = 14;
pub const K_BITS: usize = 64;
pub const FLOCK_K_SKIP: usize = 6; // log2_ceil(K_BITS)
const LOG_PACKING: usize = 6; // bits per committed K-element: log2_ceil(K_BITS)

pub const FLOCK_NUM_LINCHECK_ROUNDS: usize = BLAKE2S_R1CS_LOG_SIZE - FLOCK_K_SKIP;
const QFLOCK_SLOT_BITS: usize = BLAKE2S_R1CS_LOG_SIZE - LOG_PACKING;
pub const BLAKE2S_CONSTANT_COLUMN: usize = 512;

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
    pub placements: Vec<Placement>,
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

fn flushes_blake2s() -> Flushes {
    let [pc, fp, cnt_bc] = cols(BLAKE2S_COLUMNS, ["pc", "fp", "cnt_bc"]);
    let operands = cols(BLAKE2S_COLUMNS, ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    flushes.bytecode(pc, cnt_bc, OP_BLAKE2S, operands.map(|i| col(i, 0)).to_vec());
    // The nine cells read, as (cell, operand, offset from it): four addressed message chunks, then
    // the consecutive chaining-value and output pairs, then the metadata cell (the byte counter and
    // the two flags). Each holds two q_flock limbs and a zero top.
    #[rustfmt::skip]
    let cells = [("m0", "o_0", 0), ("m1", "o_1", 0), ("m2", "o_2", 0), ("m3", "o_3", 0),
                 ("cv0", "o_v", 0), ("cv1", "o_v", 1), ("out0", "o_out", 0), ("out1", "o_out", 1),
                 ("md", "o_md", 0)];
    for (cell, operand, exponent) in cells {
        let names = [
            operand,
            &format!("cnt_{cell}"),
            &format!("{cell}_lo"),
            &format!("{cell}_hi"),
        ];
        let [address, count, lo, hi] = cols(BLAKE2S_COLUMNS, names);
        flushes.memory_cols(prod(fp, address, exponent), count, &[lo, hi]);
    }
    flushes
}

pub const OP_XOR: usize = 0;
pub const OP_MUL: usize = 1;
pub const OP_SET: usize = 2;
pub const OP_DEREF: usize = 3;
pub const OP_JUMP: usize = 4;
pub const OP_BLAKE2S: usize = 5;
pub const N_TABLES: usize = 6;

#[rustfmt::skip]
const ARITH_COLUMNS: &[&str] = &["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"];
const SET_COLUMNS: &[&str] = &["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"];
#[rustfmt::skip]
const DEREF_COLUMNS: &[&str] = &["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc"];
#[rustfmt::skip]
const JUMP_COLUMNS: &[&str] = &["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b"];
#[rustfmt::skip]
const BLAKE2S_COLUMNS: &[&str] = &[
    "pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    // These eighteen value limbs live in q_flock, not here: each is already a flock witness slot.
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo", "md_hi",
    // ...and the read counts, committed here like every other column.
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc",
];

pub fn tables() -> Vec<Table> {
    let table = |opcode, columns, flushes, constraints| Table {
        opcode,
        columns,
        flushes,
        constraints,
    };
    vec![
        table(OP_XOR, ARITH_COLUMNS, flushes_arith(OP_XOR, false), |_| vec![]),
        table(OP_MUL, ARITH_COLUMNS, flushes_arith(OP_MUL, true), |_| vec![]),
        table(OP_SET, SET_COLUMNS, flushes_set(), |_| vec![]),
        table(OP_DEREF, DEREF_COLUMNS, flushes_deref(), |_| vec![]),
        table(OP_JUMP, JUMP_COLUMNS, flushes_jump(), jump_constraints),
        table(OP_BLAKE2S, BLAKE2S_COLUMNS, flushes_blake2s(), |_| vec![]),
    ]
}

// Where in the flock witness each embedded BLAKE2s limb live: one 64-bit slot per limb, the chaining value first, then the
// digest, the message block and the metadata. Slots 8 and 9 are flock's constant wire and the padding up to its message base, which no memory cell carries.
#[rustfmt::skip]
const BLAKE2S_SLOTS: [Option<&str>; 20] = [
    Some("cv0_lo"), Some("cv0_hi"), Some("cv1_lo"), Some("cv1_hi"), Some("out0_lo"), Some("out0_hi"), Some("out1_lo"), Some("out1_hi"), None, None,
    Some("m0_lo"), Some("m0_hi"), Some("m1_lo"), Some("m1_hi"), Some("m2_lo"), Some("m2_hi"), Some("m3_lo"), Some("m3_hi"), Some("md_lo"), Some("md_hi"),
];

const TABLE_WIDTHS: [usize; N_TABLES] = [
    ARITH_COLUMNS.len(),
    ARITH_COLUMNS.len(),
    SET_COLUMNS.len(),
    DEREF_COLUMNS.len(),
    JUMP_COLUMNS.len(),
    BLAKE2S_COLUMNS.len(),
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

pub fn build_layout<'a>(
    bytecode: &'a Bytecode,
    log_memory: u64,
    table_log_heights: &[u64],
) -> Result<Layout<'a>, VerifierError> {
    let log_bytecode = log2_strict(bytecode.len() as u64)?;
    require(
        (16..=32).contains(&log_memory)
            && table_log_heights
                .iter()
                .all(|&log_height| log_height <= MAX_TABLE_LOG as u64)
            && table_log_heights[OP_BLAKE2S] >= 3
            && (BUS_BITS..=32 + BUS_BITS).contains(&log_bytecode),
        VerifierError::AnnouncedTableSizes,
    )?;
    let log_bytecode = log_bytecode - BUS_BITS;
    let log_memory = log_memory as usize;
    let table_log_heights: Vec<usize> = table_log_heights
        .iter()
        .map(|&log_height| log_height as usize)
        .collect();

    let tables = tables();
    let mut push = Vec::new();
    let mut pull = Vec::new();
    let mut count = Vec::new();
    for (table, &height) in tables.iter().zip(&table_log_heights) {
        let block = |coordinates: &Vec<Form>| BusBlock {
            log_rows: height,
            coordinates: coordinates.clone(),
            owner: table.opcode,
        };
        push.extend(table.flushes.push.iter().map(block));
        pull.extend(table.flushes.pull.iter().map(block));
        count.extend(table.count_columns().map(|local| block(&vec![col(local, 0)])));
    }

    // Every column's log size, in global order: the framework's, q_flock's, then each table's block.
    let qflock_kappa = table_log_heights[OP_BLAKE2S] + QFLOCK_SLOT_BITS;
    let mut kappas = vec![
        log_memory,
        log_memory,
        log_memory,
        log_memory,
        log_bytecode,
        qflock_kappa,
    ];
    for table in &tables {
        kappas.extend(vec![table_log_heights[table.opcode]; table.width()]);
    }

    // A BLAKE2s value limb gets no block of its own: it is committed inside q_flock, whose slots
    // interleave, so it sits at q_flock's offset behind its own slot's bits. Same width either way.
    let mut limbs = BTreeMap::new();
    for (slot, name) in BLAKE2S_SLOTS.iter().enumerate() {
        if let Some(name) = name {
            limbs.insert(
                GLOBAL_COLUMN_BASES[OP_BLAKE2S] + cols(BLAKE2S_COLUMNS, [name])[0],
                slot as u64,
            );
        }
    }
    let blocks: Vec<usize> = (0..kappas.len()).filter(|column| !limbs.contains_key(column)).collect();
    let block_kappas: Vec<usize> = blocks.iter().map(|&column| kappas[column]).collect();
    let (block_offsets, total_log) = stack_offsets(&block_kappas);
    let offsets: BTreeMap<usize, u64> = blocks.into_iter().zip(block_offsets).collect();
    let stack_log = MIN_STACKED_LOG.max(total_log); // Floor at the PCS minimum
    let placed = block_kappas.iter().map(|&kappa| 1 << kappa).sum();
    let placement = |(column, &kappa): (usize, &usize)| match limbs.get(&column) {
        Some(slot) => Placement {
            variables: kappa,
            index: offsets[&QFLOCK] + slot,
            low: QFLOCK_SLOT_BITS,
        },
        None => Placement {
            variables: kappa,
            index: offsets[&column],
            low: 0,
        },
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
