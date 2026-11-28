//! The instruction tables, their links, and where every committed column sits in the stack.

use crate::bytecode::Bytecode;
use crate::field::{E, GEN, ONE, ZERO};
use crate::hash::{STATE_LANES, keccak_f};
use crate::keccak::KeccakShape;
use crate::multilinear::{Placement, log2_ceil, log2_strict, stack_offsets};
use crate::{VerifierError, require};
use std::collections::BTreeMap;
use std::ops::Add;

/// The stacked program has `2^BYTECODE_SLOT_BITS` slots per instruction.
pub const BYTECODE_SLOT_BITS: usize = 4;

/// The opcode's slot: the link reads slots 1 and 2 as the program's address and presence columns, slot 0 unused, and
/// the operands follow (§sec:link-targets, §sec:e2e-bc).
pub const OPCODE_SLOT: usize = 3;

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

    /// The monomials and their coefficients: `[]` is 1, `[i]` is `x_i`, `[i, j]` is `x_i·x_j`.
    pub fn terms(&self) -> impl Iterator<Item = (&[usize], E)> {
        self.terms.iter().map(|(monomial, &c)| (monomial.as_slice(), c))
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

/// The proof system's version, leading the Fiat-Shamir IV's preimage so that no two versions share a
/// transcript. Its length is fixed and Keccak's padding binds the preimage's, so the bytecode that
/// follows needs no length field of its own. Nothing derives it from the constants below: any change
/// to the constraint system bumps it by hand. Mirrored in `formal/Statement/Verifier/Lib.lean`.
pub const TAG: &[u8] = b"leanvm-v1";

// The columns no instruction table owns. They come first in the global column numbering, the tables after.
pub const NUM_GLOBAL_COLUMNS: usize = 3;
pub const MEMORY_0: usize = 0;
pub const MEMORY_1: usize = 1;
pub const QKECCAK: usize = 2;

pub const K_BITS: usize = 64;

/// The Keccak reduction commits a step's state every `KECCAK_DEPTH` rounds but the output, a lane per slot of
/// `q_keccak` and a word per step: lane `l` of the state after `KECCAK_DEPTH·m` rounds is slot `25m + l`.
pub const KECCAK_DEPTH: usize = 12;
pub const KECCAK_MIN_STEPS_LOG: usize = 9; // the reduction is sized for at least one block of 512 steps

/// The bounds the announced sizes are first checked against, as logs: a table's rows, the memory and the bytecode. The
/// link's pointer width (`pointer_width`, at most `MAX_POINTER_WIDTH = 24` bits) then binds tighter: an execution
/// verifies only with at most `2^24` cells of memory and `2^24` instructions, and fewer than `2^24` cycles in all.
pub const MAX_TABLE_LOG: usize = 30;
/// The least memory a proof announces, as a log: the public input's two cells.
pub const MIN_LOG_MEMORY: usize = 1;
pub const MAX_LOG_MEMORY: usize = 30;
/// The largest bytecode, as a log of its instructions.
pub const MAX_LOG_BYTECODE: usize = 30;
/// The PCS's least and largest stacks, as logs.
pub const MIN_STACKED_LOG: usize = 16;
pub const MAX_STACKED_LOG: usize = 30;

pub struct Layout<'a> {
    pub log_memory: usize,
    pub log_bytecode: usize,
    pub bytecode: &'a Bytecode,
    pub tables: Vec<Table>,
    pub table_rows: Vec<u64>,
    /// Where each column sits, `None` for a column nothing commits: the `KECCAK` output lanes.
    pub placements: Vec<Option<Placement>>,
    pub stack_log: usize,
    pub table_log_heights: Vec<usize>,
    pub keccak: KeccakShape,
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

/// A row's step of the state chain: its cycle pointer, its `(pc, fp)`, and the successor state it derives.
#[derive(Clone, Debug)]
pub struct StateLink {
    pub cycle: usize,
    pub pc: usize,
    pub fp: usize,
    pub next: [Form; 2],
}

/// A row's read of the program: its pointer, its `pc`, its opcode, and each operand equation `Σ_{s ∈ slots} BC_s = form`
/// it checks against its instruction, weighed by the first slot's challenge. A slot no equation names is read only
/// through the accesses' [`Read`]s.
#[derive(Clone, Debug)]
pub struct BytecodeLink {
    pub pointer: usize,
    pub pc: usize,
    pub opcode: usize,
    pub operands: Vec<(Vec<usize>, Form)>,
}

/// A term of an access's value that the row reads where one of its pointers points, rather than from its columns.
#[derive(Clone, Debug)]
pub enum Read {
    /// `scale·word(σ)`, the word in the cell the row's pointer column `pointer` names; `scale` has degree at most one.
    Word { pointer: usize, scale: Form },
    /// `scale·BC_slot(σ_bc)`, a slot of the row's instruction.
    Slot { slot: usize, scale: E },
    /// `scale·fp·BC_slot(σ_bc)`.
    Frame { slot: usize, scale: E },
    /// `scale·pc·BC_slot(σ_bc)`, where `pc = g^{σ_bc}`.
    Pc { slot: usize, scale: E },
}

/// A row's memory access: its pointer and how far past the pointer's cell it reads, the column gating it if any, the
/// address, and the word `lo + y·hi`. The address is `address + g^e·fp·BC_slot(σ_bc)` for `frame = Some((slot, e))`,
/// and the word is `value + Σ reads`.
#[derive(Clone, Debug)]
pub struct Access {
    pub pointer: usize,
    pub shift: usize,
    pub gate: Option<usize>,
    pub address: Form,
    pub frame: Option<(usize, u64)>,
    pub value: Form,
    pub reads: Vec<Read>,
}

/// Everything a table links, over its own local column indices.
#[derive(Clone, Debug, Default)]
pub struct Links {
    state: Option<StateLink>,
    bytecode: Option<BytecodeLink>,
    pub memory: Vec<Access>,
}

/// `y`, the generator of `E` over `K`: a word is `lo + y·hi`.
pub const Y: E = E::new(0, 1);

impl Links {
    fn state_derived(&mut self, cycle: usize, pc: usize, fp: usize, npc: Form, nfp: Form) {
        self.state = Some(StateLink {
            cycle,
            pc,
            fp,
            next: [npc, nfp],
        });
    }

    fn state_step(&mut self, cycle: usize, pc: usize, fp: usize) {
        self.state_derived(cycle, pc, fp, col(pc, 1), col(fp, 0));
    }

    fn bytecode(&mut self, pc: usize, pointer: usize, opcode: usize, operands: Vec<(Vec<usize>, Form)>) {
        self.bytecode = Some(BytecodeLink {
            pointer,
            pc,
            opcode,
            operands,
        });
    }

    /// The access to the cell `shift` past the one `pointer` names, when the column `gate` is 1 if there is one; at
    /// 0 the access takes part in no link. A gated access reads nothing: its coefficients already hold the gate.
    #[allow(clippy::too_many_arguments)]
    fn access(
        &mut self,
        pointer: usize,
        shift: usize,
        gate: Option<usize>,
        address: Form,
        frame: Option<(usize, u64)>,
        value: Form,
        reads: Vec<Read>,
    ) {
        assert!(gate.is_none() || (frame.is_none() && reads.is_empty()));
        self.memory.push(Access {
            pointer,
            shift,
            gate,
            address,
            frame,
            value,
            reads,
        });
    }

    /// An ungated access to the cell at `fp·BC_slot(σ_bc)`.
    fn framed(&mut self, pointer: usize, slot: usize, value: Form, reads: Vec<Read>) {
        self.access(pointer, 0, None, Form::default(), Some((slot, 0)), value, reads);
    }

    pub fn state(&self) -> &StateLink {
        self.state.as_ref().expect("every table steps the state")
    }

    pub fn bytecode_link(&self) -> &BytecodeLink {
        self.bytecode.as_ref().expect("every table reads the program")
    }

    /// The pointer columns, in the order Hotwire numbers them: the cycle, the bytecode, then each access's pointer
    /// in order of first use.
    pub fn pointers(&self) -> Vec<usize> {
        let mut out = vec![self.state().cycle, self.bytecode_link().pointer];
        for access in &self.memory {
            if !out[2..].contains(&access.pointer) {
                out.push(access.pointer);
            }
        }
        out
    }

    /// The largest shift any access takes.
    pub fn max_shift(&self) -> usize {
        self.memory.iter().map(|a| a.shift).max().unwrap_or(0)
    }
}

/// One instruction's table: its columns, its links, its constraints.
pub struct Table {
    /// Also its index in the table list, so `g^opcode` is its bytecode tag.
    pub opcode: usize,
    pub columns: Vec<String>,
    /// The row a padding row holds.
    pub padding: Vec<E>,
    pub links: Links,
    pub constraints: fn(&[E]) -> Vec<E>,
}

impl Table {
    pub fn n_constraints(&self) -> usize {
        (self.constraints)(&vec![ZERO; self.width()]).len()
    }

    pub fn width(&self) -> usize {
        self.columns.len()
    }
}

fn word(pointer: usize) -> Read {
    Read::Word {
        pointer,
        scale: constant(ONE),
    }
}

// The operands of XOR, MUL, SET, DEREF and JUMP sit in bytecode slots 4, 5, 6, 7 and 8, in the order the ISA lists them.

fn links_arith(opcode: usize, multiply: bool) -> Links {
    let columns = if multiply { MUL_COLUMNS } else { XOR_COLUMNS };
    let [pc, fp, ix_a, ix_b, ix_c, ix_bc, ix_cycle] =
        cols(columns, ["pc", "fp", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]);
    let mut links = Links::default();
    links.state_step(ix_cycle, pc, fp);
    links.bytecode(pc, ix_bc, opcode, vec![]);
    if multiply {
        // `a` is committed, `b` is read where its pointer points, and `c = a·b` is linear in that read.
        let [a0, a1] = cols(columns, ["a_0", "a_1"]);
        let a = col(a0, 0) + Form::term(vec![a1], Y);
        links.framed(ix_a, 4, a.clone(), vec![]);
        links.framed(ix_b, 5, Form::default(), vec![word(ix_b)]);
        links.framed(
            ix_c,
            6,
            Form::default(),
            vec![Read::Word {
                pointer: ix_b,
                scale: a,
            }],
        );
    } else {
        links.framed(ix_a, 4, Form::default(), vec![word(ix_a)]);
        links.framed(ix_b, 5, Form::default(), vec![word(ix_b)]);
        links.framed(ix_c, 6, Form::default(), vec![word(ix_a), word(ix_b)]);
    }
    links
}

fn links_set() -> Links {
    let [pc, fp, ix, ix_bc, ix_cycle] = cols(SET_COLUMNS, ["pc", "fp", "ix", "ix_bc", "ix_cycle"]);
    let mut links = Links::default();
    links.state_step(ix_cycle, pc, fp);
    links.bytecode(pc, ix_bc, OP_SET, vec![]);
    // The stored immediate's two limbs are slots 5 and 6 of the instruction.
    let immediate = vec![Read::Slot { slot: 5, scale: ONE }, Read::Slot { slot: 6, scale: Y }];
    links.framed(ix, 4, Form::default(), immediate);
    links
}

fn links_deref() -> Links {
    let [pc, fp, ptr, o2, s] = cols(DEREF_COLUMNS, ["pc", "fp", "ptr", "o2", "s"]);
    let [ix_ptr, ix_target, ix_local, ix_bc, ix_cycle] =
        cols(DEREF_COLUMNS, ["ix_ptr", "ix_target", "ix_local", "ix_bc", "ix_cycle"]);
    let mut links = Links::default();
    links.state_step(ix_cycle, pc, fp);
    // `s = f_pc + f_fp`, which is 1 exactly when a flag is set.
    links.bytecode(
        pc,
        ix_bc,
        OP_DEREF,
        vec![(vec![5], col(o2, 0)), (vec![7, 8], col(s, 0))],
    );
    links.framed(ix_ptr, 4, col(ptr, 0), vec![]);
    // v2 = (1 + s)*v3 + f_pc*(g^2*pc) + f_fp*fp: only the low lane takes the two K-valued sources.
    let store = vec![
        Read::Word {
            pointer: ix_local,
            scale: constant(ONE) + col(s, 0),
        },
        Read::Pc {
            slot: 7,
            scale: gpow(2),
        },
        Read::Frame { slot: 8, scale: ONE },
    ];
    links.access(ix_target, 0, None, prod(ptr, o2, 0), None, Form::default(), store);
    links.framed(ix_local, 6, Form::default(), vec![word(ix_local)]);
    links
}

fn links_jump() -> Links {
    let [pc, fp, cond, dest, frame, pc_next, fp_next] = cols(
        JUMP_COLUMNS,
        ["pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next"],
    );
    let [ix_c, ix_d, ix_f, ix_bc, ix_cycle] = cols(JUMP_COLUMNS, ["ix_c", "ix_d", "ix_f", "ix_bc", "ix_cycle"]);
    let mut links = Links::default();
    // The successor is committed, so the state link stays affine; the identities tie it to the jump.
    links.state_derived(ix_cycle, pc, fp, col(pc_next, 0), col(fp_next, 0));
    links.bytecode(pc, ix_bc, OP_JUMP, vec![]);
    // The three words are K-valued on every row, taken or not: committed as one lane, the high one zero.
    links.framed(ix_c, 4, col(cond, 0), vec![]);
    links.framed(ix_d, 5, col(dest, 0), vec![]);
    links.framed(ix_f, 6, col(frame, 0), vec![]);
    links
}

/// `b = [cond ≠ 0]` by its inverse `w`, and the successor `b·(v_pc, v_fp) + (1 + b)·(g·pc, fp)` (§sec:tab-jump).
fn jump_constraints(columns: &[E]) -> Vec<E> {
    let [pc, fp, condition, dest, frame, pc_next, fp_next, inverse, flag] = cols(
        JUMP_COLUMNS,
        ["pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next", "w", "b"],
    )
    .map(|index| columns[index]);
    let untaken = flag + ONE;
    vec![
        flag + condition * inverse,
        condition * untaken,
        pc_next + flag * dest + untaken * gpow(1) * pc,
        fp_next + flag * frame + untaken * fp,
    ]
}

/// The lanes each of a sponge state's thirteen cells holds, `(lo, hi)`, in the even layout or the odd one, `None`
/// marking a limb that holds no lane: nine rate cells, lanes 0..16 two to a cell then lane 16 in a low limb (even), or
/// lane 0 in a high limb then lanes 1..17 two to a cell (odd), then the capacity lanes 17..25.
pub const fn keccak_cell_lanes(odd: bool) -> [(Option<usize>, Option<usize>); KECCAK_CELLS] {
    let mut lanes = [(None, None); KECCAK_CELLS];
    let mut cell = 0;
    while cell < KECCAK_CELLS {
        lanes[cell] = match (odd, cell) {
            (_, 9..) | (true, 1..) => (Some(2 * cell - 1), Some(2 * cell)),
            (true, _) => (None, Some(0)),
            (false, 8) => (Some(16), None),
            (false, _) => (Some(2 * cell), Some(2 * cell + 1)),
        };
        cell += 1;
    }
    lanes
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

/// The bytecode slot of KECCAK's offset operand `i`, in the order `m0..m3, tail, b8, cap, out`.
pub const fn keccak_offset_slot(i: usize) -> usize {
    OPCODE_SLOT + 1 + i
}

fn links_keccak() -> Links {
    let [pc, fp, free, o_out] = cols(KECCAK_HEAD, ["pc", "fp", "free", "o_out"]);
    let [in_odd, out_odd, out_two, out_all] = cols(KECCAK_HEAD, ["odd_in", "odd_out", "out_two", "out_all"]);
    let mut links = Links::default();
    links.state_step(KECCAK_CYCLE, pc, fp);
    // The seven read offsets ride the instruction alone; `out` and the four flags are committed.
    let operands = [o_out, in_odd, out_odd, out_two, out_all]
        .into_iter()
        .enumerate()
        .map(|(i, c)| (vec![keccak_offset_slot(7) + i], col(c, 0)))
        .collect();
    links.bytecode(pc, KECCAK_IX_BC, OP_KECCAK, operands);
    // The thirteen cells read (four addressed ones, the tail run, b8, the cap run), then the thirteen written, each
    // holding its lanes in the layout its flag names: a read cell's free lane is the column `free`, a written one's zero.
    // Output cell 0 is always written, cell 1 when `out_two` is 1, and cells 2..13 when `out_all` is 1.
    // A cell's operand, as `keccak_offset_slot` orders the eight, and its step past the operand's cell, whose pointer
    // is `KECCAK_IX + operand`.
    let part = |cell: usize| match cell {
        0..4 => (cell, 0),
        4..8 => (4, cell - 4),
        8 => (5, 0),
        _ => (6, cell - 9),
    };
    let (even, odd) = (keccak_cell_lanes(false), keccak_cell_lanes(true));
    for (side, lanes, flag, missing) in [(0, KECCAK_IN, in_odd, Some(free)), (1, KECCAK_OUT, out_odd, None)] {
        let lane = |lane: Option<usize>| lane.map(|lane| lanes + lane);
        for cell in 0..KECCAK_CELLS {
            let limb = |e: Option<usize>, o: Option<usize>| layout_limb(lane(e), lane(o), flag, missing);
            let mut value = limb(even[cell].0, odd[cell].0);
            value.add_scaled(&limb(even[cell].1, odd[cell].1), Y);
            if side == 0 {
                let (operand, step) = part(cell);
                let frame = Some((keccak_offset_slot(operand), step as u64));
                links.access(KECCAK_IX + operand, step, None, Form::default(), frame, value, vec![]);
            } else {
                let gate = match cell {
                    0 => None,
                    1 => Some(out_two),
                    _ => Some(out_all),
                };
                let address = prod(fp, o_out, cell as u64);
                links.access(KECCAK_IX + 7, cell, gate, address, None, value, vec![]);
            }
        }
    }
    links
}

pub const OP_XOR: usize = 0;
pub const OP_MUL: usize = 1;
pub const OP_SET: usize = 2;
pub const OP_DEREF: usize = 3;
pub const OP_JUMP: usize = 4;
pub const OP_KECCAK: usize = 5;
pub const N_TABLES: usize = 6;

const XOR_COLUMNS: &[&str] = &["pc", "fp", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"];
const MUL_COLUMNS: &[&str] = &["pc", "fp", "a_0", "a_1", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"];
const SET_COLUMNS: &[&str] = &["pc", "fp", "ix", "ix_bc", "ix_cycle"];
#[rustfmt::skip]
const DEREF_COLUMNS: &[&str] = &["pc", "fp", "ptr", "o2", "s", "ix_ptr", "ix_target", "ix_local", "ix_bc", "ix_cycle"];
#[rustfmt::skip]
const JUMP_COLUMNS: &[&str] = &["pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next", "w", "b", "ix_c", "ix_d", "ix_f", "ix_bc", "ix_cycle"];
// KECCAK's columns: these, then the input lanes `in_l`, the output lanes `out_l`, the eight block pointers
// (`KECCAK_IX..KECCAK_IX + 8`: the four addressed cells, `tail`, `b8`, `cap`, the output run), `ix_bc` and
// `ix_cycle`. The fifty value lanes are not committed in the table: an input lane is one of q_keccak's slots, and the
// output lanes' claims are the Keccak reduction's claim on the output.
const KECCAK_HEAD: &[&str] = &["pc", "fp", "o_out", "odd_in", "odd_out", "out_two", "out_all", "free"];
/// Cells a sponge state occupies, which `KECCAK` reads then writes.
pub const KECCAK_CELLS: usize = 13;
pub const KECCAK_IN: usize = KECCAK_HEAD.len();
pub const KECCAK_OUT: usize = KECCAK_IN + STATE_LANES;
pub const KECCAK_IX: usize = KECCAK_OUT + STATE_LANES;
const KECCAK_IX_BC: usize = KECCAK_IX + 8;
const KECCAK_CYCLE: usize = KECCAK_IX_BC + 1;

/// The local KECCAK column riding spare slot `k` (`cpu::keccak_value` in the prover): its
/// committed columns in local order, the ones before the value lanes then the pointers
/// after them.
pub const fn spare_local(k: usize) -> usize {
    if k < KECCAK_IN { k } else { KECCAK_IX + (k - KECCAK_IN) }
}

/// Slots of the run the committed states occupy, and the ones they leave over.
pub const QKECCAK_SLOTS: usize = STATE_LANES * (crate::hash::ROUNDS / KECCAK_DEPTH);
pub const QKECCAK_SPARE: usize = (1 << log2_ceil(QKECCAK_SLOTS as u64)) - QKECCAK_SLOTS;
// The same guard the prover carries (`cpu::layout`): every spare slot needs a committed column
// of the table to put in it, distinct from the others and not one of the value lanes. It holds
// at this depth, not at every divisor of 24, and the two sides must refuse together.
const _: () = {
    let mut k = 0;
    while k < QKECCAK_SPARE {
        let local = spare_local(k);
        assert!(k == 0 || spare_local(k - 1) < local);
        assert!(local < KECCAK_IN || (local >= KECCAK_IX && local < TABLE_WIDTHS[OP_KECCAK]));
        k += 1;
    }
};

/// The slot of `q_keccak` the global column `column` IS, if it is one: an input lane (slot =
/// lane), or one of the KECCAK table's own columns riding a slot past the committed states.
/// The reduction weighs nothing on those spare slots, so the stack carries those columns
/// there rather than a block of zeros and a block of its own.
pub fn qkeccak_slot(column: usize) -> Option<usize> {
    let local = column.checked_sub(GLOBAL_COLUMN_BASES[OP_KECCAK])?;
    if let Some(k) = (0..QKECCAK_SPARE).find(|&k| spare_local(k) == local) {
        return Some(QKECCAK_SLOTS + k);
    }
    (KECCAK_IN..KECCAK_OUT).contains(&local).then(|| local - KECCAK_IN)
}

fn keccak_columns() -> Vec<String> {
    let lanes = |prefix: &'static str| (0..STATE_LANES).map(move |lane| format!("{prefix}_{lane}"));
    let pointers = ["m0", "m1", "m2", "m3", "tail", "b8", "cap", "out"].map(|operand| format!("ix_{operand}"));
    let head = KECCAK_HEAD.iter().map(|name| name.to_string());
    head.chain(lanes("in"))
        .chain(lanes("out"))
        .chain(pointers)
        .chain(["ix_bc".to_string(), "ix_cycle".to_string()])
        .collect()
}

pub fn tables() -> Vec<Table> {
    let table = |opcode, columns: Vec<String>, links, constraints| Table {
        opcode,
        padding: vec![ZERO; columns.len()],
        columns,
        links,
        constraints,
    };
    let named = |columns: &[&str]| columns.iter().map(|name| name.to_string()).collect();
    let mut keccak = table(OP_KECCAK, keccak_columns(), links_keccak(), |_| vec![]);
    // A padding row is zero, but for KECCAK's output lanes: a padding row permutes zeros.
    let mut output = [0; STATE_LANES];
    keccak_f(&mut output);
    for (padding, lane) in keccak.padding[KECCAK_OUT..].iter_mut().zip(output) {
        *padding = E::new(lane, 0);
    }
    vec![
        table(OP_XOR, named(XOR_COLUMNS), links_arith(OP_XOR, false), |_| vec![]),
        table(OP_MUL, named(MUL_COLUMNS), links_arith(OP_MUL, true), |_| vec![]),
        table(OP_SET, named(SET_COLUMNS), links_set(), |_| vec![]),
        table(OP_DEREF, named(DEREF_COLUMNS), links_deref(), |_| vec![]),
        table(OP_JUMP, named(JUMP_COLUMNS), links_jump(), jump_constraints),
        keccak,
    ]
}

pub const TABLE_WIDTHS: [usize; N_TABLES] = [
    XOR_COLUMNS.len(),
    MUL_COLUMNS.len(),
    SET_COLUMNS.len(),
    DEREF_COLUMNS.len(),
    JUMP_COLUMNS.len(),
    KECCAK_CYCLE + 1,
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
pub const TABLE_LOG_FLOORS: [usize; N_TABLES] = [0, 0, 0, 0, 0, KECCAK_MIN_STEPS_LOG];

fn keccak_shape(table_log_heights: &[usize]) -> KeccakShape {
    KeccakShape {
        log_steps: table_log_heights[OP_KECCAK],
        depth: KECCAK_DEPTH,
    }
}

/// Every column's log size, in global order: the framework's, q_keccak's, then each table's block.
fn column_kappas(tables: &[Table], log_memory: usize, table_log_heights: &[usize]) -> Vec<usize> {
    let keccak = keccak_shape(table_log_heights);
    let mut kappas = vec![log_memory, log_memory, keccak.log_steps + keccak.slot_bits()];
    for table in tables {
        kappas.extend(vec![table_log_heights[table.opcode]; table.width()]);
    }
    kappas
}

/// What a stack block's log size is, in terms of the announced sizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SizeSource {
    Memory,
    Table(usize),
}

/// A column with a block of its own in the stack: its log size is its source's plus `adj`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StackBlock {
    pub column: usize,
    pub source: SizeSource,
    pub adj: usize,
}

/// The stack's blocks, in global column order. A column q_keccak carries gets none: it is one of its slots, 2^height
/// words, whether an input lane or a KECCAK column riding a spare slot (`qkeccak_slot`). An output lane is not
/// committed at all, nothing ever opening it.
pub fn stack_blocks() -> Vec<StackBlock> {
    let outputs =
        GLOBAL_COLUMN_BASES[OP_KECCAK] + KECCAK_OUT..GLOBAL_COLUMN_BASES[OP_KECCAK] + KECCAK_OUT + STATE_LANES;
    let mut blocks = vec![
        StackBlock {
            column: MEMORY_0,
            source: SizeSource::Memory,
            adj: 0,
        },
        StackBlock {
            column: MEMORY_1,
            source: SizeSource::Memory,
            adj: 0,
        },
        StackBlock {
            column: QKECCAK,
            source: SizeSource::Table(OP_KECCAK),
            adj: log2_ceil(QKECCAK_SLOTS as u64),
        },
    ];
    for table in tables() {
        let base = GLOBAL_COLUMN_BASES[table.opcode];
        for local in 0..table.width() {
            let column = base + local;
            if qkeccak_slot(column).is_none() && !outputs.contains(&column) {
                blocks.push(StackBlock {
                    column,
                    source: SizeSource::Table(table.opcode),
                    adj: 0,
                });
            }
        }
    }
    blocks
}

/// The stack of columns of these log sizes: each stacked column's offset, and its log size, floored at the PCS minimum.
fn stack(kappas: &[usize]) -> (BTreeMap<usize, u64>, usize) {
    let blocks = stack_blocks();
    let block_kappas: Vec<usize> = blocks.iter().map(|block| kappas[block.column]).collect();
    let (block_offsets, total_log) = stack_offsets(&block_kappas);
    (
        blocks.iter().map(|block| block.column).zip(block_offsets).collect(),
        MIN_STACKED_LOG.max(total_log),
    )
}

/// The stack of the smallest execution of a bytecode of `2^log_bytecode` instructions: the least memory, every table at
/// its floor. A recursion guest, whose children are proofs of its own bytecode, need open no smaller one. The program
/// is public and has no committed column, so the stack does not depend on its size.
pub fn min_execution_stacked_log(_log_bytecode: usize) -> usize {
    let tables = tables();
    stack(&column_kappas(&tables, MIN_LOG_MEMORY, &TABLE_LOG_FLOORS)).1
}

/// Each table's log height: the least power of two holding its rows, at least its floor.
pub fn table_log_heights(table_rows: &[u64]) -> Vec<usize> {
    table_rows
        .iter()
        .zip(TABLE_LOG_FLOORS)
        .map(|(&rows, floor)| log2_ceil(rows).max(floor))
        .collect()
}

pub fn build_layout<'a>(
    bytecode: &'a Bytecode,
    log_memory: u64,
    table_rows: &[u64],
) -> Result<Layout<'a>, VerifierError> {
    let log_bytecode = log2_strict(bytecode.len() as u64)?;
    require(
        (MIN_LOG_MEMORY as u64..=MAX_LOG_MEMORY as u64).contains(&log_memory)
            && table_rows.iter().all(|&rows| rows <= 1 << MAX_TABLE_LOG)
            && (BYTECODE_SLOT_BITS..=MAX_LOG_BYTECODE + BYTECODE_SLOT_BITS).contains(&log_bytecode),
        VerifierError::AnnouncedTableSizes,
    )?;
    let log_bytecode = log_bytecode - BYTECODE_SLOT_BITS;
    let log_memory = log_memory as usize;
    let table_log_heights = table_log_heights(table_rows);

    let tables = tables();

    let keccak = keccak_shape(&table_log_heights);
    let kappas = column_kappas(&tables, log_memory, &table_log_heights);
    let (offsets, stack_log) = stack(&kappas);
    let placement = |(column, &kappa): (usize, &usize)| {
        let index = match qkeccak_slot(column) {
            Some(slot) => offsets[&QKECCAK] + ((slot as u64) << kappa),
            None => *offsets.get(&column)?,
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
        table_rows: table_rows.to_vec(),
        placements,
        stack_log,
        table_log_heights,
        keccak,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Block sizes only grow with the size limits, so the limits are the worst case for `stack_offsets`.
    #[test]
    fn stack_offsets_fit_at_size_limits() {
        let table_log_heights = table_log_heights(&[1u64 << MAX_TABLE_LOG; N_TABLES]);
        let kappas = column_kappas(&tables(), MAX_LOG_MEMORY, &table_log_heights);
        let sizes: Vec<usize> = stack_blocks().iter().map(|block| kappas[block.column]).collect();
        assert!(sizes.len() >= 2, "the stack must have at least two blocks");
        let mut total = 0u64;
        for exponent in sizes {
            assert!(
                exponent < u64::BITS as usize,
                "block exponent {exponent} exceeds the shift range"
            );
            total = total.checked_add(1u64 << exponent).expect("block sizes exceed u64");
        }
    }
}
