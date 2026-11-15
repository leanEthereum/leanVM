//! The public structure of a proof that the aggregation guest bakes in and reads its children with: each bus block's
//! coordinates as the prover writes them ([`Coord`]), the committed columns' kappa sources and stacking, the stacked
//! bytecode, and the constants of the bus, the table sumcheck, the Keccak reduction and the opening.
//!
//! The tables, their columns and every size come from the verifier (`verifier::layout`). What is restated here is the
//! order in which the prover writes each coordinate's terms, which the guest's term arrays list.

use isa::Op;
use verifier::layout::{self as spec, GLOBAL_COLUMN_BASES, N_TABLES, OP_KECCAK};
use verifier::{E, K, KeccakShape, grinding_bits};

/// The columns no table owns, first in the global numbering.
pub(crate) const MEM_LO: usize = spec::MEMORY_0;
pub(crate) const MEM_HI: usize = spec::MEMORY_1;
const MFCNT: usize = spec::MEMORY_FINAL_COUNTERS;
const BFCNT: usize = spec::BYTECODE_FINAL_COUNTERS;
pub(crate) const QKECCAK: usize = spec::QKECCAK;

/// Bits indexing a bus tuple's coordinates, and the stacked bytecode's selector bits: its sixteen slots are those.
pub(crate) const N_TUPLE_BITS: usize = spec::BUS_BITS;
pub(crate) const N_BYTECODE_SELECTORS: usize = spec::BUS_BITS;
/// Slot of the first public column: a bytecode tuple leads with its tag, its index and its read count.
const BYTECODE_PUBLIC_SLOT: usize = 3;
/// Operand slots of a bytecode tuple, after the opcode.
const BYTECODE_OPERANDS: usize = 12;

/// Rounds between two committed Keccak states.
pub(crate) const KECCAK_DEPTH: usize = spec::KECCAK_DEPTH;
/// The reduction's shape at its fewest steps.
pub(crate) const KECCAK_MIN_SHAPE: KeccakShape = KeccakShape {
    log_steps: spec::KECCAK_MIN_STEPS_LOG,
    depth: KECCAK_DEPTH,
};

/// `log2` of the slots `q_keccak` holds per step.
pub(crate) fn slot_log() -> usize {
    KECCAK_MIN_SHAPE.slot_bits()
}

/// `g^n` in `K`, `n < 2^32`.
pub(crate) fn g_pow(n: usize) -> K {
    static TABLES: std::sync::OnceLock<GPow> = std::sync::OnceLock::new();
    TABLES
        .get_or_init(GPow::new)
        .at(u32::try_from(n).expect("an exponent below 2^32"))
}

/// One tuple coordinate as a function of its block's row `z`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Coord {
    /// A public constant.
    Const(K),
    /// A committed column.
    Col(usize),
    /// `g^k` times a committed column.
    GCol(usize, u32),
    /// `g^k` times the product of two committed columns.
    Prod(usize, usize, u32),
    /// The index column `g^z`.
    Index,
    /// One of the program's public bytecode columns: the opcode, then the operand slots.
    Public(usize),
    /// A sum of `Const`, `Col`, `GCol` and `Prod` terms, in a table's blocks only.
    Sum(Vec<Coord>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates, and for a table's block the tuple its padding row
/// holds.
#[derive(Clone, Debug)]
pub(crate) struct Block {
    pub(crate) kappa: usize,
    pub(crate) coords: Vec<Coord>,
    pub(crate) padding: Vec<K>,
}

/// A table coordinate's value on a row whose local columns are `row`.
fn coord_at(c: &Coord, row: &[K]) -> K {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => row[*i],
        Coord::GCol(i, k) => g_pow(*k as usize) * row[*i],
        Coord::Prod(i, j, k) => g_pow(*k as usize) * row[*i] * row[*j],
        Coord::Sum(cs) => cs.iter().fold(K(0), |sum, c| sum + coord_at(c, row)),
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    }
}

fn offset_coord(base: usize, c: &Coord) -> Coord {
    match c {
        Coord::Col(i) => Coord::Col(base + i),
        Coord::GCol(i, k) => Coord::GCol(base + i, *k),
        Coord::Prod(i, j, k) => Coord::Prod(base + i, base + j, *k),
        Coord::Sum(cs) => Coord::Sum(cs.iter().map(|c| offset_coord(base, c)).collect()),
        other => other.clone(),
    }
}

/// A table's push and pull flushes, in its local columns. The push of a memory-checked entry carries the count
/// advanced by `g` where the pull carries it as read.
#[derive(Default)]
struct Flushes {
    push: Vec<Vec<Coord>>,
    pull: Vec<Vec<Coord>>,
}

use Coord::{Col, Const, GCol, Prod};

impl Flushes {
    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    fn state_step(&mut self, pc: usize, fp: usize) {
        let sep = Const(K(spec::SEP_STATE.c0));
        self.pair(vec![sep.clone(), GCol(pc, 1), Col(fp)], vec![sep, Col(pc), Col(fp)]);
    }

    fn state_derived(&mut self, pc: usize, fp: usize, npc: Coord, nfp: Coord) {
        let sep = Const(K(spec::SEP_STATE.c0));
        self.pair(vec![sep.clone(), npc, nfp], vec![sep, Col(pc), Col(fp)]);
    }

    fn bytecode(&mut self, pc: usize, count: usize, opcode: usize, operands: &[Coord]) {
        let (sep, opcode) = (Const(K(spec::SEP_BYTECODE.c0)), Const(g_pow(opcode)));
        let push = [sep.clone(), Col(pc), GCol(count, 1), opcode.clone()];
        let pull = [sep, Col(pc), Col(count), opcode];
        self.pair([&push[..], operands].concat(), [&pull[..], operands].concat());
    }

    fn memory_pushing(&mut self, counter: Coord, addr: Coord, count: usize, vals: [Coord; 2]) {
        let sep = Const(K(spec::SEP_MEM.c0));
        let push = [sep.clone(), addr.clone(), counter];
        let pull = [sep, addr, Col(count)];
        self.pair([&push[..], &vals].concat(), [&pull[..], &vals].concat());
    }

    fn memory_coords(&mut self, addr: Coord, count: usize, vals: [Coord; 2]) {
        self.memory_pushing(GCol(count, 1), addr, count, vals);
    }

    /// [`Self::memory_coords`] when the column `flag` is 1: the push's counter is `count·(1 + flag·(g + 1))`.
    fn memory_coords_if(&mut self, flag: usize, addr: Coord, count: usize, vals: [Coord; 2]) {
        let counter = Coord::Sum(vec![Col(count), Prod(flag, count, 1), Prod(flag, count, 0)]);
        self.memory_pushing(counter, addr, count, vals);
    }

    fn memory(&mut self, addr: Coord, count: usize, lo: usize, hi: usize) {
        self.memory_coords(addr, count, [Col(lo), Col(hi)]);
    }

    /// A `K`-valued word: the high limb is zero.
    fn memory_k(&mut self, addr: Coord, count: usize, value: usize) {
        self.memory_coords(addr, count, [Col(value), Const(K(0))]);
    }
}

/// The tower product's lanes: lane `i` is `Σ g^e·x_j·y_k` over `(j, k, e)` in `TOWER_LANES[i]`.
const TOWER_LANES: [&[(usize, usize, u32)]; 2] = [&[(0, 0, 0), (1, 1, 0)], &[(0, 1, 0), (1, 0, 0), (1, 1, 1)]];

/// A cell limb holding lane `even` in the even layout and `odd` in the odd one, as `flag` selects: `a + flag·(a + b)`,
/// a missing lane being the column `missing`, or zero.
fn layout_limb(even: Option<usize>, odd: Option<usize>, values: usize, flag: usize, missing: Option<usize>) -> Coord {
    let col = |lane: Option<usize>| lane.map(|l| values + l).or(missing);
    let (a, b) = (col(even), col(odd));
    if a == b {
        return a.map_or(Const(K(0)), Col);
    }
    Coord::Sum(
        [a.map(Col), a.map(|a| Prod(flag, a, 0)), b.map(|b| Prod(flag, b, 0))]
            .into_iter()
            .flatten()
            .collect(),
    )
}

/// Table `table`'s flushes, as the prover writes them.
fn flushes(table: &spec::Table) -> Flushes {
    let c = |name: &str| {
        table
            .columns
            .iter()
            .position(|column| column == name)
            .unwrap_or_else(|| panic!("no column {name}"))
    };
    let zero = || Const(K(0));
    let mut f = Flushes::default();
    let (pc, fp, bc) = (c("pc"), c("fp"), c("cnt_bc"));
    match table.opcode {
        spec::OP_XOR | spec::OP_MUL => {
            let (a, b) = ([c("va_0"), c("va_1")], [c("vb_0"), c("vb_1")]);
            f.state_step(pc, fp);
            let operands = [Col(c("o_a")), Col(c("o_b")), Col(c("o_c")), zero(), zero()];
            f.bytecode(pc, bc, table.opcode, &operands);
            f.memory(Prod(fp, c("o_a"), 0), c("cnt_a"), a[0], a[1]);
            f.memory(Prod(fp, c("o_b"), 0), c("cnt_b"), b[0], b[1]);
            let result = if table.opcode == spec::OP_XOR {
                [0, 1].map(|i| Coord::Sum(vec![Col(a[i]), Col(b[i])]))
            } else {
                TOWER_LANES.map(|lane| Coord::Sum(lane.iter().map(|&(j, k, e)| Prod(a[j], b[k], e)).collect()))
            };
            f.memory_coords(Prod(fp, c("o_c"), 0), c("cnt_c"), result);
        }
        spec::OP_SET => {
            let k = [c("k_0"), c("k_1")];
            f.state_step(pc, fp);
            f.bytecode(
                pc,
                bc,
                spec::OP_SET,
                &[Col(c("o")), Col(k[0]), Col(k[1]), zero(), zero()],
            );
            f.memory(Prod(fp, c("o"), 0), c("cnt"), k[0], k[1]);
        }
        spec::OP_DEREF => {
            let (f_pc, f_fp, ptr, v3) = (c("f_pc"), c("f_fp"), c("ptr"), [c("v3_0"), c("v3_1")]);
            f.state_step(pc, fp);
            let operands = ["o1", "o2", "o3", "f_pc", "f_fp"].map(|name| Col(c(name)));
            f.bytecode(pc, bc, spec::OP_DEREF, &operands);
            f.memory_k(Prod(fp, c("o1"), 0), c("cnt_ptr"), ptr);
            // The stored word: `(1 + f_pc + f_fp)·v3 + f_pc·(g²·pc) + f_fp·fp`, the K-valued sources in the low lane.
            let gated = |v: usize| vec![Col(v), Prod(f_pc, v, 0), Prod(f_fp, v, 0)];
            let low = [gated(v3[0]), vec![Prod(f_pc, pc, 2), Prod(f_fp, fp, 0)]].concat();
            let store = [Coord::Sum(low), Coord::Sum(gated(v3[1]))];
            f.memory_coords(Prod(ptr, c("o2"), 0), c("cnt_target"), store);
            f.memory(Prod(fp, c("o3"), 0), c("cnt_local"), v3[0], v3[1]);
        }
        spec::OP_JUMP => {
            let (b, v_pc, v_fp) = (c("b"), c("v_pc"), c("v_fp"));
            f.state_derived(
                pc,
                fp,
                Coord::Sum(vec![Prod(b, v_pc, 0), Prod(b, pc, 1), GCol(pc, 1)]),
                Coord::Sum(vec![Prod(b, v_fp, 0), Prod(b, fp, 0), Col(fp)]),
            );
            let operands = [Col(c("o_c")), Col(c("o_d")), Col(c("o_f")), zero(), zero()];
            f.bytecode(pc, bc, spec::OP_JUMP, &operands);
            f.memory_k(Prod(fp, c("o_c"), 0), c("cnt_c"), c("v_cond"));
            f.memory_k(Prod(fp, c("o_d"), 0), c("cnt_d"), v_pc);
            f.memory_k(Prod(fp, c("o_f"), 0), c("cnt_f"), v_fp);
        }
        OP_KECCAK => {
            let o_m0 = c("o_m0");
            let (in_odd, out_odd, out_two, out_all) = (c("odd_in"), c("odd_out"), c("out_two"), c("out_all"));
            f.state_step(pc, fp);
            let operands: Vec<Coord> = (o_m0..=out_all).map(Col).collect();
            f.bytecode(pc, bc, OP_KECCAK, &operands);
            // Thirteen cells read, then thirteen written: output cell 0 always, cell 1 as `out_two` says, the rest
            // as `out_all` says. A cell's address is its offset operand's, times `g` per cell along a run.
            let (even, odd) = (spec::keccak_cell_lanes(false), spec::keccak_cell_lanes(true));
            let cells = spec::KECCAK_CELLS;
            for cell in 0..2 * cells {
                let (operand, step) = match cell {
                    0..4 => (cell, 0),
                    4..8 => (4, cell - 4),
                    8 => (5, 0),
                    9..13 => (6, cell - 9),
                    _ => (7, cell - 13),
                };
                let (s, values, flag, free) = match cell < cells {
                    true => (cell, spec::KECCAK_IN, in_odd, Some(c("free"))),
                    false => (cell - cells, spec::KECCAK_OUT, out_odd, None),
                };
                let lo = layout_limb(even[s].0, odd[s].0, values, flag, free);
                let hi = layout_limb(even[s].1, odd[s].1, values, flag, free);
                let (addr, count) = (Prod(fp, o_m0 + operand, step as u32), c(&format!("cnt_{cell}")));
                match cell.checked_sub(cells) {
                    None | Some(0) => f.memory_coords(addr, count, [lo, hi]),
                    Some(1) => f.memory_coords_if(out_two, addr, count, [lo, hi]),
                    Some(_) => f.memory_coords_if(out_all, addr, count, [lo, hi]),
                }
            }
        }
        opcode => unreachable!("no table {opcode}"),
    }
    f
}

/// What `q_keccak` holds for a global column, if anything.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum KeccakLane {
    /// A column whose words are `q_keccak`'s slot: an input lane, or a KECCAK column riding a spare slot.
    Slot(usize),
    /// Output lane `l`, whose claim is the Keccak reduction's claim on the output.
    Output(usize),
}

pub(crate) fn keccak_value(column: usize) -> Option<KeccakLane> {
    if let Some(slot) = spec::qkeccak_slot(column) {
        return Some(KeccakLane::Slot(slot));
    }
    let local = column.checked_sub(GLOBAL_COLUMN_BASES[OP_KECCAK])?;
    let lane = local.checked_sub(spec::KECCAK_OUT)?;
    (lane < keccak256::STATE_LANES).then_some(KeccakLane::Output(lane))
}

/// The global column count.
fn n_columns() -> usize {
    GLOBAL_COLUMN_BASES[N_TABLES - 1] + spec::TABLE_WIDTHS[N_TABLES - 1]
}

/// Per committed column, `Some((source, adj))` with kappa = value(source) + adj, source 0 the constant 0, 1 the memory's
/// log size and `2 + t` table `t`'s; `None` for a column nothing commits on its own.
pub(crate) fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let mut k = vec![Some((0, 0)); n_columns()];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    k[QKECCAK] = Some((2 + OP_KECCAK, slot_log()));
    for t in 0..N_TABLES {
        let base = GLOBAL_COLUMN_BASES[t];
        k[base..base + spec::TABLE_WIDTHS[t]].fill(Some((2 + t, 0)));
    }
    for (column, k) in k.iter_mut().enumerate() {
        if keccak_value(column).is_some() {
            *k = None;
        }
    }
    k
}

/// The bus blocks' kappa sources, in side order (push, pull, count), as [`bus_blocks`] builds them.
pub(crate) fn block_kappa_sources(log_bytecode: usize) -> Vec<(usize, usize)> {
    let framework = [(0, 0), (1, 0), (0, log_bytecode)];
    let (mut push, mut pull, mut count) = (framework.to_vec(), framework.to_vec(), Vec::new());
    for (t, table) in spec::tables().iter().enumerate() {
        let f = flushes(table);
        push.extend(std::iter::repeat_n((2 + t, 0), f.push.len()));
        pull.extend(std::iter::repeat_n((2 + t, 0), f.pull.len()));
        count.extend(std::iter::repeat_n((2 + t, 0), table.count_columns().count()));
    }
    [push, pull, count].concat()
}

/// Each table's log height: the least that holds its rows, at least its floor.
pub(crate) fn table_logs(rows: &[u64]) -> [usize; N_TABLES] {
    std::array::from_fn(|t| (rows[t].next_power_of_two().ilog2() as usize).max(spec::TABLE_LOG_FLOORS[t]))
}

/// The bus blocks of an execution of a `2^log_bytecode`-instruction program with `2^log_mem` cells of memory and tables
/// of `2^taus[t]` rows: push, pull, count.
pub(crate) fn bus_blocks(log_bytecode: usize, log_mem: usize, taus: &[usize; N_TABLES]) -> [Vec<Block>; 3] {
    let full = |kappa, coords| Block {
        kappa,
        coords,
        padding: Vec::new(),
    };
    let one = Const(K(1));
    // The run starts at `(pc, fp) = (1, 1)` and ends at the bytecode's last cell, the frame back at 1.
    let final_pc = g_pow((1 << log_bytecode) - 1);
    let (sep_state, sep_mem) = (Const(K(spec::SEP_STATE.c0)), Const(K(spec::SEP_MEM.c0)));
    let bytecode = |count: Coord| {
        let head = [Const(K(spec::SEP_BYTECODE.c0)), Coord::Index, count];
        let public = (0..=BYTECODE_OPERANDS).map(Coord::Public);
        full(log_bytecode, head.into_iter().chain(public).collect())
    };
    let mut push = vec![
        full(0, vec![sep_state.clone(), one.clone(), one.clone()]),
        full(
            log_mem,
            vec![sep_mem.clone(), Coord::Index, one.clone(), Col(MEM_LO), Col(MEM_HI)],
        ),
        bytecode(one.clone()),
    ];
    let mut pull = vec![
        full(0, vec![sep_state, Const(final_pc), one]),
        full(
            log_mem,
            vec![sep_mem, Coord::Index, Col(MFCNT), Col(MEM_LO), Col(MEM_HI)],
        ),
        bytecode(Col(BFCNT)),
    ];
    let mut count = Vec::new();
    for (t, table) in spec::tables().iter().enumerate() {
        let padding: Vec<K> = table.padding.iter().map(|word| K(word.c0)).collect();
        let block = |coords: &Vec<Coord>| Block {
            kappa: taus[t],
            padding: coords.iter().map(|c| coord_at(c, &padding)).collect(),
            coords: coords.iter().map(|c| offset_coord(GLOBAL_COLUMN_BASES[t], c)).collect(),
        };
        let f = flushes(table);
        push.extend(f.push.iter().map(block));
        pull.extend(f.pull.iter().map(block));
        count.extend(table.count_columns().map(|column| block(&vec![Col(column)])));
    }
    [push, pull, count]
}

/// Lay `2^kappa`-sized items end to end, largest first, ties by index, at aligned offsets: each item's offset (zero
/// for a `None`) and the total size.
pub(crate) fn stack_offsets(kappas: &[Option<usize>]) -> (Vec<usize>, usize) {
    let mut order: Vec<usize> = (0..kappas.len()).filter(|&i| kappas[i].is_some()).collect();
    order.sort_by_key(|&i| (std::cmp::Reverse(kappas[i]), i));
    let mut offsets = vec![0; kappas.len()];
    let mut at = 0;
    for i in order {
        offsets[i] = at;
        at += 1 << kappas[i].unwrap();
    }
    (offsets, at)
}

/// A bus side's stacking: each block's offset in its leaf vector, and the vector's log size.
pub(crate) fn side_stack(blocks: &[Block]) -> (Vec<usize>, usize) {
    let (offsets, placed) = stack_offsets(&blocks.iter().map(|b| Some(b.kappa)).collect::<Vec<_>>());
    (offsets, placed.max(1).next_power_of_two().ilog2() as usize)
}

/// Every column's offset in the committed stack, and the stack's log size, for the given sizes.
pub(crate) fn column_stack(log_bytecode: usize, log_mem: usize, taus: &[usize; N_TABLES]) -> (Vec<usize>, usize) {
    let values: Vec<usize> = [0, log_mem].into_iter().chain(taus.iter().copied()).collect();
    let kappas: Vec<Option<usize>> = col_kappa_sources(log_bytecode)
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect();
    let (offsets, placed) = stack_offsets(&kappas);
    let mu = (placed.max(1).next_power_of_two().ilog2() as usize).max(verifier::MIN_STACKED_LOG);
    (offsets, mu)
}

/// Each range's start in a run of ranges of these lengths.
pub(crate) fn xi_offsets(lengths: impl Iterator<Item = usize>) -> Vec<usize> {
    lengths
        .scan(0, |at, n| {
            let start = *at;
            *at += n;
            Some(start)
        })
        .collect()
}

/// Where the bus forms sit in the table sumcheck's `ξ`-powers: after every table's identities.
pub(crate) fn xi_form_base() -> usize {
    spec::tables().iter().map(|t| t.n_constraints()).sum()
}

/// The table sumcheck's `ξ`-powers: one per identity, then one per bus tree.
pub(crate) fn n_xi_powers() -> usize {
    xi_form_base() + verifier::N_BUS_TREES
}

/// The grind before the bus fingerprint, for a push side of `2^mu` leaves.
pub(crate) fn bus_grinding_bits(mu: usize) -> u32 {
    grinding_bits(1 << mu)
}

/// The grind of a bus GKR round, of degree `4 + 1`.
pub(crate) const ROUND_GRIND: u32 = grinding_bits(4 + 1);

/// The grind before a bus GKR layer's `y`, its `step` coordinates, the last layer's doubled.
pub(crate) fn y_grind(step: usize, last: bool) -> u32 {
    grinding_bits((step << usize::from(last)) as u128)
}

/// `g^n` in `K` by four byte tables.
struct GPow([[K; 256]; 4]);

impl GPow {
    fn new() -> Self {
        Self(std::array::from_fn(|byte| {
            let base = spec::gpow(1 << (8 * byte));
            let mut powers = [K(1); 256];
            for v in 1..256 {
                powers[v] = K((E::from(powers[v - 1]) * base).c0);
            }
            powers
        }))
    }

    fn at(&self, n: u32) -> K {
        let byte = |b: usize| (n >> (8 * b)) as usize & 255;
        (1..4)
            .filter(|&b| byte(b) != 0)
            .fold(self.0[0][byte(0)], |acc, b| acc * self.0[b][byte(b)])
    }
}

/// The stacked bytecode multilinear of a program: its thirteen public columns (the opcode, then the operand slots) at
/// their bus tuple slots, padded to sixteen. What a transcript's IV hashes and the deferred claims are about.
pub fn bytecode_table(prog: &[Op]) -> Vec<u64> {
    let g = |n: u32| g_pow(n as usize).0;
    let flag = u64::from;
    let row = |op: &Op| -> (usize, Vec<u64>) {
        match *op {
            Op::Xor { a, b, c } => (spec::OP_XOR, vec![g(a), g(b), g(c)]),
            Op::Mul { a, b, c } => (spec::OP_MUL, vec![g(a), g(b), g(c)]),
            Op::Set { o, k } => (spec::OP_SET, vec![g(o), k.c0, k.c1]),
            Op::Deref { o1, o2, o3, mode } => (
                spec::OP_DEREF,
                vec![g(o1), g(o2), g(o3), flag(mode.f_pc()), flag(mode.f_fp())],
            ),
            Op::Jump { oc, od, of } => (spec::OP_JUMP, vec![g(oc), g(od), g(of)]),
            Op::Keccak {
                m,
                tail,
                b8,
                cap,
                out,
                in_odd,
                out_odd,
                out_cells,
            } => {
                let (out_two, out_all) = out_cells.flags();
                let offsets = m.into_iter().chain([tail, b8, cap, out]).map(g);
                let flags = [in_odd, out_odd, out_two, out_all].map(flag);
                (OP_KECCAK, offsets.chain(flags).collect())
            }
        }
    };
    let kbc = prog.len().trailing_zeros() as usize;
    assert_eq!(prog.len(), 1 << kbc, "a bytecode is a power of two long");
    let mut table = vec![0; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (pc, op) in prog.iter().enumerate() {
        let (opcode, operands) = row(op);
        assert!(operands.len() <= BYTECODE_OPERANDS);
        let column = |i: usize| (BYTECODE_PUBLIC_SLOT + i) << kbc;
        table[column(0) + pc] = g_pow(opcode).0;
        for (i, value) in operands.into_iter().enumerate() {
            table[column(1 + i) + pc] = value;
        }
    }
    table
}

#[cfg(test)]
mod tests {
    //! The restated structure against the stable prover's own.
    use super::*;
    extern crate stable_leanvm_core as leanvm_core;

    fn coord(c: &leanvm_core::leaf::Coord) -> Coord {
        use leanvm_core::leaf::Coord as P;
        match c {
            P::Const(v) => Coord::Const(K(v.0)),
            P::Col(i) => Coord::Col(*i),
            P::GCol(i, k) => Coord::GCol(*i, *k),
            P::Prod(i, j, k) => Coord::Prod(*i, *j, *k),
            P::Index => Coord::Index,
            P::Public(_) => Coord::Public(usize::MAX),
            P::Sum(cs) => Coord::Sum(cs.iter().map(coord).collect()),
        }
    }

    fn program(kbc: usize) -> Vec<Op> {
        let mut prog = vec![Op::Xor { a: 3, b: 1, c: 260 }; 1 << kbc];
        prog[1] = Op::Set {
            o: 70_000,
            k: E::new(5, 9),
        };
        prog[2] = Op::Jump { oc: 1, od: 2, of: 3 };
        prog
    }

    #[test]
    fn bus_blocks_are_the_provers() {
        let (kbc, log_mem, rows) = (6, 11, [3usize, 1 << 10, 0, 7, 100, 513]);
        let prog = program(kbc);
        let theirs = leanvm_core::cpu::layout(&prog, log_mem, rows, Default::default());
        let rows64 = rows.map(|r| r as u64);
        let taus = table_logs(&rows64);
        assert_eq!(taus, theirs.taus);
        let ours = bus_blocks(kbc, log_mem, &taus);
        for (ours, theirs) in ours.iter().zip([&theirs.push, &theirs.pull, &theirs.count]) {
            assert_eq!(ours.len(), theirs.len());
            for (a, b) in ours.iter().zip(theirs) {
                assert_eq!(a.kappa, b.kappa);
                let public = |c: &Coord| match c {
                    Coord::Public(_) => Coord::Public(usize::MAX),
                    c => c.clone(),
                };
                assert_eq!(
                    a.coords.iter().map(public).collect::<Vec<_>>(),
                    b.coords.iter().map(coord).collect::<Vec<_>>()
                );
                assert_eq!(a.padding, b.padding.iter().map(|v| K(v.0)).collect::<Vec<_>>());
            }
        }
        assert_eq!(block_kappa_sources(kbc), leanvm_core::cpu::block_kappa_sources(kbc));
        assert_eq!(col_kappa_sources(kbc), leanvm_core::cpu::col_kappa_sources(kbc));
        let (offsets, mu) = column_stack(kbc, log_mem, &taus);
        assert_eq!(mu, theirs.shape.mu);
        for (column, placement) in theirs.placements.iter().enumerate() {
            if col_kappa_sources(kbc)[column].is_some() {
                assert_eq!(offsets[column], placement.offset);
            }
        }
        for (blocks, side) in ours.iter().zip([&theirs.push, &theirs.pull, &theirs.count]) {
            let theirs = leanvm_core::leaf::layout(side);
            assert_eq!(side_stack(blocks), (theirs.offsets, theirs.mu));
        }
        for column in 0..n_columns() {
            let theirs = leanvm_core::cpu::keccak_value(column).map(|lane| match lane {
                leanvm_core::cpu::KeccakLane::Slot(s) => KeccakLane::Slot(s),
                leanvm_core::cpu::KeccakLane::Output(l) => KeccakLane::Output(l),
            });
            assert_eq!(keccak_value(column), theirs);
        }
        assert_eq!(n_columns(), leanvm_core::cpu::schema().n);
        let ours: Vec<u64> = bytecode_table(&prog);
        let theirs: Vec<u64> = leanvm_core::cpu::layout::bytecode_table(&prog)
            .iter()
            .map(|w| w.0)
            .collect();
        assert_eq!(ours, theirs);
    }

    #[test]
    fn constants_are_the_provers() {
        use leanvm_core::{cpu, gkr, keccak, leaf, tables};
        assert_eq!(xi_form_base(), cpu::xi_form_base());
        assert_eq!(n_xi_powers(), cpu::n_xi_powers());
        assert_eq!(
            (N_TUPLE_BITS, N_BYTECODE_SELECTORS),
            (leaf::N_TUPLE_BITS, leaf::N_BYTECODE_SELECTORS)
        );
        assert_eq!(verifier::N_BUS_TREES, leaf::N_BUS_TREES);
        assert_eq!(ROUND_GRIND, gkr::ROUND_GRIND);
        for mu in 0..40 {
            assert_eq!(bus_grinding_bits(mu), leaf::bus_grinding_bits(mu));
            assert_eq!(
                [y_grind(mu, false), y_grind(mu, true)],
                [gkr::y_grind(mu, false), gkr::y_grind(mu, true)]
            );
        }
        assert_eq!((KECCAK_DEPTH, slot_log()), (keccak::DEPTH, keccak::SLOT_LOG));
        assert_eq!(1 << spec::KECCAK_MIN_STEPS_LOG, keccak::MIN_STEPS);
        assert_eq!(spec::TABLE_LOG_FLOORS, tables::TABLE_LOG_FLOORS);
        assert_eq!(MEM_LO, cpu::MEM_LO);
        assert_eq!((MEM_HI, QKECCAK), (cpu::MEM_HI, cpu::QKECCAK));
    }
}
