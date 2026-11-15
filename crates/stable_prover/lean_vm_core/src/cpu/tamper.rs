//! A malicious prover, for the fuzzer: an edit to the witness after the honest run built it and before
//! anything is committed. The prover then proves the edited witness as if it were honest, so a proof
//! that verifies is a witness the constraints and the bus do not pin. The transcript's own forgeries are
//! [`fiat_shamir::tamper`], re-exported here.

use super::layout::{KeccakLane, Witness, keccak_value};
use super::{Layout, MEMORY_0, MEMORY_1, MEMORY_FINAL_COUNTERS, BYTECODE_FINAL_COUNTERS, QKECCAK, Stats};
use crate::leaf::Coord;
use crate::tables::{self, FlushBuilder};
use primitives::field::{F64, F128};
use std::cell::RefCell;
use std::collections::HashMap;
use verifier::layout::{GLOBAL_COLUMN_BASES, TABLE_WIDTHS};

pub use fiat_shamir::tamper as transcript;

/// The shared column of each memory cell's final access count, `g^{A[i]}`.
pub const MFCNT: usize = MEMORY_FINAL_COUNTERS;
/// The shared column of each pc's final execution count.
pub const BFCNT: usize = BYTECODE_FINAL_COUNTERS;

/// The witness as the edit sees it: the public layout, every column's words, and the stacked bytecode the
/// boundary tuples read.
pub struct WitnessView<'a> {
    pub layout: &'a Layout,
    /// `log2` of the memory the run announced.
    pub log_mem: usize,
    /// The public input, the statement: `check` reads it.
    public_input: [F128; 2],
    stacked: &'a [u64],
    q: &'a mut [F64],
    virt: &'a mut [(usize, Vec<F64>)],
}

/// Where a global column lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Owner {
    /// A shared column: the memory limbs, the access counts, `q_keccak`.
    Shared,
    /// Column `local` of table `table` ([`Stats::TABLES`] order).
    Table { table: usize, local: usize },
}

impl WitnessView<'_> {
    /// Global columns, committed or virtual.
    pub fn n_columns(&self) -> usize {
        GLOBAL_COLUMN_BASES[tables::N_TABLES - 1] + TABLE_WIDTHS[tables::N_TABLES - 1]
    }

    pub fn owner(&self, column: usize) -> Owner {
        let base = GLOBAL_COLUMN_BASES;
        match (0..tables::N_TABLES).rev().find(|&t| column >= base[t]) {
            Some(table) => Owner::Table { table, local: column - base[table] },
            None => Owner::Shared,
        }
    }

    /// A readable name: `MEMORY_0`, `XOR.5`, ... with what kind of storage backs it.
    pub fn name(&self, column: usize) -> String {
        let storage = match keccak_value(column) {
            Some(KeccakLane::Slot(slot)) => format!(" (q_keccak slot {slot})"),
            Some(KeccakLane::Output(lane)) => format!(" (virtual output lane {lane})"),
            None => String::new(),
        };
        let name = match (column, self.owner(column)) {
            (MEMORY_0, _) => "MEMORY_0".into(),
            (MEMORY_1, _) => "MEMORY_1".into(),
            (MFCNT, _) => "MFCNT".into(),
            (BFCNT, _) => "BFCNT".into(),
            (QKECCAK, _) => "QKECCAK".into(),
            (_, Owner::Table { table, local }) => format!("{}.{local}", Stats::TABLES[table]),
            (c, Owner::Shared) => format!("shared.{c}"),
        };
        name + &storage
    }

    /// Rows the program really executed in a table's column, the rest being padding. `None` for a shared column.
    pub fn real_rows(&self, column: usize) -> Option<usize> {
        match self.owner(column) {
            Owner::Table { table, .. } => Some(self.layout.rows[table]),
            Owner::Shared => None,
        }
    }

    /// The words of global `column`, wherever they are kept: its window of the stack, its `q_keccak`
    /// slot, or its private buffer.
    pub fn column_mut(&mut self, column: usize) -> &mut [F64] {
        if let Some(i) = self.virt.iter().position(|(c, _)| *c == column) {
            return &mut self.virt[i].1;
        }
        let placements = &self.layout.placements;
        match keccak_value(column) {
            Some(KeccakLane::Slot(slot)) => {
                let steps = 1 << self.layout.taus[verifier::layout::OP_KECCAK];
                let offset = placements[QKECCAK].offset;
                &mut self.q[offset + slot * steps..][..steps]
            }
            _ if placements[column].n_vars == usize::MAX => &mut [],
            _ => {
                let p = placements[column];
                &mut self.q[p.offset..][..1 << p.n_vars]
            }
        }
    }

    /// The whole committed stack, gaps between placements included.
    pub fn stack_mut(&mut self) -> &mut [F64] {
        self.q
    }

    /// [`Self::column_mut`], read only.
    pub fn column(&self, column: usize) -> &[F64] {
        if let Some((_, buf)) = self.virt.iter().find(|(c, _)| *c == column) {
            return buf;
        }
        let placements = &self.layout.placements;
        match keccak_value(column) {
            Some(KeccakLane::Slot(slot)) => {
                let steps = 1 << self.layout.taus[verifier::layout::OP_KECCAK];
                let offset = placements[QKECCAK].offset;
                &self.q[offset + slot * steps..][..steps]
            }
            _ if placements[column].n_vars == usize::MAX => &[],
            _ => {
                let p = placements[column];
                &self.q[p.offset..][..1 << p.n_vars]
            }
        }
    }

    /// Words of the stack the placed columns cover; the rest, up to its end, is the zero pad of the last lane.
    pub fn placed_len(&self) -> usize {
        self.layout.placements.iter().filter(|p| p.n_vars != usize::MAX).map(|p| 1usize << p.n_vars).sum()
    }

    /// `q_keccak`'s committed states, every slot of them: the input lanes, then the state after each
    /// [`crate::keccak::DEPTH`] rounds.
    pub fn keccak_states_mut(&mut self) -> &mut [F64] {
        let steps = 1 << self.layout.taus[verifier::layout::OP_KECCAK];
        let offset = self.layout.placements[QKECCAK].offset;
        let slots = crate::keccak::MIN_SHAPE.slots();
        &mut self.q[offset..][..slots * steps]
    }

    fn columns(&self) -> Vec<&[F64]> {
        (0..self.n_columns()).map(|c| self.column(c)).collect()
    }

    /// The instructions' words of the stacked bytecode, the boundary tuples' [`Coord::Public`] source.
    fn instructions(&self) -> Vec<&[u64]> {
        let per = self.stacked.len() >> verifier::layout::BUS_BITS;
        self.stacked.chunks_exact(per).collect()
    }

    /// Every memory access a table's real row makes, read off its pull flushes: a pair that cancels (a
    /// `KECCAK` output cell its row does not write) is left out. `block` is the pull side's index, its owner
    /// in [`block_owners`]'s order.
    pub fn accesses(&self) -> Vec<Access> {
        let cols = self.columns();
        let cells: HashMap<u64, usize> =
            primitives::field::g_powers(1 << self.log_mem).into_iter().enumerate().map(|(i, g)| (g.0, i)).collect();
        let owners = block_owners();
        let mut out = Vec::new();
        for (k, block) in self.layout.pull.iter().enumerate() {
            if !matches!(block.coords.first(), Some(Coord::Const(sep)) if sep.0 == tables::SEP_MEM.0) {
                continue;
            }
            let public = self.instructions();
            let gpow: Vec<F64> = (0..block.rows).map(|z| primitives::field::g_pow(z)).collect();
            for row in 0..block.rows {
                let at = |c: &Coord| eval(&cols, &public, c, row, &gpow);
                let tuple = |b: &crate::leaf::Block| b.coords.iter().map(|c| at(c)).collect::<Vec<_>>();
                if tuple(&self.layout.push[k]) == tuple(block) {
                    continue;
                }
                let addr = at(&block.coords[1]);
                let col = |c: &Coord| match c {
                    Coord::Col(i) => Some(*i),
                    Coord::Sum(cs) => cs.iter().find_map(|c| match c {
                        Coord::Col(i) => Some(*i),
                        _ => None,
                    }),
                    _ => None,
                };
                out.push(Access {
                    block: k,
                    owner: owners[&k],
                    row,
                    addr,
                    cell: cells.get(&addr.0).copied(),
                    count: col(&block.coords[2]),
                    values: [col(&block.coords[3]), col(&block.coords[4])],
                });
            }
        }
        out
    }

    /// The relation the protocol is meant to enforce, checked directly on the witness: the bus balances as a
    /// multiset, every read count is nonzero, every padding row flushes its table's padding tuple, the tables'
    /// identities hold on every row, memory opens with the public input, and `q_keccak`'s states and the output
    /// lanes follow Keccak-f. `Err` names the first part that fails.
    ///
    /// A witness this accepts but the program could not have produced is a hole in the arithmetization; one it
    /// refuses but a verifier accepts is a hole in the protocol.
    pub fn check(&self) -> Result<(), String> {
        let public_input = self.public_input;
        let cols = self.columns();
        let public = self.instructions();
        // Memory opens with the public input: cells 0 and 1 are its two halves' limbs.
        for (i, half) in public_input.iter().enumerate() {
            let [lo, hi] = half.to_limbs();
            if cols[MEMORY_0][i] != F64(lo) || cols[MEMORY_1][i] != F64(hi) {
                return Err("public input".into());
            }
        }
        // The bus balances as a multiset of full tuples, trailing zeros trimmed.
        let mut balance: HashMap<Vec<u64>, isize> = HashMap::new();
        for (blocks, sign) in [(&self.layout.push, 1isize), (&self.layout.pull, -1)] {
            for block in blocks {
                for row in 0..block.rows {
                    let gpow: Vec<F64> = (0..block.rows).map(|z| primitives::field::g_pow(z)).collect();
                    let mut tuple: Vec<u64> =
                        block.coords.iter().map(|c| eval(&cols, &public, c, row, &gpow).0).collect();
                    while tuple.last() == Some(&0) {
                        tuple.pop();
                    }
                    *balance.entry(tuple).or_default() += sign;
                }
            }
        }
        if balance.values().any(|&n| n != 0) {
            return Err("bus".into());
        }
        // Every read count is nonzero.
        for block in &self.layout.count {
            for row in 0..block.rows {
                let gpow: Vec<F64> = (0..block.rows).map(|z| primitives::field::g_pow(z)).collect();
                if eval(&cols, &public, &block.coords[0], row, &gpow) == F64::ZERO {
                    return Err("read count zero".into());
                }
            }
        }
        // Padding rows flush their table's padding tuple.
        let owners = block_owners();
        for blocks in [&self.layout.push, &self.layout.pull] {
            for (k, block) in blocks.iter().enumerate() {
                for row in block.rows..1 << block.kappa {
                    let gpow: Vec<F64> = (0..(1usize << block.kappa)).map(|z| primitives::field::g_pow(z)).collect();
                    let tuple: Vec<F64> =
                        block.coords.iter().map(|c| eval(&cols, &public, c, row, &gpow)).collect();
                    if tuple != block.padding {
                        return Err(format!(
                            "padding row of {}'s block {k}",
                            Stats::TABLES[owners[&k]]
                        ));
                    }
                }
            }
        }
        // The tables' identities hold on every row of the full cube.
        for (t, table) in tables::tables().iter().enumerate() {
            let base = GLOBAL_COLUMN_BASES[t];
            let n = table.n_committed_columns();
            for identity in 0..table.n_constraints() {
                let mut pows = vec![F128::ZERO; table.n_constraints()];
                pows[identity] = F128::ONE;
                let form = table.constraint(&pows);
                for row in 0..1 << self.layout.taus[t] {
                    let evals: Vec<F128> = (0..n).map(|c| F128::new(cols[base + c][row].0, 0)).collect();
                    let linear = form.coeffs.iter().zip(&evals).fold(form.constant, |acc, (&w, &v)| acc + w * v);
                    let value = form.prods.iter().fold(linear, |acc, &(a, b, q)| acc + evals[a] * evals[b] * q);
                    if value != F128::ZERO {
                        return Err(format!("{} identity {identity}", Stats::TABLES[t]));
                    }
                }
            }
        }
        self.check_keccak()
    }

    fn check_keccak(&self) -> Result<(), String> {
        use primitives::hash::STATE_LANES;
        let steps = 1 << self.layout.taus[verifier::layout::OP_KECCAK];
        let offset = self.layout.placements[QKECCAK].offset;
        let slots = crate::keccak::MIN_SHAPE.slots();
        let states = &self.q[offset..][..slots * steps];
        let inputs: Vec<[u64; STATE_LANES]> =
            (0..steps).map(|j| std::array::from_fn(|l| states[l * steps + j].0)).collect();
        // The committed middle states follow Keccak-f from the committed inputs.
        let mut expected = vec![F64::ZERO; states.len()];
        crate::keccak::place(&inputs, &mut expected);
        if expected[..] != states[..] {
            return Err("keccak committed state".into());
        }
        // The virtual output lanes are the permutation of the inputs.
        for (column, words) in self.virt.iter() {
            if let Some(KeccakLane::Output(lane)) = keccak_value(*column) {
                for (j, input) in inputs.iter().enumerate() {
                    let mut output = *input;
                    primitives::hash::keccak_f(&mut output);
                    if words[j].0 != output[lane] {
                        return Err("keccak output lane".into());
                    }
                }
            }
        }
        Ok(())
    }
}

/// One memory access a table's real row makes.
#[derive(Clone, Debug)]
pub struct Access {
    /// The pull side's block index.
    pub block: usize,
    /// The table that owns it, in [`Stats::TABLES`] order.
    pub owner: usize,
    pub row: usize,
    /// The cell's address, a g-power.
    pub addr: F64,
    /// The memory cell it names, `None` past the memory.
    pub cell: Option<usize>,
    /// The global column holding the read count, when it is one.
    pub count: Option<usize>,
    /// The global columns carrying the word's two limbs, each `None` where the flush derives the limb or
    /// carries a constant.
    pub values: [Option<usize>; 2],
}

/// Each table's flush's index in `Layout::push` (and `pull`, which pairs with it), and the table that owns it.
fn block_owners() -> HashMap<usize, usize> {
    let mut owners = HashMap::new();
    let mut k = 0;
    for (t, table) in tables::tables().iter().enumerate() {
        let mut builder = FlushBuilder::new();
        table.flushes(&mut builder);
        for _ in 0..builder.push.len() {
            owners.insert(k, t);
            k += 1;
        }
    }
    owners
}

/// A flush coordinate at `row`, over global columns. `gpow` holds `g^z` for the index coordinate;
/// `public` the instructions' words, the boundary tuples' [`Coord::Public`] source.
fn eval(cols: &[&[F64]], public: &[&[u64]], c: &Coord, row: usize, gpow: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => cols[*i][row],
        Coord::GCol(i, k) => primitives::field::g_pow(*k as usize) * cols[*i][row],
        Coord::Prod(i, j, k) => primitives::field::g_pow(*k as usize) * cols[*i][row] * cols[*j][row],
        Coord::Sum(cs) => cs.iter().map(|c| eval(cols, public, c, row, gpow)).sum(),
        Coord::Index => gpow.get(row).copied().unwrap_or_else(|| primitives::field::g_pow(row)),
        Coord::Public(slot) => F64(public.get(row).map(|words| words[*slot]).unwrap_or(0)),
    }
}

/// An edit to the next witness this thread proves.
pub type WitnessTamper = Box<dyn FnOnce(&mut WitnessView)>;

thread_local! {
    static ARMED: RefCell<Option<WitnessTamper>> = const { RefCell::new(None) };
    static TAMPERED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the latest [`super::prove`] on this thread handed its witness to an armed edit. A prover-side
/// assertion that the witness is consistent (the bus's two roots agree, a side decomposes into its leaf
/// value) is a completeness check the malicious prover has to get past to reach the verifier; gating it
/// on `!tampered()` under this feature lets it.
pub fn tampered() -> bool {
    TAMPERED.with(|t| t.get())
}

/// The next [`super::prove`] on this thread edits its witness with `tamper` before committing it.
pub fn arm(tamper: WitnessTamper) {
    ARMED.with(|armed| *armed.borrow_mut() = Some(tamper));
}

/// Drop an edit no prover took.
pub fn disarm() {
    ARMED.with(|armed| armed.borrow_mut().take());
}

pub(super) fn apply(w: &mut Witness, stacked: &[u64], public_input: &[F128; 2]) {
    let tamper = ARMED.with(|armed| armed.borrow_mut().take());
    TAMPERED.with(|t| t.set(tamper.is_some()));
    if let Some(tamper) = tamper {
        let Witness { q, virt, layout, .. } = w;
        tamper(&mut WitnessView {
            layout,
            log_mem: layout.placements[MEMORY_0].n_vars,
            public_input: *public_input,
            stacked,
            q,
            virt,
        });
    }
}