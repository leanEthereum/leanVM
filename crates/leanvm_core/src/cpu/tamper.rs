//! A malicious prover, for the fuzzer: an edit to the witness after the honest run built it and before
//! anything is committed. The prover then proves the edited witness as if it were honest, so a proof
//! that verifies is a witness the constraints and the bus do not pin. The transcript's own forgeries are
//! [`fiat_shamir::tamper`], re-exported here.

use super::layout::{KeccakLane, Witness, keccak_value, schema};
use super::{Layout, MEM_HI, MEM_LO, QKECCAK, Stats};
use crate::leaf::{Block, Coord};
use crate::tables;
use primitives::field::{F64, F128};
use std::cell::RefCell;
use std::collections::HashMap;

pub use fiat_shamir::tamper as transcript;

/// The shared column of each memory cell's final access count, `g^{A[i]}`.
pub const MFCNT: usize = super::MFCNT;
/// The shared column of each pc's final execution count.
pub const BFCNT: usize = super::BFCNT;

/// The witness as the edit sees it: the public layout, and every column's words.
pub struct WitnessView<'a> {
    pub layout: &'a Layout,
    pub log_mem: usize,
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
        self.layout.placements.len()
    }

    pub fn owner(&self, column: usize) -> Owner {
        let base = &schema().base;
        match (0..tables::N_TABLES).rev().find(|&t| column >= base[t]) {
            Some(table) => Owner::Table {
                table,
                local: column - base[table],
            },
            None => Owner::Shared,
        }
    }

    /// A readable name: `MEM_LO`, `XOR.5`, ... with what kind of storage backs it.
    pub fn name(&self, column: usize) -> String {
        let storage = match keccak_value(column) {
            Some(KeccakLane::Slot(slot)) => format!(" (q_keccak slot {slot})"),
            Some(KeccakLane::Output(lane)) => format!(" (virtual output lane {lane})"),
            None => String::new(),
        };
        let name = match (column, self.owner(column)) {
            (MEM_LO, _) => "MEM_LO".into(),
            (MEM_HI, _) => "MEM_HI".into(),
            (super::MFCNT, _) => "MFCNT".into(),
            (super::BFCNT, _) => "BFCNT".into(),
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
                let steps = 1 << self.layout.taus[tables::KECCAK_TABLE];
                &mut self.q[placements[QKECCAK].offset + slot * steps..][..steps]
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
                let steps = 1 << self.layout.taus[tables::KECCAK_TABLE];
                &self.q[placements[QKECCAK].offset + slot * steps..][..steps]
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
        self.layout
            .placements
            .iter()
            .filter(|p| !p.is_virtual())
            .map(|p| 1usize << p.n_vars)
            .sum()
    }

    /// `q_keccak`'s committed states, every slot of them: the input lanes, then the state after each
    /// [`crate::keccak::DEPTH`] rounds.
    pub fn keccak_states_mut(&mut self) -> &mut [F64] {
        let steps = 1 << self.layout.taus[tables::KECCAK_TABLE];
        let offset = self.layout.placements[QKECCAK].offset;
        &mut self.q[offset..][..crate::keccak::SLOTS * steps]
    }

    fn columns(&self) -> Vec<&[F64]> {
        (0..self.n_columns()).map(|c| self.column(c)).collect()
    }

    /// Every memory access a table's real row makes, read off its pull flushes: a pair that cancels (a
    /// `KECCAK` output cell its row does not write) is left out.
    pub fn accesses(&self) -> Vec<Access> {
        let cols = self.columns();
        let cells: HashMap<u64, usize> = primitives::field::g_powers(1 << self.log_mem)
            .into_iter()
            .enumerate()
            .map(|(i, g)| (g.0, i))
            .collect();
        let mut out = Vec::new();
        for (k, table) in block_owners() {
            let (push, pull) = (&self.layout.push[k], &self.layout.pull[k]);
            if !matches!(pull.coords[0], Coord::Const(sep) if sep == tables::SEP_MEM) {
                continue;
            }
            for row in 0..pull.rows {
                let tuple = |b: &Block| b.coords.iter().map(|c| eval(&cols, c, row, &[])).collect::<Vec<_>>();
                if tuple(push) == tuple(pull) {
                    continue;
                }
                let addr = eval(&cols, &pull.coords[1], row, &[]);
                let col = |c: &Coord| match c {
                    Coord::Col(i) => Some(*i),
                    _ => None,
                };
                out.push(Access {
                    table,
                    row,
                    addr,
                    cell: cells.get(&addr.0).copied(),
                    count: col(&pull.coords[2]),
                    values: [col(&pull.coords[3]), col(&pull.coords[4])],
                });
            }
        }
        out
    }

    /// The relation the protocol is meant to enforce, checked directly on the witness: the bus balances
    /// as a multiset, every read count is nonzero, every padding row flushes its table's padding tuple,
    /// the tables' identities hold on every row, memory opens with the public input, and `q_keccak`'s
    /// states and the output lanes follow Keccak-f. `Err` names the first part that fails.
    ///
    /// A witness this accepts but the program could not have produced is a hole in the arithmetization;
    /// one it refuses but a verifier accepts is a hole in the protocol.
    pub fn check(&self) -> Result<(), String> {
        let l = self.layout;
        let cols = self.columns();
        let longest = l
            .push
            .iter()
            .chain(&l.pull)
            .map(|b| 1usize << b.kappa)
            .max()
            .unwrap_or(1);
        let gpow = primitives::field::g_powers(longest);
        for (i, half) in l.pi.iter().enumerate() {
            let limbs = [cols[MEM_LO][i], cols[MEM_HI][i]];
            if limbs != half.to_limbs().map(F64) {
                return Err("public input".into());
            }
        }
        let mut balance: HashMap<Vec<u64>, i64> = HashMap::new();
        for (blocks, sign) in [(&l.push, 1), (&l.pull, -1)] {
            for block in blocks {
                for row in 0..block.rows {
                    let mut tuple: Vec<u64> = block.coords.iter().map(|c| eval(&cols, c, row, &gpow).0).collect();
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
        for block in &l.count {
            if (0..block.rows).any(|row| eval(&cols, &block.coords[0], row, &gpow) == F64::ZERO) {
                return Err("read count zero".into());
            }
        }
        let owners: HashMap<usize, usize> = block_owners().collect();
        let count_owner = count_owners();
        let sides = [(&l.push, &owners), (&l.pull, &owners), (&l.count, &count_owner)];
        for (blocks, owner) in sides {
            for (k, block) in blocks.iter().enumerate() {
                for row in block.rows..1 << block.kappa {
                    let tuple: Vec<F64> = block.coords.iter().map(|c| eval(&cols, c, row, &gpow)).collect();
                    if tuple != block.padding {
                        return Err(format!("padding row of {}", Stats::TABLES[owner[&k]]));
                    }
                }
            }
        }
        for (t, table) in tables::tables().iter().enumerate() {
            let (base, n) = (schema().base[t], table.n_committed_columns());
            for identity in 0..table.n_constraints() {
                let mut pows = vec![F128::ZERO; table.n_constraints()];
                pows[identity] = F128::ONE;
                let form = table.constraint(&pows);
                let at = |c: usize, row: usize| F128::new(cols[base + c][row].0, 0);
                for row in 0..1 << l.taus[t] {
                    let linear = (0..n).fold(form.constant, |acc, c| acc + form.coeffs[c] * at(c, row));
                    let value = form
                        .prods
                        .iter()
                        .fold(linear, |acc, &(a, b, w)| acc + w * at(a, row) * at(b, row));
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
        let steps = 1 << self.layout.taus[tables::KECCAK_TABLE];
        let offset = self.layout.placements[QKECCAK].offset;
        let states = &self.q[offset..][..crate::keccak::SLOTS * steps];
        let inputs: Vec<[u64; STATE_LANES]> = (0..steps)
            .map(|j| std::array::from_fn(|l| states[l * steps + j].0))
            .collect();
        let mut expected = vec![F64::ZERO; states.len()];
        let shape = keccak_gkr::Shape::new(steps, crate::keccak::DEPTH);
        drop(keccak_gkr::Witness::generate(shape, &inputs, &mut expected));
        if expected[..] != states[..] {
            return Err("keccak committed state".into());
        }
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

/// One memory access of a table's real row.
#[derive(Clone, Debug)]
pub struct Access {
    /// [`Stats::TABLES`] order.
    pub table: usize,
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

/// Each table flush's index in `Layout::push` (and `pull`, which pairs with it), and the table that owns it.
fn block_owners() -> impl Iterator<Item = (usize, usize)> {
    let mut k = 3; // the boundary state, memory and bytecode blocks lead both sides
    let mut owners = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let mut fb = tables::FlushBuilder::new();
        table.flushes(&mut fb);
        for _ in 0..fb.push.len() {
            owners.push((k, t));
            k += 1;
        }
    }
    owners.into_iter()
}

fn count_owners() -> HashMap<usize, usize> {
    let mut k = 0;
    let mut owners = HashMap::new();
    for (t, table) in tables::tables().iter().enumerate() {
        for _ in table.count_columns() {
            owners.insert(k, t);
            k += 1;
        }
    }
    owners
}

/// A flush coordinate at `row`, over global columns. `gpow` holds `g^z` for the index coordinate.
fn eval(cols: &[&[F64]], c: &Coord, row: usize, gpow: &[F64]) -> F64 {
    match c {
        Coord::Const(v) => *v,
        Coord::Col(i) => cols[*i][row],
        Coord::GCol(i, k) => primitives::field::g_pow(*k as usize) * cols[*i][row],
        Coord::Prod(i, j, k) => primitives::field::g_pow(*k as usize) * cols[*i][row] * cols[*j][row],
        Coord::Sum(cs) => cs.iter().map(|c| eval(cols, c, row, gpow)).sum(),
        Coord::Index => gpow.get(row).copied().unwrap_or_else(|| primitives::field::g_pow(row)),
        Coord::Public(column) => column[row],
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

pub(super) fn apply(w: &mut Witness) {
    let tamper = ARMED.with(|armed| armed.borrow_mut().take());
    TAMPERED.with(|t| t.set(tamper.is_some()));
    if let Some(tamper) = tamper {
        let Witness {
            q,
            virt,
            layout,
            log_mem,
            ..
        } = w;
        tamper(&mut WitnessView {
            layout,
            log_mem: *log_mem,
            q,
            virt,
        });
    }
}

/// Replace `program`'s bytecode and keep everything [`super::Program::assemble`] derived from the old one: the Fiat-Shamir
/// IV and the public bytecode columns. A malicious prover is not bound to the honest `Program`, so this is how it
/// executes one bytecode under another's transcript, which every verifier must reject.
pub fn replace_bytecode(program: &mut super::Program, prog: Vec<super::Op>) {
    program.prog = prog;
}
