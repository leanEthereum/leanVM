//! What a run of the program on the reference interpreter records for the memory argument.
//!
//! A row carries what its accesses saw, its clock, and per access the timestamp its cell was last accessed at.
//!
//! Everything else comes back from the program's entry at the row's index.

use crate::rv::machine::{MemoryAccess, Step};
use crate::rv::{BlockAccess, Class, Ext, Hash, Limb, Machine, RegisterFile, RiscvProgram, WordAccess};
use crate::tables;
use crate::tables::{ClassSpec, ClassTable, Clock, N_TABLES};
use primitives::field::F64;

/// A finished run: its output, its rows, and what it left behind.
pub struct Execution {
    /// The public output: `a0` to `a3` as the run left them.
    pub output: [u64; 4],
    /// The rows proven, padding rows included.
    pub cycles: usize,
    /// The rows per table before the padding rows: the work the program itself does.
    ///
    /// Cost measurements want these, not the power-of-two heights that get proven.
    pub base_counts: [usize; N_TABLES],
    /// The rows and the final state, emitted in the same walk as the run.
    pub(crate) trace: Trace,
}

// Why: every row commits at least one word, so a run one commitment holds is far below the cycles the clock counts.
const _: () = assert!(1u64 << crate::pcs::MAX_MU < Clock::MAX_CYCLES);

/// Each cell's last timestamp in one read-write array (§sec:memchan).
struct LastAccess(Vec<u64>);

impl LastAccess {
    /// `n` cells, each last accessed at the seed's timestamp.
    fn new(n: usize) -> Self {
        Self(vec![Clock::SEED_CLOCK; n])
    }

    /// Access `cell` at timestamp `at`, and return the timestamp of its previous access.
    #[inline(always)]
    fn access(&mut self, cell: usize, at: u64) -> u64 {
        std::mem::replace(&mut self.0[cell], at)
    }

    /// Every cell's last timestamp, as field words.
    fn timestamps(&self) -> Vec<F64> {
        self.0.iter().map(|&t| F64(t)).collect()
    }
}

/// What a run keeps of each step it makes.
pub(super) trait Recorder {
    /// Record the row of `step`, executed at clock `ts`.
    fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64);

    /// The rows recorded so far, per table.
    fn row_counts(&self) -> [usize; N_TABLES];
}

/// The rows a run makes per table, and nothing else.
pub(super) struct RowCounter {
    /// The table of each bytecode entry, or none for a class with no table.
    tables: Vec<Option<usize>>,
    /// The rows counted so far, per table.
    counts: [usize; N_TABLES],
}

impl RowCounter {
    /// A counter for runs of `p`.
    pub(super) fn new(p: &RiscvProgram) -> Self {
        Self {
            tables: p.entries().iter().map(|e| ClassTable::index_of(e.class)).collect(),
            counts: [0; N_TABLES],
        }
    }
}

impl Recorder for RowCounter {
    #[inline(always)]
    fn record(&mut self, _: &RiscvProgram, _: &Machine<'_>, step: Step, _: u64) {
        let table = self.tables[step.index].expect("every class that runs has a table");
        self.counts[table] += 1;
    }

    fn row_counts(&self) -> [usize; N_TABLES] {
        self.counts
    }
}

/// A trace being recorded: the rows so far, and each cell's last access timestamp.
pub(super) struct TraceBuilder {
    /// The register file's cells.
    regs: LastAccess,
    /// RAM's cells, then the advice's, as the machine numbers them.
    ram: LastAccess,
    /// Each table's rows.
    rows: [Vec<Row>; N_TABLES],
    /// The hash table's payloads, one per row.
    hash: Vec<HashRow>,
    /// The extension-field table's payloads, one per row.
    ext: Vec<ExtRow>,
    /// Each table's access slots, which a padding row's accesses pull as their previous timestamps.
    padding_prev: [Vec<u64>; N_TABLES],
    /// The advice before the run, which is committed.
    adv_init: Vec<F64>,
}

impl Recorder for TraceBuilder {
    #[inline(always)]
    fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64) {
        self.record_row(p, m, step, ts);
    }

    fn row_counts(&self) -> [usize; N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }
}

impl TraceBuilder {
    /// The trace of a run of `p` about to start on this advice region.
    pub(super) fn new(p: &RiscvProgram, advice: &[u64]) -> Self {
        Self {
            regs: LastAccess::new(RegisterFile::CELLS),
            ram: LastAccess::new((1 << p.log_ram()) + (1 << p.log_advice())),
            rows: std::array::from_fn(|_| Vec::new()),
            hash: Vec::new(),
            ext: Vec::new(),
            padding_prev: std::array::from_fn(|t| ClassSpec::ALL[t].slots().into_iter().map(u64::from).collect()),
            adv_init: advice.iter().map(|&w| F64(w)).collect(),
        }
    }

    /// Record the row of `step`, executed at clock `ts`.
    #[inline(always)]
    fn record_row(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64) {
        let e = &p.entries()[step.index];
        let table = ClassTable::index_of(e.class).expect("every class that runs has a table");
        let spec = ClassSpec::ALL[table];

        // The register accesses the class makes, in column order, each at its slot of the row's clock.
        let cells = [e.a1, e.a2, e.ad].map(|cell| cell as usize);
        let made = [true, spec.reads_rs2, spec.writes_rd || spec.reads_rd];
        let mut prev = [0; 4];
        let mut n = 0;
        for (i, slot) in Clock::REG_SLOTS.into_iter().enumerate() {
            if made[i] {
                prev[n] = self.regs.access(cells[i], ts | u64::from(slot));
                n += 1;
            }
        }

        // The memory access, after the register accesses; the machine made it, so each address names a cell.
        let cell_of = |address: u64| m.memory().cell(address).expect("an access the machine made");
        let mut word = WordAccess::default();
        match step.memory {
            MemoryAccess::None => {}
            MemoryAccess::Word(access) => {
                prev[n] = self
                    .ram
                    .access(cell_of(access.address), ts | u64::from(Clock::RAM_SLOT));
                word = access;
            }
            // A hash row's block, word `k` at `v1 ^ 8k`.
            MemoryAccess::Block(h) => {
                let mut all = [0; 2 + Hash::WORDS];
                all[..n].copy_from_slice(&prev[..n]);
                for k in 0..Hash::WORDS {
                    let cell = cell_of(step.v1 ^ (8 * k as u64));
                    all[n + k] = self.ram.access(cell, ts | u64::from(Clock::block_slot(k)));
                }
                self.hash.push(HashRow {
                    block: h.block,
                    out: h.out,
                    prev: all,
                });
            }
            // An extension-field row's limbs, after its register reads: memory cells, or `x0` for a base-field `b`.
            MemoryAccess::Ext(instance) => {
                let mut all = [0; 3 + Ext::LIMBS];
                all[..n].copy_from_slice(&prev[..n]);
                for k in 0..Ext::LIMBS {
                    let at = ts | u64::from(Clock::limb_slot(k));
                    all[n + k] = match Ext::limb(instance.pointers, instance.flags, k) {
                        Limb::Memory(address) => self.ram.access(cell_of(address), at),
                        Limb::Zero => self.regs.access(0, at),
                    };
                }
                self.ext.push(ExtRow {
                    instance: *instance,
                    c: instance.eval(),
                    prev: all,
                });
            }
        }

        self.rows[table].push(Row {
            index: step.index as u32,
            ts,
            v1: step.v1,
            v2: step.v2,
            out: step.out,
            taken: step.taken,
            vd_old: step.vd_old,
            ram: word,
            prev,
        });
    }

    /// Write out a padding row of entry `index`, at clock zero.
    ///
    /// It touches nothing: every read holds zero, and every write rewrites what it writes.
    ///
    /// Its circuit instance is an honest one, on those zeros.
    ///
    /// An access in slot `k` pushes the timestamp `0 ^ k` and pulls that same timestamp, so the two tuples cancel.
    pub(super) fn pad(&mut self, p: &RiscvProgram, index: usize) {
        let e = &p.entries()[index];
        let table = ClassTable::index_of(e.class).expect("a fill block's class has a table");
        let outcome = e.evaluate(p.pc_of(index), 0, 0, 0);
        let slots = &self.padding_prev[table];

        // Its accesses' timestamps: in its payload for a hash or an extension-field row, in the row otherwise.
        let mut prev = [0; 4];
        match e.class {
            // A hash row compresses a zero block, and rewrites the result it finds there.
            Class::Hash => {
                let block = [0; Hash::WORDS];
                let mut h = BlockAccess::from(Hash {
                    flags: e.flags,
                    t: 0,
                    block,
                });
                h.block[Hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
                let mut all = [0; 2 + Hash::WORDS];
                all.copy_from_slice(slots);
                self.hash.push(HashRow {
                    block: h.block,
                    out: h.out,
                    prev: all,
                });
            }
            // An extension-field row multiplies zeros at address zero, and writes zero over zero.
            Class::Ext => {
                let instance = Ext {
                    flags: e.flags,
                    pointers: [0; 3],
                    limbs: [0; Ext::LIMBS],
                };
                let mut all = [0; 3 + Ext::LIMBS];
                all.copy_from_slice(slots);
                self.ext.push(ExtRow {
                    instance,
                    c: instance.eval(),
                    prev: all,
                });
            }
            _ => prev[..slots.len()].copy_from_slice(slots),
        }

        self.rows[table].push(Row {
            index: index as u32,
            ts: 0,
            v1: 0,
            v2: 0,
            out: outcome.out,
            taken: outcome.taken,
            vd_old: outcome.out,
            ram: outcome.access.unwrap_or_default(),
            prev,
        });
    }

    /// The finished trace: the rows, and what the machine `m` left in each array when the clock stopped at `ts_final`.
    pub(super) fn finish(self, p: &RiscvProgram, m: &Machine<'_>, ts_final: u64) -> Trace {
        let ram_last = self.ram.timestamps();
        let (ram_ts, adv_ts) = ram_last.split_at(1 << p.log_ram());
        Trace {
            rows: self.rows,
            hash: self.hash,
            ext: self.ext,
            reg_fin: m.registers().cells().iter().map(|&r| F64(r)).collect(),
            reg_ts: self.regs.timestamps(),
            ram_fin: m.memory().ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init: self.adv_init,
            adv_fin: m.memory().advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
            ts_final,
        }
    }
}

/// What a hash row adds to a row.
pub(crate) struct HashRow {
    /// The block's words as the row found them.
    pub(crate) block: [u64; Hash::WORDS],
    /// The four words the compression writes.
    pub(crate) out: [u64; 4],
    /// The previous timestamp of every access, the registers' first.
    pub(crate) prev: [u64; 2 + Hash::WORDS],
}

impl HashRow {
    /// Word `k` of the block after the row.
    pub(crate) const fn word_after(&self, k: usize) -> u64 {
        match k.wrapping_sub(Hash::OUT as usize / 8) {
            j if j < 4 => self.out[j],
            _ => self.block[k],
        }
    }
}

/// What an extension-field row adds to a row.
pub(crate) struct ExtRow {
    /// The instance as the row found it.
    pub(crate) instance: Ext,
    /// `c`'s limbs after the row.
    pub(crate) c: [u64; 3],
    /// The previous timestamp of every access, the registers' first.
    pub(crate) prev: [u64; 3 + Ext::LIMBS],
}

/// One executed instruction, as its table's row records it.
pub(crate) struct Row {
    /// The entry executed.
    pub(crate) index: u32,
    /// The row's clock, zero on a padding row.
    pub(crate) ts: u64,
    /// The first register's value.
    pub(crate) v1: u64,
    /// The second register's value.
    pub(crate) v2: u64,
    /// What the class computed.
    pub(crate) out: u64,
    /// Whether the class took the jump.
    pub(crate) taken: bool,
    /// What the destination held before the write, if the class makes one.
    pub(crate) vd_old: u64,
    /// A load's or a store's cell access; zeros for another class.
    pub(crate) ram: WordAccess,
    /// The previous timestamps of the register accesses the class makes, then of its RAM access.
    ///
    /// Unused on a hash or an extension-field row, whose payload records every access.
    pub(crate) prev: [u64; 4],
}

/// What a row records beyond the fields every row has.
#[derive(Clone, Copy)]
pub(crate) enum Payload<'a> {
    /// Nothing: the row of a table with at most one word access.
    None,
    /// A hash row's block, and its accesses.
    Hash(&'a HashRow),
    /// An extension-field row's limbs, and its accesses.
    Ext(&'a ExtRow),
}

/// A row and its payload: everything a circuit port or a column reads.
#[derive(Clone, Copy)]
pub(crate) struct RowRef<'a> {
    /// The fields every row has.
    pub(crate) row: &'a Row,
    /// What the row's table records beyond them.
    pub(crate) payload: Payload<'a>,
}

impl<'a> RowRef<'a> {
    /// A row whose table records no payload.
    pub(crate) const fn plain(row: &'a Row) -> Self {
        Self {
            row,
            payload: Payload::None,
        }
    }

    /// The previous timestamps of the row's accesses in column order, at least as many as its class makes.
    pub(crate) const fn prev(self) -> &'a [u64] {
        match self.payload {
            Payload::None => &self.row.prev,
            Payload::Hash(hash) => &hash.prev,
            Payload::Ext(ext) => &ext.prev,
        }
    }

    /// Cell `k` before the row: a hash row's block word, or the one cell of a load or a store.
    pub(crate) const fn cell(self, k: usize) -> u64 {
        match self.payload {
            Payload::Hash(hash) => hash.block[k],
            _ => self.row.ram.old,
        }
    }

    /// Cell `k` after the row.
    pub(crate) const fn cell_new(self, k: usize) -> u64 {
        match self.payload {
            Payload::Hash(hash) => hash.word_after(k),
            _ => self.row.ram.new,
        }
    }
}

/// One table's payloads, in row order.
#[derive(Clone, Copy)]
pub(crate) enum Payloads<'a> {
    /// The table records none.
    None,
    /// The hash table's.
    Hash(&'a [HashRow]),
    /// The extension-field table's.
    Ext(&'a [ExtRow]),
}

/// One table's rows, and their payloads.
#[derive(Clone, Copy)]
pub(crate) struct TableRows<'a> {
    /// The fields every row has.
    pub(crate) rows: &'a [Row],
    /// What the rows record beyond them, row `i`'s at `i`.
    pub(crate) payloads: Payloads<'a>,
}

impl<'a> TableRows<'a> {
    /// Row `i`, with its payload.
    pub(crate) const fn row(self, i: usize) -> RowRef<'a> {
        let payload = match self.payloads {
            Payloads::None => Payload::None,
            Payloads::Hash(hash) => Payload::Hash(&hash[i]),
            Payloads::Ext(ext) => Payload::Ext(&ext[i]),
        };
        RowRef {
            row: &self.rows[i],
            payload,
        }
    }
}

/// Every row of a run, and what the run leaves for the finalize blocks.
pub(crate) struct Trace {
    /// Each table's rows, in table order.
    pub(crate) rows: [Vec<Row>; tables::N_TABLES],
    /// The hash table's payloads, row `i`'s at `i`.
    pub(crate) hash: Vec<HashRow>,
    /// The extension-field table's payloads, row `i`'s at `i`.
    pub(crate) ext: Vec<ExtRow>,
    /// The registers after the run.
    pub(crate) reg_fin: Vec<F64>,
    /// Each register's last timestamp, the seed's if never touched.
    pub(crate) reg_ts: Vec<F64>,
    /// RAM after the run.
    pub(crate) ram_fin: Vec<F64>,
    /// Each RAM word's last timestamp.
    pub(crate) ram_ts: Vec<F64>,
    /// The advice before the run, which is committed.
    pub(crate) adv_init: Vec<F64>,
    /// The advice after the run.
    pub(crate) adv_fin: Vec<F64>,
    /// Each advice word's last timestamp.
    pub(crate) adv_ts: Vec<F64>,
    /// The clock the run ended on: the final state's timestamp.
    pub(crate) ts_final: u64,
}

impl Trace {
    /// How often each bytecode entry is read, once by every row, written into `counts` as integers.
    pub(crate) fn count_reads(&self, counts: &mut [F64]) {
        counts.fill(F64::ZERO);
        for row in self.rows.iter().flatten() {
            counts[row.index as usize].0 += 1;
        }
    }

    /// Table `t`'s rows, with the payloads they record.
    pub(crate) fn table(&self, t: usize) -> TableRows<'_> {
        let payloads = match ClassSpec::ALL[t].class {
            Class::Hash => Payloads::Hash(&self.hash),
            Class::Ext => Payloads::Ext(&self.ext),
            _ => Payloads::None,
        };
        TableRows {
            rows: &self.rows[t],
            payloads,
        }
    }

    /// The rows per table.
    pub(crate) fn row_counts(&self) -> [usize; tables::N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }
}
