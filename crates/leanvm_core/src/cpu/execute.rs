//! What a run of the program on the reference interpreter records for the register log and the memory argument.
//!
//! A row carries what its accesses saw, its time and clock, and per memory access the timestamp its cell was last
//! accessed at.
//!
//! Everything else comes back from the program's entry at the row's index.

use crate::registers::LogWitness;
use crate::rv::machine::{MemoryAccess, Step};
use crate::rv::{BlockAccess, Class, Ext, Hash, Limb, Machine, RegisterFile, RiscvProgram, WordAccess};
use crate::tables::{Clock, PerTable, TableId};
use primitives::field::{F64, G};

/// A finished run: its output, its rows, and what it left behind.
pub struct Execution {
    /// The public output: `a0` to `a3` as the run left them.
    pub output: [u64; 4],
    /// The rows proven, padding rows included.
    pub proven_rows: usize,
    /// The rows per table before the padding rows: the work the program itself does.
    ///
    /// Cost measurements want these, not the power-of-two heights that get proven.
    pub base_counts: PerTable<usize>,
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
    fn row_counts(&self) -> PerTable<usize>;

    /// The cycles recorded so far: the register log's live rows.
    fn cycles(&self) -> usize {
        self.row_counts().values().sum()
    }
}

/// The rows a run makes per table, and nothing else.
pub(super) struct RowCounter {
    /// The table of each bytecode entry, or none for a class with no table.
    tables: Vec<Option<TableId>>,
    /// The rows counted so far, per table.
    counts: PerTable<usize>,
}

impl RowCounter {
    /// A counter for runs of `p`.
    pub(super) fn new(p: &RiscvProgram) -> Self {
        Self {
            tables: p.entries().iter().map(|e| TableId::of(e.class)).collect(),
            counts: PerTable::default(),
        }
    }
}

impl Recorder for RowCounter {
    #[inline(always)]
    fn record(&mut self, _: &RiscvProgram, _: &Machine<'_>, step: Step, _: u64) {
        let table = self.tables[step.index].expect("every class that runs has a table");
        self.counts[table] += 1;
    }

    fn row_counts(&self) -> PerTable<usize> {
        self.counts
    }
}

/// A trace being recorded: the rows so far, the register log, and each memory cell's last access timestamp.
pub(super) struct TraceBuilder {
    /// RAM's cells, then the advice's, as the machine numbers them.
    ram: LastAccess,
    /// The zero cell, which a base-field extension operand's high limbs read.
    zero: LastAccess,
    /// Each table's rows.
    rows: PerTable<Vec<Row>>,
    /// The hash table's payloads, one per row.
    hash: Vec<HashRow>,
    /// The extension-field table's payloads, one per row.
    ext: Vec<ExtRow>,
    /// The register log: a row per cycle.
    registers: LogWitness,
    /// The register file as the register log leaves it.
    register_file: [u64; RegisterFile::CELLS],
    /// The next row's time, `g^cycle`.
    time: F64,
    /// The advice before the run, which is committed.
    adv_init: Vec<F64>,
}

impl Recorder for TraceBuilder {
    #[inline(always)]
    fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64) {
        self.record_row(p, m, step, ts);
    }

    fn row_counts(&self) -> PerTable<usize> {
        PerTable::from_fn(|t| self.rows[t].len())
    }

    fn cycles(&self) -> usize {
        self.registers.live
    }
}

impl TraceBuilder {
    /// The trace of a run of `p` about to start on this advice region.
    pub(super) fn new(p: &RiscvProgram, advice: &[u64]) -> Self {
        Self {
            ram: LastAccess::new((1 << p.log_ram()) + (1 << p.log_advice())),
            zero: LastAccess::new(1),
            rows: PerTable::default(),
            hash: Vec::new(),
            ext: Vec::new(),
            registers: LogWitness::default(),
            register_file: [0; RegisterFile::CELLS],
            time: F64::ONE,
            adv_init: advice.iter().map(|&w| F64(w)).collect(),
        }
    }

    /// Record the row of `step`, executed at clock `ts`: its register cycle, then its memory accesses in order.
    #[inline(always)]
    fn record_row(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64) {
        let e = &p.entries()[step.index];
        let table = TableId::of(e.class).expect("every class that runs has a table");
        let spec = table.spec();

        // A class with no `rs2` reads `x0`, and one with no write writes zero to the sink; the entry says so.
        // A pointer read is the write group's, flagged, writing back what it found.
        let written = match (spec.writes_rd, spec.reads_rd) {
            (true, _) => step.out,
            (_, true) => self.register_file[e.ad as usize],
            _ => 0,
        };
        self.cycle([e.a1, e.a2, e.ad], written, spec.reads_rd);

        // The memory accesses, access `k` at slot `k` of the row's clock; the machine made them, so each names a cell.
        let cell_of = |address: u64| m.memory().cell(address).expect("an access the machine made");
        let mut word = WordAccess::default();
        let mut prev = [0; 1];
        match step.memory {
            MemoryAccess::None => {}
            MemoryAccess::Word(access) => {
                prev[0] = self.ram.access(cell_of(access.address), ts);
                word = access;
            }
            // A hash row's block, word `k` at `v1 ^ 8k`.
            MemoryAccess::Block(h) => {
                let prev = std::array::from_fn(|k| self.ram.access(cell_of(step.v1 ^ (8 * k as u64)), ts | k as u64));
                self.hash.push(HashRow {
                    block: h.block,
                    out: h.out,
                    prev,
                });
            }
            // An extension-field row's limbs: memory cells, or the zero cell for a base-field `b`'s high limbs.
            MemoryAccess::Ext(instance) => {
                let prev = std::array::from_fn(|k| {
                    let at = ts | k as u64;
                    match Ext::limb(instance.pointers, instance.flags, k) {
                        Limb::Memory(address) => self.ram.access(cell_of(address), at),
                        Limb::Zero => self.zero.access(0, at),
                    }
                });
                self.ext.push(ExtRow {
                    instance: *instance,
                    c: instance.eval(),
                    prev,
                });
            }
        }

        self.rows[table].push(Row {
            index: step.index as u32,
            ts,
            time: self.time.0,
            v1: step.v1,
            v2: step.v2,
            out: step.out,
            taken: step.taken,
            ram: word,
            prev,
        });
        self.time *= G;
    }

    /// Append the register log's cycle: cells read, read, written, the written value, and whether it is a pointer read.
    fn cycle(&mut self, cells: [u8; 3], written: u64, pointer: bool) {
        for (group, &cell) in self.registers.cells.iter_mut().zip(&cells) {
            group.push(cell);
        }
        let old = std::mem::replace(&mut self.register_file[cells[2] as usize], written);
        self.registers.inc.push(F64(old ^ written));
        self.registers.flag.push(pointer);
        self.registers.live += 1;
    }

    /// Write out a padding row of entry `index`.
    pub(super) fn pad(&mut self, p: &RiscvProgram, index: usize) {
        let padding = padding_row(p, index);
        let table = TableId::of(p.entries()[index].class).expect("a fill block's class has a table");
        self.hash.extend(padding.hash);
        self.ext.extend(padding.ext);
        self.rows[table].push(padding.row);
    }

    /// The finished trace: the rows, the register log, and what the machine `m` left in each memory array when the
    /// clock stopped at `ts_final`.
    pub(super) fn finish(self, p: &RiscvProgram, m: &Machine<'_>, ts_final: u64) -> Trace {
        let ram_last = self.ram.timestamps();
        let (ram_ts, adv_ts) = ram_last.split_at(1 << p.log_ram());
        Trace {
            rows: self.rows,
            hash: self.hash,
            ext: self.ext,
            registers: self.registers,
            ram_fin: m.memory().ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init: self.adv_init,
            adv_fin: m.memory().advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
            zero_ts: self.zero.0[0],
            ts_final,
        }
    }
}

/// A padding row and its payload.
pub(crate) struct PaddingRow {
    pub(crate) row: Row,
    pub(crate) hash: Option<HashRow>,
    pub(crate) ext: Option<ExtRow>,
}

impl PaddingRow {
    /// The row with its payload.
    pub(crate) const fn view(&self) -> RowRef<'_> {
        let payload = match (&self.hash, &self.ext) {
            (Some(hash), _) => Payload::Hash(hash),
            (_, Some(ext)) => Payload::Ext(ext),
            _ => Payload::None,
        };
        RowRef {
            row: &self.row,
            payload,
        }
    }
}

/// The padding row of entry `index`, at time and clock zero.
///
/// - Its register cycle is at time zero, which no log row has: it pulls a public padding tuple.
/// - Its memory access in slot `k` pushes the timestamp `0 ^ k` and pulls that same timestamp, so the two cancel.
///
/// Its circuit instance is an honest one, on zeros.
pub(crate) fn padding_row(p: &RiscvProgram, index: usize) -> PaddingRow {
    let e = &p.entries()[index];
    let outcome = e.evaluate(p.pc_of(index), 0, 0, 0);
    // A hash row compresses a zero block, and rewrites the result it finds there.
    let hash = (e.class == Class::Hash).then(|| {
        let mut h = BlockAccess::from(Hash {
            flags: e.flags,
            t: 0,
            block: [0; Hash::WORDS],
        });
        h.block[Hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
        HashRow {
            block: h.block,
            out: h.out,
            prev: std::array::from_fn(|k| k as u64),
        }
    });
    // An extension-field row multiplies zeros at address zero, and writes zero over zero.
    let ext = (e.class == Class::Ext).then(|| {
        let instance = Ext {
            flags: e.flags,
            pointers: [0; 3],
            limbs: [0; Ext::LIMBS],
        };
        ExtRow {
            instance,
            c: instance.eval(),
            prev: std::array::from_fn(|k| k as u64),
        }
    });
    let row = Row {
        index: index as u32,
        ts: 0,
        time: 0,
        v1: 0,
        v2: 0,
        out: outcome.out,
        taken: outcome.taken,
        ram: outcome.access.unwrap_or_default(),
        prev: [0],
    };
    PaddingRow { row, hash, ext }
}

/// What a hash row adds to a row.
pub(crate) struct HashRow {
    /// The block's words as the row found them.
    pub(crate) block: [u64; Hash::WORDS],
    /// The four words the compression writes.
    pub(crate) out: [u64; 4],
    /// The previous timestamp of every access.
    pub(crate) prev: [u64; Hash::WORDS],
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
    /// The previous timestamp of every access.
    pub(crate) prev: [u64; Ext::LIMBS],
}

/// One executed instruction, as its table's row records it.
pub(crate) struct Row {
    /// The entry executed.
    pub(crate) index: u32,
    /// The row's clock, zero on a padding row.
    pub(crate) ts: u64,
    /// The row's time, `g^cycle`, zero on a padding row.
    pub(crate) time: u64,
    /// The first register's value.
    pub(crate) v1: u64,
    /// The second register's value.
    pub(crate) v2: u64,
    /// What the class computed.
    pub(crate) out: u64,
    /// Whether the class took the jump.
    pub(crate) taken: bool,
    /// A load's or a store's cell access; zeros for another class.
    pub(crate) ram: WordAccess,
    /// The previous timestamp of a load's or a store's access.
    ///
    /// Unused on another row: a hash or an extension-field row's payload records every access.
    pub(crate) prev: [u64; 1],
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
    pub(crate) rows: PerTable<Vec<Row>>,
    /// The hash table's payloads, row `i`'s at `i`.
    pub(crate) hash: Vec<HashRow>,
    /// The extension-field table's payloads, row `i`'s at `i`.
    pub(crate) ext: Vec<ExtRow>,
    /// The register log: a row per cycle.
    pub(crate) registers: LogWitness,
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
    /// The zero cell's last timestamp.
    pub(crate) zero_ts: u64,
    /// The clock the run ended on: the final state's timestamp.
    pub(crate) ts_final: u64,
}

impl Trace {
    /// How often each bytecode entry is read, once by every row, written into `counts` as integers.
    pub(crate) fn count_reads(&self, counts: &mut [F64]) {
        counts.fill(F64::ZERO);
        for row in self.rows.values().flatten() {
            counts[row.index as usize].0 += 1;
        }
    }

    /// Table `t`'s rows, with the payloads they record.
    pub(crate) fn table(&self, t: TableId) -> TableRows<'_> {
        let payloads = match t.class() {
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
    pub(crate) fn row_counts(&self) -> PerTable<usize> {
        PerTable::from_fn(|t| self.rows[t].len())
    }
}
