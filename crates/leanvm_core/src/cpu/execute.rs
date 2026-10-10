//! What a run of the program on the reference interpreter records: each table's rows, and the two memory logs.
//!
//! A row carries what its class read and computed, and its positions in the logs.
//!
//! Everything else comes back from the program's entry at the row's index.

use crate::memory::{CHUNK, LogWitness, Regions};
use crate::rv::machine::{MemoryAccess, Step};
use crate::rv::{BlockAccess, Class, Ext, Hash, Limb, Machine, RegisterFile, RiscvProgram, WordAccess};
use crate::tables::{PerTable, TableId};
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
    /// The rows and the logs, emitted in the same walk as the run.
    pub(crate) trace: Trace,
}

/// What a run keeps of each step it makes.
pub(super) trait Recorder {
    /// Record the row of `step`.
    fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step);

    /// The rows recorded so far, per table.
    fn row_counts(&self) -> PerTable<usize>;

    /// The logs' live rows so far: the cycles, then the memory accesses.
    fn live(&self) -> [usize; 2];
}

/// The rows a run makes per table, and nothing else.
pub(super) struct RowCounter {
    /// The table of each bytecode entry, or none for a class with no table.
    tables: Vec<Option<TableId>>,
    /// The rows counted so far, per table.
    counts: PerTable<usize>,
    /// The memory accesses counted so far.
    accesses: usize,
}

impl RowCounter {
    /// A counter for runs of `p`.
    pub(super) fn new(p: &RiscvProgram) -> Self {
        Self {
            tables: p.entries().iter().map(|e| TableId::of(e.class)).collect(),
            counts: PerTable::default(),
            accesses: 0,
        }
    }
}

impl Recorder for RowCounter {
    #[inline(always)]
    fn record(&mut self, _: &RiscvProgram, _: &Machine<'_>, step: Step) {
        let table = self.tables[step.index].expect("every class that runs has a table");
        self.counts[table] += 1;
        self.accesses += match &step.memory {
            MemoryAccess::None => 0,
            MemoryAccess::Word(_) => 1,
            MemoryAccess::Block(_) => Hash::WORDS,
            MemoryAccess::Ext(x) => (0..Ext::LIMBS)
                .filter(|&k| Ext::limb(x.pointers, x.flags, k) != Limb::Zero)
                .count(),
        };
    }

    fn row_counts(&self) -> PerTable<usize> {
        self.counts
    }

    fn live(&self) -> [usize; 2] {
        [self.counts.values().sum(), self.accesses]
    }
}

/// A trace being recorded: the rows so far, and the logs of the run's accesses.
pub(super) struct TraceBuilder {
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
    /// The memory log: a row per access.
    memory: LogWitness,
    /// RAM and the advice as the memory log's cells.
    regions: Regions,
    /// The machine's RAM cells, which its advice cells follow.
    ram_cells: usize,
    /// The next row's register log position, `g^cycle`.
    time: F64,
    /// The next access's memory log position, `g^n`.
    position: F64,
    /// The advice before the run, which is committed.
    adv_init: Vec<F64>,
}

impl Recorder for TraceBuilder {
    #[inline(always)]
    fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step) {
        self.record_row(p, m, step);
    }

    fn row_counts(&self) -> PerTable<usize> {
        PerTable::from_fn(|t| self.rows[t].len())
    }

    fn live(&self) -> [usize; 2] {
        [self.registers.live, self.memory.live]
    }
}

impl TraceBuilder {
    /// The trace of a run of `p`, whose memory log's cells are `regions`, about to start on this advice.
    pub(super) fn new(p: &RiscvProgram, regions: Regions, advice: &[u64]) -> Self {
        let mut initial = vec![F64::ZERO; CHUNK << regions.low];
        for (z, &word) in p.image().iter().enumerate() {
            initial[regions.ram.cell(z, regions.low)] = F64(word);
        }
        for (z, &word) in advice.iter().enumerate() {
            initial[regions.advice.cell(z, regions.low)] = F64(word);
        }
        Self {
            rows: PerTable::default(),
            hash: Vec::new(),
            ext: Vec::new(),
            registers: LogWitness {
                cells: vec![Vec::new(); 3],
                initial: vec![F64::ZERO; RegisterFile::CELLS],
                ..LogWitness::default()
            },
            register_file: [0; RegisterFile::CELLS],
            memory: LogWitness {
                cells: vec![Vec::new()],
                initial,
                ..LogWitness::default()
            },
            ram_cells: 1 << p.log_ram(),
            regions,
            time: F64::ONE,
            position: F64::ONE,
            adv_init: advice.iter().map(|&w| F64(w)).collect(),
        }
    }

    /// Record the row of `step`: its register cycle, then its memory accesses in the order it makes them.
    #[inline(always)]
    fn record_row(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step) {
        let e = &p.entries()[step.index];
        let table = TableId::of(e.class).expect("every class that runs has a table");
        let spec = table.spec();
        let (time, position) = (self.time, self.position);

        // A class with no `rs2` reads `x0`, and one with no write writes zero to the sink; the entry says so.
        // A pointer read is the write group's, flagged, writing back what it found.
        let written = match (spec.writes_rd, spec.reads_rd) {
            (true, _) => step.vd,
            (_, true) => self.register_file[e.ad as usize],
            _ => 0,
        };
        self.cycle([e.a1, e.a2, e.ad], written, spec.reads_rd);

        let cell = |address: u64| m.memory().cell(address).expect("an access the machine made");
        let mut word = WordAccess::default();
        match step.memory {
            MemoryAccess::None => {}
            MemoryAccess::Word(access) => {
                self.access(cell(access.address), access.old, access.new);
                word = access;
            }
            // A hash row's block, word `k` at `v1 ^ 8k`.
            MemoryAccess::Block(h) => {
                let row = HashRow {
                    block: h.block,
                    out: h.out,
                };
                for k in 0..Hash::WORDS {
                    self.access(cell(step.v1 ^ (8 * k as u64)), row.block[k], row.word_after(k));
                }
                self.hash.push(row);
            }
            // An extension-field row's limbs, `c`'s rewritten; a base-field `b`'s high limbs are no access.
            MemoryAccess::Ext(instance) => {
                let c = instance.eval();
                for k in 0..Ext::LIMBS {
                    if let Limb::Memory(address) = Ext::limb(instance.pointers, instance.flags, k) {
                        let after = if k < 6 { instance.limbs[k] } else { c[k - 6] };
                        self.access(cell(address), instance.limbs[k], after);
                    }
                }
                self.ext.push(ExtRow { instance: *instance, c });
            }
        }

        self.rows[table].push(Row {
            index: step.index as u32,
            time: time.0,
            position: position.0,
            v1: step.v1,
            v2: step.v2,
            out: step.out,
            taken: step.taken,
            ram: word,
        });
        self.time *= G;
    }

    /// Append the register log's cycle: cells read, read, written, the written value, and whether it is a pointer read.
    fn cycle(&mut self, cells: [u8; 3], written: u64, pointer: bool) {
        for (group, &cell) in self.registers.cells.iter_mut().zip(&cells) {
            group.push(u32::from(cell));
        }
        let old = std::mem::replace(&mut self.register_file[cells[2] as usize], written);
        self.registers.inc.push(F64(old ^ written));
        self.registers.flag.push(pointer);
        self.registers.live += 1;
    }

    /// Append the memory log's access to the machine's cell `cell`, from `old` to `new`.
    fn access(&mut self, cell: usize, old: u64, new: u64) {
        let (low, ram_cells) = (self.regions.low, self.ram_cells);
        let cell = match cell.checked_sub(ram_cells) {
            None => self.regions.ram.cell(cell, low),
            Some(z) => self.regions.advice.cell(z, low),
        };
        self.memory.cells[0].push(cell as u32);
        self.memory.inc.push(F64(old ^ new));
        self.memory.live += 1;
        self.position *= G;
    }

    /// Write out a padding row of entry `index`.
    pub(super) fn pad(&mut self, p: &RiscvProgram, index: usize) {
        let padding = padding_row(p, index);
        let table = TableId::of(p.entries()[index].class).expect("a fill block's class has a table");
        self.hash.extend(padding.hash);
        self.ext.extend(padding.ext);
        self.rows[table].push(padding.row);
    }

    /// The finished trace.
    pub(super) fn finish(self) -> Trace {
        Trace {
            rows: self.rows,
            hash: self.hash,
            ext: self.ext,
            registers: self.registers,
            memory: self.memory,
            adv_init: self.adv_init,
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

/// The padding row of entry `index`, at positions zero: it reads zeros and touches no log.
///
/// Its circuit instance is an honest one, on those zeros.
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
        }
    });
    let row = Row {
        index: index as u32,
        time: 0,
        position: 0,
        v1: 0,
        v2: 0,
        out: outcome.out,
        taken: outcome.taken,
        ram: outcome.access.unwrap_or_default(),
    };
    PaddingRow { row, hash, ext }
}

/// What a hash row adds to a row.
pub(crate) struct HashRow {
    /// The block's words as the row found them.
    pub(crate) block: [u64; Hash::WORDS],
    /// The four words the compression writes.
    pub(crate) out: [u64; 4],
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
}

/// One executed instruction, as its table's row records it.
pub(crate) struct Row {
    /// The entry executed.
    pub(crate) index: u32,
    /// The row's register log position, `g^cycle`; zero on a padding row.
    pub(crate) time: u64,
    /// The memory log position of the row's first access, `g^n`; zero on a padding row.
    pub(crate) position: u64,
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
}

/// What a row records beyond the fields every row has.
#[derive(Clone, Copy)]
pub(crate) enum Payload<'a> {
    /// Nothing: the row of a table with at most one word access.
    None,
    /// A hash row's block.
    Hash(&'a HashRow),
    /// An extension-field row's limbs.
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

/// Every row of a run, and its two logs.
pub(crate) struct Trace {
    /// Each table's rows, in table order.
    pub(crate) rows: PerTable<Vec<Row>>,
    /// The hash table's payloads, row `i`'s at `i`.
    pub(crate) hash: Vec<HashRow>,
    /// The extension-field table's payloads, row `i`'s at `i`.
    pub(crate) ext: Vec<ExtRow>,
    /// The register log, its live rows alone.
    pub(crate) registers: LogWitness,
    /// The memory log, its live rows alone.
    pub(crate) memory: LogWitness,
    /// The advice before the run, which is committed.
    pub(crate) adv_init: Vec<F64>,
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
