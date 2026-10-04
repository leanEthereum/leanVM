//! What a run of the program on the reference interpreter records for the memory argument.
//!
//! A row carries what its accesses saw, its clock, and per access the timestamp its cell was last accessed at.
//!
//! Everything else comes back from the program's entry at the row's index.

use crate::rv::machine::{MemoryAccess, Step};
use crate::rv::{
    BlockAccess, Class, Ext, ExtResult, Hash, InstructionClass, Limb, Machine, RegisterFile, RiscvProgram, WordAccess,
};
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

/// A trace being recorded: the rows so far, and each cell's last access timestamp.
pub(super) struct TraceBuilder {
    /// The register file's cells.
    regs: LastAccess,
    /// RAM's cells, then the advice's, as the machine numbers them.
    ram: LastAccess,
    /// Each table's rows.
    rows: [Vec<Row>; N_TABLES],
    /// Each table's access slots, which a padding row's accesses pull as their previous timestamps.
    padding_prev: [Vec<u64>; N_TABLES],
    /// The advice before the run, which is committed.
    adv_init: Vec<F64>,
}

impl TraceBuilder {
    /// The rows recorded so far, per table.
    pub(super) fn row_counts(&self) -> [usize; N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }

    /// The trace of a run of `p` about to start on this advice region.
    pub(super) fn new(p: &RiscvProgram, advice: &[u64]) -> Self {
        Self {
            regs: LastAccess::new(RegisterFile::CELLS),
            ram: LastAccess::new((1 << p.log_ram()) + (1 << p.log_advice())),
            rows: std::array::from_fn(|_| Vec::new()),
            padding_prev: std::array::from_fn(|t| ClassSpec::ALL[t].slots().into_iter().map(u64::from).collect()),
            adv_init: advice.iter().map(|&w| F64(w)).collect(),
        }
    }

    /// Record the row of `step`, executed at clock `ts`.
    pub(super) fn record(&mut self, p: &RiscvProgram, m: &Machine<'_>, step: Step, ts: u64) {
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
        let (mut word, mut hash, mut ext) = (WordAccess::default(), None, None);
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
                hash = Some(Box::new(HashRow {
                    block: h.block,
                    out: h.out,
                    prev: all,
                }));
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
                ext = Some(Box::new(ExtRow {
                    instance: *instance,
                    result: instance.eval(),
                    prev: all,
                }));
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
            hash,
            ext,
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
        let outcome = e.evaluate(0, 0, 0);
        let slots = &self.padding_prev[table];

        // A hash row compresses a zero block, and rewrites the result it finds there.
        let hash = (e.class == Class::Hash).then(|| {
            let block = [0; Hash::WORDS];
            let mut h = BlockAccess::from(Hash {
                flags: e.flags,
                t: 0,
                block,
            });
            h.block[Hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
            let mut all = [0; 2 + Hash::WORDS];
            all.copy_from_slice(slots);
            Box::new(HashRow {
                block: h.block,
                out: h.out,
                prev: all,
            })
        });

        // An extension-field row multiplies zeros at address zero, and writes zero over zero.
        let ext = (e.class == Class::Ext).then(|| {
            let instance = Ext {
                flags: e.flags,
                pointers: [0; 3],
                limbs: [0; Ext::LIMBS],
            };
            let mut all = [0; 3 + Ext::LIMBS];
            all.copy_from_slice(slots);
            Box::new(ExtRow {
                instance,
                result: instance.eval(),
                prev: all,
            })
        });

        // Any other row keeps its slots' timestamps itself.
        let mut prev = [0; 4];
        if hash.is_none() && ext.is_none() {
            prev[..slots.len()].copy_from_slice(slots);
        }

        self.rows[table].push(Row {
            index: index as u32,
            ts: 0,
            v1: 0,
            v2: 0,
            out: outcome.out,
            taken: outcome.taken,
            vd_old: if e.link { p.pc_of(index) + 4 } else { outcome.out },
            ram: outcome.access.unwrap_or_default(),
            prev,
            hash,
            ext,
        });
    }

    /// The finished trace: the rows, and what the machine `m` left in each array when the clock stopped at `ts_final`.
    pub(super) fn finish(self, p: &RiscvProgram, m: &Machine<'_>, ts_final: u64) -> Trace {
        let ram_last = self.ram.timestamps();
        let (ram_ts, adv_ts) = ram_last.split_at(1 << p.log_ram());
        Trace {
            rows: self.rows,
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
    /// What the instance computes, and where its limbs are on the bus.
    pub(crate) result: ExtResult,
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
    /// A hash row keeps them in its hash part instead, and an extension-field row in its own.
    pub(crate) prev: [u64; 4],
    /// A hash row's block, and its accesses.
    pub(crate) hash: Option<Box<HashRow>>,
    /// An extension-field row's limbs, and its accesses.
    pub(crate) ext: Option<Box<ExtRow>>,
}

impl Row {
    /// Hash block and output recorded by a compression instruction.
    ///
    /// # Panics
    ///
    /// Panics if this row is not a hash instruction.
    pub(crate) fn hash(&self) -> &HashRow {
        self.hash.as_deref().expect("a hash row has its block")
    }

    /// Extension-field operands and result recorded by a multiplication instruction.
    ///
    /// # Panics
    ///
    /// Panics if this row is not an extension-field instruction.
    pub(crate) fn ext(&self) -> &ExtRow {
        self.ext.as_deref().expect("an extension-field row has its limbs")
    }

    /// The previous timestamps of the row's accesses in column order, at least as many as its class makes.
    pub(crate) fn prev(&self) -> &[u64] {
        match (&self.hash, &self.ext) {
            (Some(hash), _) => &hash.prev,
            (_, Some(ext)) => &ext.prev,
            _ => &self.prev,
        }
    }
}

/// Every row of a run, and what the run leaves for the finalize blocks.
pub(crate) struct Trace {
    /// Each table's rows, in table order.
    pub(crate) rows: [Vec<Row>; tables::N_TABLES],
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

    /// The rows per table.
    pub(crate) fn row_counts(&self) -> [usize; tables::N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }
}
