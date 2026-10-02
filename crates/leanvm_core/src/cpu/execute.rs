//! Run the program on the reference interpreter ([`crate::rv::Machine`]) and record,
//! for every access, what the memory argument needs ([`Trace`]).

use super::*;
use crate::rv::machine::MemoryAccess;
use crate::rv::{BlockAccess, Class, Hash, Machine, RegisterFile, WordAccess};
use crate::tables::{CLASSES, CLOCK_START, CYCLE, MAX_CYCLES, RAM_SLOT, REG_SLOTS, SEED_CLOCK, block_slot};
use primitives::field::F64;

pub struct Execution {
    /// The public output: `a0..a3` as the run left them.
    pub output: [u64; 4],
    pub cycles: usize, // number of rows proven, padding rows included
    /// Rows per table before the padding rows: each table's height, the work the
    /// program itself does, as against the power-of-two counts that get proven. Cost
    /// measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows, final timestamps and counts, emitted in the same walk
}

/// Each cell's last timestamp in one read-write array, the memory argument's bookkeeping (§sec:memchan).
struct Cells {
    last: Vec<u64>,
}

impl Cells {
    /// Every cell starts last accessed at the seed's timestamp.
    fn new(n: usize) -> Self {
        Self {
            last: vec![SEED_CLOCK; n],
        }
    }

    /// Access `cell` at timestamp `at`, returning the timestamp of its previous access.
    #[inline(always)]
    fn access(&mut self, cell: usize, at: u64) -> u64 {
        std::mem::replace(&mut self.last[cell], at)
    }

    fn timestamps(&self) -> Vec<F64> {
        self.last.iter().map(|&t| F64(t)).collect()
    }
}

// Why: every row commits at least one word of its own, so a run one commitment holds is far below the cycles the clock counts.
const _: () = assert!(1u64 << crate::pcs::MAX_MU < MAX_CYCLES);

impl Program {
    /// Run the program on `advice`, recording every row, then write out the
    /// padding rows that bring each table to its proven size ([`padding`]). A run that
    /// traps, or outruns the clock, has no proof.
    pub fn execute(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let max = 1 << p.log_advice();
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        let mut m = Machine::new(p, advice);
        let adv_init: Vec<F64> = m.memory().advice().iter().map(|&w| F64(w)).collect();
        let mut regs = Cells::new(RegisterFile::CELLS);
        // RAM's cells, then the advice's, as the machine numbers them.
        let mut ram = Cells::new((1 << p.log_ram()) + (1 << p.log_advice()));
        let mut rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // The clock starts on cycle 1, so that the first access comes strictly after the seeds.
        let mut ts = CLOCK_START;
        while !m.halted() {
            // The cycle count must not carry into the live bit, and the run's final clock is one cycle past its last row.
            if ts >> crate::tables::SLOT_BITS & MAX_CYCLES == MAX_CYCLES {
                return Err(ProveError::TooLong);
            }
            let step = m.step()?;
            let e = &p.entries()[step.index];
            let table = crate::tables::table_of(e.class).expect("every class that runs has a table");
            let spec = CLASSES[table];
            // The register accesses the class makes, then the RAM access if it has one.
            // Their order here is the order of their columns, not of their clock slots.
            let cells = [e.a1, e.a2, e.ad].map(|cell| cell as usize);
            let made = [true, spec.reads_rs2, spec.writes_rd];
            let mut prev = [0; 4];
            let mut n = 0;
            for (i, slot) in REG_SLOTS.into_iter().enumerate() {
                if made[i] {
                    prev[n] = regs.access(cells[i], ts | u64::from(slot));
                    n += 1;
                }
            }
            // The machine made every access it reports, so each address names a cell.
            let cell_of = |address: u64| m.memory().cell(address).expect("an access the machine made");
            let (mut word, mut hash) = (WordAccess::default(), None);
            match step.memory {
                MemoryAccess::None => {}
                MemoryAccess::Word(access) => {
                    prev[n] = ram.access(cell_of(access.address), ts | u64::from(RAM_SLOT));
                    word = access;
                }
                // A hash row's block, word `k` at `v1 ^ 8k`, after its register reads.
                MemoryAccess::Block(h) => {
                    let mut all = [0; 2 + Hash::WORDS];
                    all[..n].copy_from_slice(&prev[..n]);
                    for k in 0..Hash::WORDS {
                        let cell = cell_of(step.v1 ^ (8 * k as u64));
                        all[n + k] = ram.access(cell, ts | u64::from(block_slot(k)));
                    }
                    hash = Some(Box::new(HashRow {
                        block: h.block,
                        out: h.out,
                        prev: all,
                    }));
                }
            }
            rows[table].push(Row {
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
            });
            ts += CYCLE;
        }
        let output = m.output()?;
        let base_counts: [usize; crate::tables::N_TABLES] = std::array::from_fn(|t| rows[t].len());

        // The padding row, written out rather than executed: one row per table, a no-op
        // at clock zero touching nothing, every read holding zero and every write
        // rewriting what it writes, which every row up to the table's proven size
        // repeats and nothing stores more than once. The bus leaves it out; its circuit
        // instance is an honest one, on those zeros.
        let mut cycles = 0;
        for (t, rows) in rows.iter_mut().enumerate() {
            let proven = 1 << super::tau_of(t, rows.len());
            cycles += proven;
            if rows.len() == proven {
                continue;
            }
            let index = self.noops[t];
            let e = &p.entries()[index];
            let outcome = e.evaluate(0, 0, 0);
            let slots: Vec<u64> = CLASSES[t].slots().into_iter().map(u64::from).collect();
            let mut prev = [0; 4];
            let hash = (e.class == Class::Hash).then(|| {
                // The compression of a zero block, whose result the row rewrites.
                let mut h = BlockAccess::from(Hash {
                    flags: e.flags,
                    t: 0,
                    block: [0; Hash::WORDS],
                });
                h.block[Hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
                let mut all = [0; 2 + Hash::WORDS];
                all.copy_from_slice(&slots);
                Box::new(HashRow {
                    block: h.block,
                    out: h.out,
                    prev: all,
                })
            });
            if hash.is_none() {
                prev[..slots.len()].copy_from_slice(&slots);
            }
            let row = Row {
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
            };
            rows.push(row);
        }

        let ram_last = ram.timestamps();
        let (ram_ts, adv_ts) = ram_last.split_at(1 << p.log_ram());
        let trace = Trace {
            rows,
            reg_fin: m.registers().cells().iter().map(|&r| F64(r)).collect(),
            reg_ts: regs.timestamps(),
            ram_fin: m.memory().ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init,
            adv_fin: m.memory().advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
            ts_final: ts,
            heights: base_counts,
        };
        Ok(Execution {
            output,
            cycles,
            base_counts,
            trace,
        })
    }
}
