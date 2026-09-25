//! Run the program on the reference interpreter ([`crate::rv::Machine`]) and record,
//! for every access, what the memory argument needs ([`Trace`]).

use super::*;
use crate::rv::{self, ADVICE_BASE, Class, LOG_REGS, Machine, RAM_BASE, Trap, hash, machine::compute};
use crate::tables::{CLASSES, CLOCK_STRIDE, RAM_SLOT, RANGE_LOG, REG_SLOTS, block_slot};
use primitives::field::{F64, mul_by_g};

pub struct Execution {
    /// The public output: `a0..a3` as the run left them.
    pub output: [u64; 4],
    pub cycles: usize, // number of rows proven, padding rows included
    /// Rows per table before the padding rows: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows, final timestamps and counts, emitted in the same walk
}

/// Running read counts `g^{count}` of the two range arrays' entries, which every
/// read-write array's gap checks share.
struct Ranges {
    lo: Vec<F64>,
    hi: Vec<F64>,
}

impl Ranges {
    /// One read of each range array, at the chunks of `gap`.
    #[inline(always)]
    fn read(&mut self, gap: u32) -> (F64, F64) {
        let (lo, hi) = ((gap & ((1 << RANGE_LOG) - 1)) as usize, (gap >> RANGE_LOG) as usize);
        let counts = (self.lo[lo], self.hi[hi]);
        self.lo[lo] = mul_by_g(counts.0);
        self.hi[hi] = mul_by_g(counts.1);
        counts
    }
}

/// What the memory argument keeps per cell of one read-write array (§sec:memchan):
/// its last access, as the clock's exponent and as its g-power.
struct Cells {
    last: Vec<u32>,
    last_ts: Vec<F64>,
}

impl Cells {
    /// Every cell starts last accessed at the seed's `g^0`.
    fn new(n: usize) -> Self {
        Self {
            last: vec![0; n],
            last_ts: vec![F64::ONE; n],
        }
    }

    /// Access `cell` at clock `y`, whose g-power is `ts`.
    #[inline(always)]
    fn access(&mut self, ranges: &mut Ranges, cell: usize, y: u32, ts: F64) -> Access {
        let (x, x_ts) = (self.last[cell], self.last_ts[cell]);
        // The clock only moves forward, and starts after the seed's zero.
        let gap = y - x - 1;
        let (count_lo, count_hi) = ranges.read(gap);
        self.last[cell] = y;
        self.last_ts[cell] = ts;
        Access {
            x: x_ts,
            gap,
            count_lo,
            count_hi,
        }
    }
}

/// A padding row's access: clock zero on both sides, so the identity holds with the
/// first entry of each range array.
fn padding_access(ranges: &mut Ranges) -> Access {
    let (count_lo, count_hi) = ranges.read(0);
    Access {
        x: F64::ZERO,
        gap: 0,
        count_lo,
        count_hi,
    }
}

/// The access a row does not make: its columns do not exist, so nothing reads it.
fn padding_access_unread() -> Access {
    Access {
        x: F64::ZERO,
        gap: 0,
        count_lo: F64::ZERO,
        count_hi: F64::ZERO,
    }
}

/// `ts·g^k`.
fn advance(ts: F64, k: u32) -> F64 {
    (0..k).fold(ts, |t, _| mul_by_g(t))
}

impl Program {
    /// Run the program on `input` and `advice`, recording every row, then write out the
    /// padding rows that bring each table to a power of two ([`filler`]). A run that
    /// traps has no proof.
    pub fn execute(&self, input: [u64; rv::INPUT_WORDS], advice: &[u64]) -> Result<Execution, Trap> {
        let p = &self.rv;
        let mut m = Machine::new(p, input, advice);
        let adv_init: Vec<F64> = m.advice().iter().map(|&w| F64(w)).collect();
        let mut ranges = Ranges {
            lo: vec![F64::ONE; 1 << RANGE_LOG],
            hi: vec![F64::ONE; 1 << RANGE_LOG],
        };
        let mut regs = Cells::new(1 << LOG_REGS);
        // RAM's cells, then the advice's, as the machine numbers them.
        let mut ram = Cells::new((1 << p.log_ram) + (1 << p.log_advice));
        let cell_of = |address: u64| -> usize {
            if address >= RAM_BASE {
                ((address - RAM_BASE) / 8) as usize
            } else {
                (1 << p.log_ram) + ((address - ADVICE_BASE) / 8) as usize
            }
        };
        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; p.entries.len()];
        let mut fetch = |index: usize| {
            let v = bytecode_count[index];
            bytecode_count[index] = mul_by_g(v);
            v
        };
        let mut rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // The clock, as an exponent and as its g-power: cycle 1, so that the first
        // access comes strictly after the seeds.
        let mut tick = CLOCK_STRIDE;
        let mut ts = crate::tables::CLOCK_START;
        while !m.halted() {
            // A cell's first access is measured from the seed, so the whole run has
            // to fit the range a gap can take (§sec:memchan).
            if tick >= u32::MAX - block_slot(hash::WORDS) {
                return Err(Trap::CycleCap);
            }
            let step = m.step()?;
            let e = &p.entries[step.index];
            let table = crate::tables::table_of(e.class).expect("every class that runs has a table");
            let spec = CLASSES[table];
            // The register accesses, then the RAM access if the class has one. Their
            // order here is the order of their columns, not of their clock slots.
            let cells = [e.a1, e.a2, e.ad].map(|cell| cell as usize);
            let n_regs = if spec.writes_register() { 3 } else { 2 };
            let mut acc: [Access; 4] = std::array::from_fn(|i| match cells.get(i) {
                Some(&cell) if i < n_regs => {
                    regs.access(&mut ranges, cell, tick + REG_SLOTS[i], advance(ts, REG_SLOTS[i]))
                }
                _ => padding_access_unread(),
            });
            if let Some(access) = step.ram {
                let cell = cell_of(access.address);
                acc[3] = ram.access(&mut ranges, cell, tick + RAM_SLOT, advance(ts, RAM_SLOT));
            }
            // A hash row's block, word `k` at `v1 ^ 8k`, after its two register reads.
            let hash = step.hash.map(|h| {
                let mut all = [padding_access_unread(); 2 + hash::WORDS];
                all[..2].copy_from_slice(&acc[..2]);
                for k in 0..hash::WORDS {
                    let cell = cell_of(step.v1 ^ (8 * k as u64));
                    all[2 + k] = ram.access(&mut ranges, cell, tick + block_slot(k), advance(ts, block_slot(k)));
                }
                Box::new(HashRow {
                    block: h.block,
                    out: h.out,
                    acc: all,
                })
            });
            rows[table].push(Row {
                index: step.index as u32,
                ts,
                v1: step.v1,
                v2: step.v2,
                out: step.out,
                taken: step.taken,
                vd_old: step.vd_old,
                ram: step.ram.unwrap_or_default(),
                acc,
                hash,
                bytecode_read: fetch(step.index),
            });
            tick += spec.stride();
            ts = advance(ts, spec.stride());
        }
        let syscall = m.regs[rv::SYSCALL_REG as usize];
        if syscall != rv::SYS_EXIT {
            return Err(Trap::NotAnExit { syscall });
        }
        let output = rv::OUTPUT_REGS.map(|r| m.regs[r as usize]);
        let base_counts: [usize; crate::tables::N_TABLES] = std::array::from_fn(|t| rows[t].len());

        // The padding rows, written out rather than executed: they sit at clock zero
        // and touch nothing, every read holding zero and every write rewriting what it
        // writes (`filler`). Their circuit instance is an honest one, on those zeros.
        for (first, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
            for _ in 0..traversals {
                for index in first..=first + size {
                    let e = &p.entries[index];
                    let table = crate::tables::table_of(e.class).expect("a fill block's class has a table");
                    let (out, taken, access) = compute(e, 0, 0, 0);
                    let n_accesses = CLASSES[table].n_accesses();
                    // The row's accesses are all padding ones, in a hash row's own array.
                    let mut acc = [padding_access_unread(); 4];
                    let mut hash = (e.class == Class::Hash).then(|| {
                        // The compression of a zero block, whose result the row rewrites.
                        let mut h = rv::machine::compute_hash([0; hash::WORDS], 0, e.flags);
                        h.block[hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
                        Box::new(HashRow {
                            block: h.block,
                            out: h.out,
                            acc: [padding_access_unread(); 2 + hash::WORDS],
                        })
                    });
                    let all = hash.as_mut().map_or(&mut acc[..], |h| &mut h.acc[..]);
                    for a in &mut all[..n_accesses] {
                        *a = padding_access(&mut ranges);
                    }
                    rows[table].push(Row {
                        index: index as u32,
                        ts: F64::ZERO,
                        v1: 0,
                        v2: 0,
                        out,
                        taken,
                        vd_old: if e.link { p.pc_of(index) + 4 } else { out },
                        ram: access,
                        acc,
                        hash,
                        bytecode_read: fetch(index),
                    });
                }
            }
        }

        let cycles = rows.iter().map(Vec::len).sum();
        let (ram_ts, adv_ts) = ram.last_ts.split_at(1 << p.log_ram);
        let trace = Trace {
            rows,
            reg_fin: m.regs.iter().map(|&r| F64(r)).collect(),
            reg_ts: regs.last_ts,
            ram_fin: m.ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init,
            adv_fin: m.advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
            bytecode_count,
            range_lo_count: ranges.lo,
            range_hi_count: ranges.hi,
            ts_final: ts,
        };
        Ok(Execution {
            output,
            cycles,
            base_counts,
            trace,
        })
    }
}
