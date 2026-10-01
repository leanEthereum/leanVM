//! Record instruction rows and memory timestamps by replaying independent chunks.

use super::*;
use crate::rv::{self, ADVICE_BASE, Class, LOG_REGS, Machine, RAM_BASE, Trap, hash, machine::compute};
use crate::tables::{CLASSES, CLOCK_START, CYCLE, MAX_CYCLES, RAM_SLOT, REG_SLOTS, SEED_CLOCK, block_slot};
use parallel::SendPtr;
use primitives::field::F64;

pub struct Execution {
    /// The public output: `a0..a3` as the run left them.
    pub output: [u64; 4],
    pub cycles: usize, // number of rows proven, padding rows included
    /// Rows per table before the padding rows: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
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

/// Enough rows to amortize replay setup while keeping each snapshot bounded.
const CHUNK_ROWS: usize = 1 << 16;

/// A replay starting state with only the memory cells this chunk accesses.
struct Chunk {
    /// Address of the first instruction to replay.
    pc: u64,
    /// Global clock at the chunk's first row.
    ts: u64,
    /// Register values before the first instruction.
    regs: [u64; 1 << LOG_REGS],
    /// Last access timestamps of those registers.
    reg_ts: Vec<u64>,
    /// Number of preceding rows in each instruction table.
    offsets: [usize; crate::tables::N_TABLES],
    /// Number of rows this chunk contributes to each table.
    counts: [usize; crate::tables::N_TABLES],
    /// Distinct cells with their first value and preceding timestamp.
    memory: Vec<(usize, u64, u64)>,
}

/// Map both memory regions into the interpreter's shared cell numbering.
fn cell_of(p: &rv::Program, address: u64) -> usize {
    // RAM precedes advice in both values and timestamps.
    if address >= RAM_BASE {
        ((address - RAM_BASE) / 8) as usize
    } else {
        (1 << p.log_ram) + ((address - ADVICE_BASE) / 8) as usize
    }
}

/// Bind the interpreter's values to the previous timestamps of its accesses.
fn record_step(
    p: &rv::Program,
    step: rv::machine::Step,
    ts: u64,
    regs: &mut Cells,
    mut access: impl FnMut(usize, u64) -> u64,
) -> Row {
    // Column order is register reads, register write, then the ordinary memory access.
    let e = &p.entries[step.index];
    let spec = CLASSES[crate::tables::table_of(e.class).expect("executed class has a table")];
    // Aliases observe successive clocks: read slot 0, read slot 1, write slot 3.
    let mut prev = [0; 4];
    let mut n = 0;
    for ((cell, made), slot) in [e.a1, e.a2, e.ad]
        .into_iter()
        .zip([true, spec.reads_rs2, spec.writes_rd])
        .zip(REG_SLOTS)
    {
        if made {
            prev[n] = regs.access(cell as usize, ts | u64::from(slot));
            n += 1;
        }
    }

    // Ordinary memory occupies slot 2 on a separate array from the registers.
    if let Some(a) = step.ram {
        prev[n] = access(cell_of(p, a.address), ts | u64::from(RAM_SLOT));
    }

    // Hash reads and writes use all sixteen block slots, including permuted bases.
    let hash = step.hash.map(|h| {
        let mut all = [0; 2 + hash::WORDS];
        all[..n].copy_from_slice(&prev[..n]);
        for k in 0..hash::WORDS {
            all[n + k] = access(cell_of(p, step.v1 ^ (8 * k as u64)), ts | u64::from(block_slot(k)));
        }
        Box::new(HashRow {
            block: h.block,
            out: h.out,
            prev: all,
        })
    });

    // The row now contains both interpreter values and the matching access history.
    Row {
        index: step.index as u32,
        ts,
        v1: step.v1,
        v2: step.v2,
        out: step.out,
        taken: step.taken,
        vd_old: step.vd_old,
        ram: step.ram.unwrap_or_default(),
        prev,
        hash,
    }
}

impl Program {
    /// Run and record each chunk independently after discovering its starting state.
    pub fn execute(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        // A single worker avoids paying for a second interpreter walk.
        if parallel::num_threads() == 1 {
            return self.execute_serial(advice);
        }
        self.execute_chunks(advice, CHUNK_ROWS)
    }

    /// Discover first-access memory snapshots without copying either memory region.
    fn execute_chunks(&self, advice: &[u64], chunk_rows: usize) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let max = 1 << p.log_advice;
        // Reject excess advice before allocating its declared region.
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        let planning = tracing::info_span!("Plan trace").entered();
        let mut m = Machine::new(p, advice);
        let adv_init = m.advice().iter().map(|&word| F64(word)).collect();
        let mut regs = Cells::new(1 << LOG_REGS);
        let mut ram = Cells::new((1 << p.log_ram) + (1 << p.log_advice));
        let mut ts = CLOCK_START;
        let mut counts = [0; crate::tables::N_TABLES];
        let mut chunks = Vec::new();
        let mut first_rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // Phase 1: only the first access to a cell needs a saved value and timestamp.
        while !m.halted() {
            let mut chunk = Chunk {
                pc: m.pc(),
                ts,
                regs: *m.regs(),
                reg_ts: regs.last.clone(),
                offsets: counts,
                counts: [0; crate::tables::N_TABLES],
                memory: Vec::new(),
            };
            for _ in 0..chunk_rows {
                if m.halted() {
                    break;
                }
                // The next clock must remain below the live bit.
                if ts >> crate::tables::SLOT_BITS & MAX_CYCLES == MAX_CYCLES {
                    return Err(ProveError::TooLong);
                }
                let step = m.step()?;
                let e = &p.entries[step.index];
                let table = crate::tables::table_of(e.class).expect("executed class has a table");
                // Keep the first chunk's rows: short runs need no second walk.
                if chunks.is_empty() {
                    first_rows[table].push(record_step(p, step, ts, &mut regs, |cell, at| ram.access(cell, at)));
                    counts[table] += 1;
                    chunk.counts[table] += 1;
                    ts += CYCLE;
                    continue;
                }
                let spec = CLASSES[table];
                for ((cell, made), slot) in [e.a1, e.a2, e.ad]
                    .into_iter()
                    .zip([true, spec.reads_rs2, spec.writes_rd])
                    .zip(REG_SLOTS)
                {
                    if made {
                        regs.access(cell as usize, ts | u64::from(slot));
                    }
                }
                // Invariant: a timestamp before the chunk start identifies its first access.
                let mut access = |address, old, slot| {
                    let cell = cell_of(p, address);
                    let prev = ram.access(cell, ts | u64::from(slot));
                    if prev < chunk.ts {
                        chunk.memory.push((cell, old, prev));
                    }
                };
                if let Some(a) = step.ram {
                    access(a.address, a.old, RAM_SLOT);
                }
                if let Some(h) = step.hash {
                    for (k, word) in h.block.into_iter().enumerate() {
                        access(step.v1 ^ (8 * k as u64), word, block_slot(k));
                    }
                }
                counts[table] += 1;
                chunk.counts[table] += 1;
                ts += CYCLE;
            }
            // Address order gives replay compact storage with deterministic lookup.
            chunk.memory.sort_unstable_by_key(|&(cell, _, _)| cell);
            chunks.push(chunk);
        }

        // Reuse direct recording when the entire run fits in the first chunk.
        if chunks.len() == 1 {
            drop(planning);
            return self.finish(m, regs, ram, adv_init, first_rows, ts);
        }
        // Validate exit before dispatching replay workers.
        let syscall = m.regs()[rv::SYSCALL_REG as usize];
        if syscall != rv::SYS_EXIT {
            return Err(Trap::NotAnExit { syscall }.into());
        }

        drop(planning);
        let replay = tracing::info_span!("Replay trace").entered();
        // Phase 2: table prefixes give every chunk a disjoint output range.
        let mut rows = first_rows;
        let padded = filler::filled(counts, &filler::solve(counts));
        for (table, rows) in rows.iter_mut().enumerate() {
            // Reserve padding too, so appending it never moves the recorded rows.
            rows.reserve_exact(padded[table] - rows.len());
            // Clearing the remaining pages here keeps replay workers from racing page faults.
            rows.resize_with(counts[table], Row::default);
        }
        let destinations = rows.each_mut().map(|rows| SendPtr(rows.as_mut_ptr()));
        parallel::for_each(chunks.len() - 1, |i| {
            // The first chunk is already recorded in its final table prefixes.
            let chunk = &chunks[i + 1];
            let words = chunk.memory.iter().map(|&(cell, value, _)| (cell, value)).collect();
            let mut machine = Machine::replay(p, chunk.pc, chunk.regs, words);
            let mut ticks: Vec<u64> = chunk.memory.iter().map(|&(_, _, prev)| prev).collect();
            let mut reg_ticks = Cells {
                last: chunk.reg_ts.clone(),
            };
            let mut written = [0; crate::tables::N_TABLES];
            let n: usize = chunk.counts.iter().sum();
            for j in 0..n {
                // A successful planning walk guarantees this exact replay cannot trap.
                let step = machine.step().expect("planned chunk replays");
                let table = crate::tables::table_of(p.entries[step.index].class).expect("executed class has a table");
                let row = record_step(p, step, chunk.ts + j as u64 * CYCLE, &mut reg_ticks, |cell, at| {
                    // Every first-access snapshot remains present throughout replay.
                    let index = chunk
                        .memory
                        .binary_search_by_key(&cell, |&(cell, _, _)| cell)
                        .expect("recorded cell");
                    std::mem::replace(&mut ticks[index], at)
                });
                // Keep the store within its assigned prefix, even if replay invariants fail.
                assert!(written[table] < chunk.counts[table]);
                // SAFETY: prefix counts partition each table into disjoint chunk ranges.
                // The initialized row slots remain alive until all workers return.
                unsafe {
                    *destinations[table].add(chunk.offsets[table] + written[table]) = row;
                }
                written[table] += 1;
            }
            // Exact counts also ensure every output slot receives one complete row.
            assert_eq!(written, chunk.counts);
        });

        drop(replay);
        self.finish(m, regs, ram, adv_init, rows, ts)
    }

    /// Record directly when there is only one worker, then append zero-clock padding.
    fn execute_serial(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let max = 1 << p.log_advice;
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        let mut m = Machine::new(p, advice);
        let adv_init: Vec<F64> = m.advice().iter().map(|&w| F64(w)).collect();
        let mut regs = Cells::new(1 << LOG_REGS);
        // RAM's cells, then the advice's, as the machine numbers them.
        let mut ram = Cells::new((1 << p.log_ram) + (1 << p.log_advice));
        let mut rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // The clock starts on cycle 1, so that the first access comes strictly after the seeds.
        let mut ts = CLOCK_START;
        while !m.halted() {
            // The cycle count must not carry into the live bit, and the run's final clock is one cycle past its last row.
            if ts >> crate::tables::SLOT_BITS & MAX_CYCLES == MAX_CYCLES {
                return Err(ProveError::TooLong);
            }
            let step = m.step()?;
            let table = crate::tables::table_of(p.entries[step.index].class).expect("executed class has a table");
            // The serial path uses the same row binding against dense timestamp storage.
            rows[table].push(record_step(p, step, ts, &mut regs, |cell, at| ram.access(cell, at)));
            ts += CYCLE;
        }
        self.finish(m, regs, ram, adv_init, rows, ts)
    }

    /// Close the live memory boundary before appending inert zero-clock rows.
    fn finish(
        &self,
        m: Machine<'_>,
        regs: Cells,
        ram: Cells,
        adv_init: Vec<F64>,
        mut rows: [Vec<Row>; crate::tables::N_TABLES],
        ts: u64,
    ) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let syscall = m.regs()[rv::SYSCALL_REG as usize];
        if syscall != rv::SYS_EXIT {
            return Err(Trap::NotAnExit { syscall }.into());
        }
        let output = rv::OUTPUT_REGS.map(|r| m.regs()[r as usize]);
        let base_counts: [usize; crate::tables::N_TABLES] = std::array::from_fn(|t| rows[t].len());

        // The padding rows, written out rather than executed: they sit at clock zero
        // and touch nothing, every read holding zero and every write rewriting what it
        // writes (`filler`). Their circuit instances are honest ones, on those zeros.
        //
        // Why: an access in slot `k` pushes the timestamp `0 ^ k`, so it pulls that
        // same timestamp, and the two tuples cancel.
        let padding_prev: [Vec<u64>; crate::tables::N_TABLES] =
            std::array::from_fn(|t| CLASSES[t].slots().into_iter().map(u64::from).collect());
        for (first, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
            for _ in 0..traversals {
                for index in first..=first + size {
                    let e = &p.entries[index];
                    let table = crate::tables::table_of(e.class).expect("a fill block's class has a table");
                    let (out, taken, access) = compute(e, 0, 0, 0);
                    let slots = &padding_prev[table];
                    let mut prev = [0; 4];
                    let hash = (e.class == Class::Hash).then(|| {
                        // The compression of a zero block, whose result the row rewrites.
                        let mut h = rv::machine::compute_hash([0; hash::WORDS], 0, e.flags);
                        h.block[hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
                        let mut all = [0; 2 + hash::WORDS];
                        all.copy_from_slice(slots);
                        Box::new(HashRow {
                            block: h.block,
                            out: h.out,
                            prev: all,
                        })
                    });
                    if hash.is_none() {
                        prev[..slots.len()].copy_from_slice(slots);
                    }
                    rows[table].push(Row {
                        index: index as u32,
                        ts: 0,
                        v1: 0,
                        v2: 0,
                        out,
                        taken,
                        vd_old: if e.link { p.pc_of(index) + 4 } else { out },
                        ram: access,
                        prev,
                        hash,
                    });
                }
            }
        }

        let cycles = rows.iter().map(Vec::len).sum();
        let ram_last = ram.timestamps();
        let (ram_ts, adv_ts) = ram_last.split_at(1 << p.log_ram);
        let trace = Trace {
            rows,
            reg_fin: m.regs().iter().map(|&r| F64(r)).collect(),
            reg_ts: regs.timestamps(),
            ram_fin: m.ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init,
            adv_fin: m.advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::{A0, A1, Asm, T0, T1, T2, ZERO};
    use proptest::prelude::*;

    /// Compare every trace word and packed circuit witness against direct recording.
    fn equal(program: &Program, advice: &[u64], chunk_rows: usize) {
        // Compare every row field and dense boundary before witness construction.
        let serial = program.execute_serial(advice).expect("fixture exits");
        let replay = program.execute_chunks(advice, chunk_rows).expect("fixture replays");
        assert_eq!(serial.output, replay.output);
        assert_eq!(serial.base_counts, replay.base_counts);
        assert_eq!(serial.cycles, replay.cycles);
        assert_eq!(serial.trace, replay.trace);

        // Committed field words must also match, including circuit witness packing.
        let serial = program.build(&serial);
        let replay = program.build(&replay);
        assert_eq!(&*serial.q, &*replay.q);
    }

    /// Exercise aliased registers and overlapping memory writes in both regions.
    fn memory_program(rounds: u64, permutation: u64, image: Vec<u64>) -> Program {
        // XOR block addressing permits every word-aligned permutation of sixteen words.
        let text = Asm::new()
            .li(T0, RAM_BASE + 8 * permutation)
            .li(T1, ADVICE_BASE + 8 * permutation)
            .li(T2, rounds)
            .label("loop")
            .load("ld", A0, 0, T1)
            .r("add", A0, A0, A0)
            .store("sd", A0, 0, T1)
            .store("sb", A0, 1, T0)
            .blake2s(T0, A0, true)
            .blake2s(T1, A0, false)
            .load("ld", A1, 0, T0)
            .i("addi", T2, T2, -1)
            .branch("bne", T2, ZERO, "loop")
            .exit()
            .finish();
        // Both regions hold a full block even when its base permutes the word order.
        Program::new(&text, rv::TEXT_BASE, image, 4, 4).unwrap()
    }

    #[test]
    fn chunk_boundaries_preserve_aliases_advice_and_hashes() {
        // Fixture: reads alias their destination, RAM is rewritten, advice is mutable.
        let program = memory_program(7, 1, vec![1; 16]);
        // Move the boundary through every register, subword and permuted hash access.
        for chunk_rows in [1, 2, 3, 7, 16, 64] {
            equal(&program, &[3], chunk_rows);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn arbitrary_memory_and_chunk_sizes_replay_exactly(
            image in any::<[u64; 16]>(),
            advice in any::<[u64; 16]>(),
            rounds in 1u64..13,
            permutation in 0u64..16,
            chunk_rows in prop_oneof![Just(1usize), Just(2usize), Just(16usize), 1usize..65],
        ) {
            // Arbitrary words reach carries, subword stores and both hash finalization modes.
            let program = memory_program(rounds, permutation, image.to_vec());
            // Bias boundaries toward single rows and a complete sixteen-word hash block.
            equal(&program, &advice, chunk_rows);
        }
    }

    #[test]
    fn every_guest_has_identical_trace_and_committed_columns() {
        // Small fixtures cover all guest runtimes without duplicating end-to-end proofs.
        let guests: [(&[u8], &[u64]); 5] = [
            (include_bytes!("../../../../programs/fibonacci/fibonacci.elf"), &[90]),
            (include_bytes!("../../../../programs/blake2s/blake2s.elf"), &[150]),
            (include_bytes!("../../../../programs/hash/hash.elf"), &[1000]),
            (include_bytes!("../../../../programs/preimage/preimage.elf"), &[9, 7, 8]),
            (
                include_bytes!("../../../../programs/numbers/numbers.elf"),
                &[3, 1, 2, 3],
            ),
        ];
        for (elf, advice) in guests {
            // A short replay chunk exercises many transitions inside compiled guest code.
            equal(&Program::from_elf(elf).unwrap(), advice, 257);
        }
        // The workload hosts supply valid signatures and a valid encoded blob.
        for (elf, advice) in [
            (leanxmss_host::ELF, leanxmss_host::batch(1).advice),
            (leansphincs_host::ELF, leansphincs_host::batch(1).advice),
            (leanda_host::ELF, leanda_host::blobs(1).advice),
        ] {
            equal(&Program::from_elf(elf).unwrap(), &advice, CHUNK_ROWS);
        }
    }

    #[test]
    fn a_full_chunk_and_a_one_row_tail_match_serial_recording() {
        // More than 2^16 rows exercise the production checkpoint size.
        let text = Asm::new()
            .li(T0, 30_000)
            .label("loop")
            .r("add", A0, A0, A0)
            .i("addi", T0, T0, -1)
            .branch("bne", T0, ZERO, "loop")
            .exit()
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 0, 0).unwrap();
        let serial = program.execute_serial(&[]).unwrap();
        let n = serial.base_counts.iter().sum::<usize>();
        // Put exit exactly at a chunk end, then in a one-row final chunk.
        for chunk_rows in [n, n - 1, CHUNK_ROWS] {
            let replay = program.execute_chunks(&[], chunk_rows).unwrap();
            assert_eq!(serial.trace, replay.trace);
        }
    }

    #[test]
    fn replay_planning_preserves_execution_errors() {
        // Invalid advice fails before allocation or dispatch.
        let text = Asm::new().exit().finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 0, 0).unwrap();
        assert!(matches!(
            program.execute_chunks(&[1, 2], 1),
            Err(ProveError::AdviceTooLong { max: 1, got: 2 })
        ));
        // A bad syscall and an instruction falling off text retain their ISA failures.
        for text in [vec![rv::asm::ECALL], vec![0x13]] {
            let program = Program::new(&text, rv::TEXT_BASE, vec![], 0, 0).unwrap();
            let serial = program.execute_serial(&[]).err().unwrap();
            let replay = program.execute_chunks(&[], 1).err().unwrap();
            assert_eq!(serial, replay);
        }
    }
}
