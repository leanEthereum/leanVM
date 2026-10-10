//! A program as the proof sees it: the decoded program, its fill blocks, and the digest of its public statement.
//!
//! It runs, is proven, and is verified against its digest.

use super::batch::{Batch, FormPowers};
use super::deferred::DeferredClaims;
use super::error::{CpuError, ProveError, VerifyError};
use super::execute::{Execution, Recorder, RowCounter, TraceBuilder};
use super::filler::{FillBlocks, Plan};
use super::layout::{Announcement, Log, Lookup, ProgramView, Schema, Sizes, regions};
use super::reduce::TableClaims;
use super::witness::Witness;
use super::{Output, Proof};
use crate::class_flock::FlockId;
use crate::constraints::{Claims, Columns};
use crate::memory::MAX_CHUNKS;
use crate::memory::{self, LinkShare, LogOpening};
use crate::pcs::{Committed, Rate};
use crate::rv::{ElfError, Guest, Machine, ProgramError, Region, RiscvProgram};
use crate::tables::{ClassTable, PerTable, TableId};
use crate::{constraints, leaf};
use fiat_shamir::arith::Native;
use fiat_shamir::transcript::{Challenger, ProverState, RawProof, Transmitter, VerifierState};
use flock::reduction;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use std::cmp::Reverse;
use tracing::info_span;

/// A validated program, its fill blocks, and the digest of everything public about it.
///
/// The decoded program is read-only, so the digest always describes what is proven.
#[derive(Clone)]
pub struct Program {
    /// The decoded program, the fill blocks appended to its text.
    pub(super) rv: RiscvProgram,
    /// The digest of the public statement, which seeds the transcript.
    pub(super) digest: [u8; 32],
    /// Where each fill block sits in the text.
    pub(super) filler: FillBlocks,
}

// Why: the digest reads tables of words as bytes, which is their little-endian image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// The domain separator of the digest, versioned with the statement's format.
    const DIGEST_DOMAIN: &'static [u8] = b"leanvm-rv64im-13";

    /// The cycles between two checks of a running trace against one commitment.
    const SIZE_CHECK_PERIOD: u64 = 1 << 16;

    /// The program of a guest's ELF executable.
    ///
    /// # Errors
    ///
    /// Refuses a file that is no guest, or whose text and RAM form no program.
    pub fn from_elf(elf: &[u8]) -> Result<Self, ElfError> {
        let guest = Guest::from_elf(elf)?;
        Self::new(
            &guest.text,
            guest.entry_pc,
            guest.image,
            guest.log_ram,
            guest.log_advice,
        )
        .map_err(ElfError::Program)
    }

    /// Whether a text of this many words fits the text region once its appended words are added.
    ///
    /// The appended words are the illegal word, the fill blocks, then the illegal slot and the halt slot.
    fn text_fits(words: usize) -> bool {
        words
            .checked_add(1 + FillBlocks::WORDS + 2)
            .and_then(usize::checked_next_power_of_two)
            .is_some_and(|total| total <= 1 << Region::TEXT.max_log_words())
    }

    /// The program of instruction words, an entry point, a RAM image and the memory sizes.
    ///
    /// The text gets an illegal word, then the fill blocks.
    ///
    /// # Errors
    ///
    /// Refuses an entry outside the supplied text, and sizes exceeding the machine's regions.
    pub fn new(
        text: &[u32],
        entry_pc: u64,
        image: Vec<u64>,
        log_ram: usize,
        log_advice: usize,
    ) -> Result<Self, ProgramError> {
        // Check the shape on the supplied text, before anything is appended to it.
        RiscvProgram::validate(text.len(), entry_pc, image.len(), log_ram, log_advice)?;

        if !Self::text_fits(text.len()) {
            return Err(ProgramError::TextTooLarge);
        }

        // A run falling off the program's own text must trap, not slide into a fill block.
        let mut text = text.to_vec();
        text.push(0);
        let filler = FillBlocks::append(&mut text);
        let rv = RiscvProgram::new(&text, entry_pc, image, log_ram, log_advice)?;
        let view = ProgramView { rv: &rv, fill: &filler };
        if regions(&rv).chunks() > MAX_CHUNKS {
            return Err(ProgramError::MemoryTooLarge);
        }
        let digest = Self::digest_of(&view);
        Ok(Self { digest, rv, filler })
    }

    /// Run the program on `advice`, recording every row, then write out the padding rows.
    ///
    /// The padding rows bring each table to a power of two.
    ///
    /// # Errors
    ///
    /// Refuses more advice than the program's region holds, a run that traps, and one too long for one proof.
    #[doc(hidden)]
    pub fn execute(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let mut m = self.machine(advice)?;
        let mut trace = TraceBuilder::new(p, regions(p), m.memory().advice());
        self.run(&mut m, &mut trace)?;
        let output = m.output()?;

        // The padding rows, written out rather than executed.
        let base_counts = trace.row_counts();
        for (first, size, traversals) in self.filler.cycles(&Plan::solve(base_counts)) {
            for _ in 0..traversals {
                for index in first..=first + size {
                    trace.pad(p, index);
                }
            }
        }

        let trace = trace.finish();
        let proven_rows = trace.rows.values().map(Vec::len).sum();
        Ok(Execution {
            output,
            proven_rows,
            base_counts,
            trace,
        })
    }

    /// The machine about to run the program on `advice`.
    fn machine(&self, advice: &[u64]) -> Result<Machine<'_>, ProveError> {
        let max = 1 << self.rv.log_advice();
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        Ok(Machine::new(&self.rv, advice))
    }

    /// Run `m` to its halt, handing every step to `recorder`.
    ///
    /// Every so many cycles the rows so far are checked against one commitment.
    ///
    /// So a run too long for one proof is refused while it runs, before its trace outgrows memory.
    #[inline(always)]
    fn run<R: Recorder>(&self, m: &mut Machine<'_>, recorder: &mut R) -> Result<(), ProveError> {
        // The heights last checked: the stack grows only when one of them does.
        let mut checked = (PerTable::default(), [0; 2]);
        let mut cycle = 0u64;
        while !m.halted() {
            if cycle.is_multiple_of(Self::SIZE_CHECK_PERIOD) {
                let counts = recorder.row_counts();
                let heights = PerTable::from_fn(|t: TableId| t.spec().provable_height(counts[t]));
                let logs = recorder.live().map(Log::log_rows);
                if (heights, logs) != checked {
                    self.committed_size(heights, recorder.live())?;
                    checked = (heights, logs);
                }
            }
            let step = m.step()?;
            recorder.record(&self.rv, m, step);
            cycle += 1;
        }
        Ok(())
    }

    /// The statistics a proof of this run would report, from one execution and no proof.
    ///
    /// The run counts its rows without recording them, and the fill plan gives the heights they are proven at.
    ///
    /// # Errors
    ///
    /// What would refuse the proof itself, the rate aside.
    pub fn measure(&self, advice: &[u64]) -> Result<Stats, ProveError> {
        let mut m = self.machine(advice)?;
        let mut counter = RowCounter::new(&self.rv);
        self.run(&mut m, &mut counter)?;
        m.output()?;
        let base_counts = counter.row_counts();
        let counts = Plan::solve(base_counts).filled(base_counts);
        Ok(Stats {
            proven_rows: counts.values().sum(),
            counts,
            base_counts,
            committed: self.committed_size(counts, counter.live())?,
            live: counter.live(),
        })
    }

    /// Prove a finished run, which a test may have forged.
    pub(super) fn prove_execution(&self, exec: &Execution, rate: Rate) -> (Proof, Stats) {
        let w = info_span!("Build witness").in_scope(|| Witness::build(self, exec));
        let stats = Stats {
            proven_rows: exec.proven_rows,
            counts: w.layout.taus.map(|t| 1usize << t),
            base_counts: exec.base_counts,
            committed: w.committed_size(),
            live: w.logs.each_ref().map(|log| log.live),
        };
        (self.prove_witness(w, Output::new(exec.output), rate), stats)
    }

    /// Prove a built witness, which a test may have forged.
    ///
    /// # Panics
    ///
    /// Panics if the witness's bus does not balance: an honest run's always does.
    fn prove_witness(&self, w: Witness, output: Output, rate: Rate) -> Proof {
        // The public statement, the program's digest and the output, seeds the transcript.
        let mut ps = ProverState::new(self.fs_seed(), output.words().map(F64));

        // Announce the sizes, then commit, before any challenge.
        let announcement = Announcement {
            taus: w.layout.taus,
            logs: w.layout.logs.each_ref().map(|log| log.log_rows),
            rate,
            live: w.logs.each_ref().map(|log| log.live as u64),
        };
        announcement.write(&mut ps);
        let committed = info_span!("Commit")
            .in_scope(|| Committed::new(&mut ps, &w.q, w.layout.shape, rate).expect("the witness matches its layout"));

        // The bus, then the linear tables' columns at its point, then the one batch over the other tables and the
        // producers, all reading the stack's windows in place.
        let spans = &Schema::get().spans;
        let (bus_claims, table_claims, shares) = {
            let l = &w.layout;
            let cols = w.columns();
            let logs = |weights: &[F192], beta: F192| {
                (l.logs.iter().zip(&w.logs))
                    .map(|(shape, log)| memory::leaves(shape, log, weights, beta))
                    .collect()
            };
            let pull = l.pull_closed(w.logs.each_ref().map(|log| log.live));
            let mut bus = info_span!("Prove bus").in_scope(|| {
                leaf::prove_balance(
                    &l.push,
                    &pull,
                    &l.producers,
                    l.grinding,
                    &cols,
                    logs,
                    spans.as_slice(),
                    &mut ps,
                )
            });
            // A settled table's columns at the bus point, short of its register numbers, which the batch folds.
            let settled: Vec<Claims> = (ClassTable::all().iter())
                .filter(|(_, table)| table.settled_at_bus())
                .map(|(t, table)| {
                    let registers = table.summed_columns();
                    let evals = &bus.evals[t.index()];
                    (evals.iter().enumerate())
                        .filter(|(c, _)| !registers.contains(c))
                        .for_each(|(_, &e)| ps.add_scalar(e));
                    Claims {
                        chi: bus.point[..l.taus[t]].to_vec(),
                        evals: evals.clone(),
                        slices: Vec::new(),
                    }
                })
                .collect();
            let summed = info_span!("Prove constraints").in_scope(|| {
                let producers = std::mem::take(&mut bus.producers);
                let coefficients: Vec<Vec<F192>> = producers.iter().map(|p| p.coefficients.clone()).collect();

                // The batch's eq point is the bus's, which lets it settle the bus forms alongside the constraints.
                let powers = FormPowers::new(&mut Native, ps.sample());
                let mut sums = powers.table_sums(&bus);
                sums.extend(producers.iter().map(|p| powers.push() * p.sigma));

                // The tables' summed columns in the field they are committed in, then the producers' lifted columns.
                let table_cols = (ClassTable::all().values().zip(spans.values()))
                    .map(|(table, &(base, _))| {
                        Columns::K(table.summed_columns().iter().map(|&c| cols[base + c]).collect())
                    })
                    .chain(producers.into_iter().map(|p| Columns::E(p.columns)))
                    .collect();
                let batch = Batch::new(l, &bus.forms, &coefficients, &bus.weights, bus.beta, powers);
                constraints::prove(batch.airs(), table_cols, &bus.point, &sums, &mut ps)
            });
            let shares = (bus.logs.into_iter())
                .map(|share| LinkShare {
                    point: share.point,
                    value: share.value,
                    weights: bus.weights.clone(),
                    beta: bus.beta,
                })
                .collect::<Vec<_>>();
            (bus.claims, TableClaims::new(settled, summed), shares)
        };
        let l = &w.layout;

        // Each memory log's argument, from its share of the bus, then the program claim's batching challenge.
        let logs: Vec<LogOpening<F192>> = info_span!("Prove memory").in_scope(|| {
            (l.logs.iter().zip(&w.logs).zip(&shares))
                .map(|((shape, log), share)| memory::prove(&mut ps, shape, log, share))
                .collect()
        });
        ps.sample();
        let slots = l.opening_claims(bus_claims, &table_claims.columns, &logs);

        // Flock's reductions, batched over every table's circuit under shared challenges.
        //
        // Each circuit leaves a validity claim on its packed witness, discharged in the same opening through a ring-switched region.
        // Each producer's multiplicity column is a ring-switched region too.
        let reductions = w.reductions;
        let slices = info_span!("Flock reductions").in_scope(|| {
            let instances: Vec<reduction::Instance<'_>> = (FlockId::ALL.into_iter().zip(&reductions))
                .map(|(f, tables)| {
                    let window = l.witness_window(f);
                    let column = &w.q[window.offset..window.offset + (1 << window.n_vars)];
                    f.instance(column, l.taus[f.table()], tables)
                })
                .collect();
            reduction::prove(&instances, &mut ps)
        });
        drop(reductions);
        let rings = l.rings(slices, &table_claims.producers, &table_claims.summed, &logs, F192::ZERO);
        info_span!("PCS open").in_scope(|| {
            committed
                .open(&mut ps, &w.q, &slots, &rings)
                .expect("opening uses the committed witness");
        });
        Proof(ps.into_proof())
    }

    /// Check that the proof shows this program, run on some advice, exiting with this output.
    ///
    /// It takes only public inputs, never the prover's witness.
    ///
    /// It is the verifier's core, then the settlement of the claims the core leaves.
    ///
    /// # Errors
    ///
    /// The proof is not one of this program and this output.
    #[tracing::instrument(name = "Verify", skip_all)]
    pub fn verify(&self, output: Output, proof: &Proof) -> Result<(), VerifyError> {
        let claims = self.verify_core(output, proof)?;
        Ok(self.check_deferred(&claims)?)
    }

    /// Verify a proof and expand its Merkle paths for recursion.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    #[tracing::instrument(name = "Verify", skip_all)]
    #[doc(hidden)]
    pub fn verify_to_raw(&self, output: Output, proof: &Proof) -> Result<RawProof, CpuError> {
        let (claims, raw) = self.replay(output, proof)?;
        self.check_deferred(&claims)?;
        Ok(raw)
    }

    /// The verifier's core: every check that depends on the proof.
    ///
    /// It returns the claims the proof leaves on polynomials only the program or the VM's circuits fix.
    /// A proof verifies exactly when the core accepts it and its claims are settled.
    /// A caller may settle them later, but never skip them.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    #[doc(hidden)]
    pub fn verify_core(&self, output: Output, proof: &Proof) -> Result<DeferredClaims, CpuError> {
        self.replay(output, proof).map(|(claims, _)| claims)
    }

    /// The verifier's core, and the proof it replayed with its Merkle paths written out.
    #[tracing::instrument(name = "Verify core", skip_all)]
    fn replay(&self, output: Output, proof: &Proof) -> Result<(DeferredClaims, RawProof), CpuError> {
        // The public statement seeds the transcript, as on the prover's side.
        let mut vs = VerifierState::new(self.fs_seed(), &proof.0, output.words().map(F64));

        // The announced sizes, then the layout they describe, then the core.
        let announcement = Announcement::read(&mut vs)?;
        let l = announcement.layout(&self.view())?;
        let live = (l.logs.iter().zip(announcement.live))
            .map(|(shape, live)| memory::live_bits(live as usize, shape.log_rows));
        let live: Vec<Vec<F192>> = live.collect();
        let output = output.words().map(|o| F192::from(F64(o)));
        let claims = l.verify_core(&mut vs, [&live[0], &live[1]], &output, announcement.rate)?;
        Ok((claims, vs.into_raw_proof()))
    }

    /// The decoded text, memory image and region sizes.
    #[doc(hidden)]
    pub const fn rv(&self) -> &RiscvProgram {
        &self.rv
    }

    /// The program as the layout reads it: its decoded text and its fill blocks.
    pub(crate) const fn view(&self) -> ProgramView<'_> {
        ProgramView {
            rv: &self.rv,
            fill: &self.filler,
        }
    }

    /// BLAKE2s over the decoded text, the entry and halt addresses, the region sizes and the initial RAM image.
    ///
    /// ELF metadata is no part of it, and every illegal encoding decodes to the same entry.
    #[doc(hidden)]
    pub const fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The transcript's seed: the digest, as words.
    ///
    /// Every challenge depends on it, and the run's public output seeds the transcript beside it.
    #[doc(hidden)]
    pub fn fs_seed(&self) -> [F64; 4] {
        fiat_shamir::digest_words(&self.digest)
    }

    /// The committed size of a run making these rows per table, each table taken at its provable height.
    ///
    /// The layout depends on the program and the heights alone, so no witness is built.
    ///
    /// # Why one check for a run in progress and a finished one
    ///
    /// - Rows only accumulate, and the fill only raises a table to a provable height.
    /// - So the heights of a run in progress never exceed those it finishes at, nor does its stack.
    /// - A run refused mid-way would therefore be refused at its end.
    ///
    /// # Errors
    ///
    /// Refuses a stack larger than one commitment.
    pub(super) fn committed_size(&self, row_counts: PerTable<usize>, live: [usize; 2]) -> Result<usize, ProveError> {
        let taus = PerTable::from_fn(|t: TableId| crate::log2_strict_usize(t.spec().provable_height(row_counts[t])));
        let (placements, shape) = Sizes::of(&self.view(), live.map(Log::log_rows)).stack(&taus);
        if shape.mu > crate::pcs::MAX_MU {
            return Err(ProveError::TooLong);
        }
        Ok(crate::witness::committed_len(&placements))
    }

    /// The digest of `rv`'s public statement.
    ///
    /// Every variable-length part is length-framed, so the preimage parses one way.
    fn digest_of(view: &ProgramView<'_>) -> [u8; 32] {
        let rv = view.rv;
        let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let table = Lookup::Bytecode.table(view);
        let table_bytes: Vec<u8> = table.iter().flat_map(|w| w.0.to_le_bytes()).collect();

        // The domain, the bytecode table, then the scalars and the image.
        let mut h = Hasher::new();
        h.update(Self::DIGEST_DOMAIN);
        h.update(&bytes(&[table.len() as u64]));
        h.update(&table_bytes);
        h.update(&bytes(&[
            rv.entry_pc(),
            rv.halt_pc(),
            rv.log_ram() as u64,
            rv.log_advice() as u64,
            rv.image().len() as u64,
        ]));
        h.update(&bytes(rv.image()));
        h.finalize()
    }
}

/// What a run costs: its rows per table, and its committed witness size.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stats {
    /// The rows proven, padding rows included.
    pub proven_rows: usize,
    /// The rows per table as proven: each a power of two, the fill blocks having filled them.
    pub counts: PerTable<usize>,
    /// The rows per table before that filling: the work the program itself does.
    pub base_counts: PerTable<usize>,
    /// The committed witness size: the columns' total length, before the stack's zero pad.
    pub committed: usize,
    /// The memory logs' live rows: the cycles, then the memory accesses.
    pub live: [usize; 2],
}

impl Stats {
    /// The cycles the run took: one row per instruction it executed, before any padding.
    #[must_use]
    pub fn cycles(&self) -> usize {
        self.base_counts.values().sum()
    }

    /// One line of per-table counts and shares, largest first, then the committed size.
    ///
    /// The counts are the program's own work: the proven counts are all powers of two, which say nothing of it.
    ///
    /// Tables with no rows are left out.
    #[must_use]
    pub fn details(&self) -> String {
        if self.proven_rows == 0 {
            return "-".to_string();
        }

        // Each table's share of the program's own rows, largest first.
        let base_cycles = self.cycles();
        let mut shares: Vec<(&str, usize)> = (self.base_counts.iter())
            .filter(|&(_, &c)| c > 0)
            .map(|(t, &c)| (t.name(), c))
            .collect();
        shares.sort_unstable_by_key(|&(_, c)| Reverse(c));
        let mut parts: Vec<String> = shares
            .iter()
            .map(|&(name, c)| {
                let pct = 100.0 * c as f64 / base_cycles as f64;
                format!("{name} 2^{} ({pct:.1}%)", primitives::pretty_f64((c as f64).log2()))
            })
            .collect();

        // The committed size, as a power of two.
        let log2 = |n: usize| primitives::pretty_f64((n.max(1) as f64).log2());
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::execute::Row;
    use crate::cpu::layout::{Framework, Shared};
    use crate::leaf::Coord;
    use crate::leaf::tests::unmatched_leaves;
    use crate::memory::{self, LogWitness};
    use crate::pcs::Rate;
    use crate::rv::asm::*;
    use crate::rv::semantics::Outcome;
    use crate::rv::{Alu, Class, Ext, Machine, ProgramError, Reg, Trap};
    use crate::tables::Separator;
    use primitives::field::g_pow;
    use std::panic::AssertUnwindSafe;

    #[test]
    fn construction_refuses_an_entry_or_a_size_out_of_range() {
        // An entry point outside the one-word text, misaligned, or in what is appended to it.
        let text = [0x0000_0073];
        for entry in [
            0,
            Region::TEXT.base() + 2,
            Region::TEXT.base() + 4,
            Region::TEXT.base() + 8,
            u64::MAX,
        ] {
            assert!(matches!(
                Program::new(&text, entry, vec![], 0, 0),
                Err(ProgramError::EntryPoint)
            ));
        }

        // An empty text has no entry point at all.
        assert!(matches!(
            Program::new(&[], Region::TEXT.base(), vec![], 0, 0),
            Err(ProgramError::EntryPoint)
        ));

        // An image larger than RAM, RAM or the advice beyond its region.
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![0, 0], 0, 0),
            Err(ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![], usize::MAX, 0),
            Err(ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![], 0, usize::MAX),
            Err(ProgramError::AdviceSize)
        ));
    }

    #[test]
    fn the_text_region_reserves_the_fill_blocks() {
        // The largest text that fits, after the illegal word, the fill blocks, and the two slots `rv` appends.
        //
        // Building a program that large takes gigabytes, so the boundary is checked on lengths.
        let limit = (1 << Region::TEXT.max_log_words()) - 1 - FillBlocks::WORDS - 2;
        assert!(Program::text_fits(limit));
        assert!(!Program::text_fits(limit + 1));

        // A text one word too long is refused before anything is built.
        let too_long = Program::new(&vec![0; limit + 1], Region::TEXT.base(), vec![], 0, 0);
        assert!(matches!(too_long, Err(ProgramError::TextTooLarge)));
    }

    #[test]
    fn illegal_encodings_share_one_identity() {
        // Two different illegal words decode to the same entry, so to the same digest.
        let program = Program::new(&[0], Region::TEXT.base(), vec![], 0, 0).unwrap();
        let same = Program::new(&[u32::MAX], Region::TEXT.base(), vec![], 0, 0).unwrap();
        assert_eq!(program.digest(), same.digest());

        // Running it traps on the first instruction.
        assert_eq!(
            Machine::new(program.rv(), &[]).run_for(1),
            Err(Trap::Illegal {
                pc: Region::TEXT.base()
            })
        );
    }

    #[test]
    fn the_digest_binds_every_public_component() {
        // Fixture: `a0 = 5; exit`, a one-word image, RAM of 4 words, no advice.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![1], 2, 0).expect("a valid program");
        assert_eq!(program.digest(), program.clone().digest());

        // Mutation: change one component at a time.
        //
        //     the text, the entry point, the image's value, the image's length, RAM's size, the advice's size
        let mut changed_text = text.clone();
        changed_text[0] = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 6).finish()[0];
        let changed = [
            Program::new(&changed_text, Region::TEXT.base(), vec![1], 2, 0),
            Program::new(&text, Region::TEXT.base() + 4, vec![1], 2, 0),
            Program::new(&text, Region::TEXT.base(), vec![2], 2, 0),
            Program::new(&text, Region::TEXT.base(), vec![1, 0], 2, 0),
            Program::new(&text, Region::TEXT.base(), vec![1], 3, 0),
            Program::new(&text, Region::TEXT.base(), vec![1], 2, 1),
        ];
        for changed in changed {
            assert_ne!(program.digest(), changed.expect("a valid program").digest());
        }
    }

    /// The leaves a witness's bus leaves unmatched, as `(side, block, row)`.
    ///
    fn unmatched(w: &Witness) -> Vec<(&'static str, usize, usize)> {
        let l = &w.layout;
        let pull = l.pull_closed(w.logs.each_ref().map(|log| log.live));
        unmatched_leaves(&l.push, &pull, &l.producers, &w.columns(), |weights, beta| {
            (l.logs.iter().zip(&w.logs))
                .map(|(shape, log)| memory::leaves(shape, log, weights, beta))
                .collect()
        })
    }

    /// The tuples a run leaves unmatched, as `(side, block, row)`.
    fn unmatched_run(program: &Program, exec: &Execution) -> Vec<(&'static str, usize, usize)> {
        unmatched(&Witness::build(program, exec))
    }

    /// The prover refuses a witness whose bus does not balance: its two products differ.
    fn assert_unbalanced(program: &Program, w: Witness, output: Output) {
        let refused = std::panic::catch_unwind(AssertUnwindSafe(|| program.prove_witness(w, output, Rate::MIN)))
            .expect_err("an unbalanced bus was proven");
        let message = refused.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(
            message.contains("two products to agree"),
            "refused for another reason: {message}"
        );
    }

    /// The log row of a time or a position `g^j`: `j`.
    fn log_row(position: u64) -> usize {
        (0..1 << 20).find(|&j| g_pow(j).0 == position).expect("a live position")
    }

    /// Make a log's row `j` write `forged` where it wrote `honest`, every later read of the cell following it.
    fn rewrite(log: &mut LogWitness, j: usize, honest: u64, forged: u64) {
        log.inc[j].0 ^= honest ^ forged;
    }

    /// The first row of the run among `rows`, past the padding rows at time zero.
    fn real(rows: &mut [Row]) -> &mut Row {
        rows.iter_mut().find(|r| r.time != 0).expect("a row of the run")
    }

    /// Extension-field products on packed elements: `x` at word 0, `y` at word 3, the base-field `w` at word 6, `c`
    /// at word 7, and `d` at word 10, so that limb addresses carry: `y`'s second limb is at `+32`, `c`'s at `+64`.
    ///
    /// ```text
    ///     extmul   c = x y             extmack  c = c + c w     (c is also a)
    ///     a0..a2 = c                   extmul   d = y y         (b is a, and nothing reads d)
    /// ```
    fn extension_products() -> Program {
        let mut image = vec![0; 13];
        image[..3].copy_from_slice(&[0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210, 0x0F1E_2D3C_4B5A_6978]);
        image[3..6].copy_from_slice(&[3, 1 << 63, 0x1B]);
        image[6] = 0xDEAD_BEEF_0BAD_F00D;
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T0, ram)
            .li(Reg::T1, ram + 24)
            .li(Reg::T2, ram + 48)
            .li(Reg::T3, ram + 56)
            .li(Reg::T4, ram + 80)
            .ext(Extmul, Reg::T3, Reg::T0, Reg::T1)
            .ext(Extmack, Reg::T3, Reg::T3, Reg::T2)
            .load(Ld, Reg::A0, 0, Reg::T3)
            .load(Ld, Reg::A1, 8, Reg::T3)
            .load(Ld, Reg::A2, 16, Reg::T3)
            .ext(Extmul, Reg::T4, Reg::T1, Reg::T1)
            .exit()
            .finish();
        Program::new(&text, Region::TEXT.base(), image, 4, 0).expect("valid instruction program")
    }

    /// `extmulk` of a = (3, 5, 7) at RAM's base by the base-field b = 9 right after it, into c after that.
    fn base_field_product() -> Program {
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T0, ram)
            .li(Reg::T1, ram + 24)
            .li(Reg::T2, ram + 32)
            .ext(Extmulk, Reg::T2, Reg::T0, Reg::T1)
            .exit()
            .finish();
        Program::new(&text, Region::TEXT.base(), vec![3, 5, 7, 9, 0, 0, 0], 3, 0).expect("valid instruction program")
    }

    /// The two families of loads and stores: the doubleword ones, whose value is a column, and the narrower ones, whose
    /// value is a circuit word. Each as `(store, load, their classes)`.
    const STORE_LOAD: [(StoreOp, LoadOp, [Class; 2]); 2] =
        [(Sd, Ld, [Class::Sd, Class::Ld]), (Sw, Lw, [Class::Store, Class::Load])];

    /// `t1 = 5` stored in RAM's fifth word then loaded into `a0`, run honestly, and its store's and load's tables.
    fn store_then_load(store: StoreOp, load: LoadOp, classes: [Class; 2]) -> (Program, Execution, [TableId; 2]) {
        let text = Asm::new()
            .li(Reg::T0, Region::RAM.base() + 32)
            .i(Addi, Reg::T1, Reg::ZERO, 5)
            .store(store, Reg::T1, 0, Reg::T0)
            .load(load, Reg::A0, 0, Reg::T0)
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 3, 0).expect("valid instruction program");
        let run = program.execute(&[]).unwrap();
        assert_eq!(run.output, [5, 0, 0, 0]);
        (program, run, classes.map(|c| TableId::of(c).unwrap()))
    }

    #[test]
    fn an_honest_run_balances() {
        // Invariant: every tuple a table pulls, a log or a producer pushes, and the bus names those left unmatched.
        //
        // Fixture state: an exit, a hash, each load and store family, extension products in both modes.
        let ram = Region::RAM.base();
        let exit = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let hash = Asm::new()
            .li(Reg::S0, ram)
            .li(Reg::S1, 64)
            .blake2s(Reg::S0, Reg::S1, true)
            .load(Ld, Reg::A0, 32, Reg::S0)
            .exit()
            .finish();
        let exit = Program::new(&exit, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let hash = Program::new(&hash, Region::TEXT.base(), vec![1; 16], 4, 0).expect("valid instruction program");
        let stores = STORE_LOAD.map(|(store, load, classes)| store_then_load(store, load, classes).0);
        let programs = [exit, hash, extension_products(), base_field_product()]
            .into_iter()
            .chain(stores);
        for program in programs {
            let unmatched = unmatched_run(&program, &program.execute(&[]).unwrap());
            assert!(unmatched.is_empty(), "unmatched (side, block, row): {unmatched:?}");
        }
    }

    #[test]
    fn a_run_too_long_for_one_proof_is_refused_while_it_runs() {
        // Fibonacci for 2^63 steps: only the size check stops it.
        let text = Asm::new()
            .li(Reg::A0, 0)
            .li(Reg::A1, 1)
            .li(Reg::T0, 1 << 63)
            .label("loop")
            .r(Add, Reg::A2, Reg::A0, Reg::A1)
            .i(Addi, Reg::A0, Reg::A1, 0)
            .i(Addi, Reg::A1, Reg::A2, 0)
            .i(Addi, Reg::T0, Reg::T0, -1)
            .branch(Bne, Reg::T0, Reg::ZERO, "loop")
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        assert_eq!(program.measure(&[]), Err(ProveError::TooLong));

        // The run stops before its rows outnumber the words of one commitment.
        let mut m = program.machine(&[]).unwrap();
        let mut counter = RowCounter::new(&program.rv);
        assert_eq!(program.run(&mut m, &mut counter), Err(ProveError::TooLong));
        let (counts, live) = (counter.row_counts(), counter.live());
        let rows: usize = counts.values().sum();
        assert!(rows < 1 << crate::pcs::MAX_MU, "{rows} rows counted");
        assert_eq!(program.committed_size(counts, live), Err(ProveError::TooLong));

        // A period earlier, no table had more than these rows, and they fit.
        let period = Program::SIZE_CHECK_PERIOD as usize;
        let earlier = counts.map(|c| c.saturating_sub(period));
        assert!(
            program
                .committed_size(earlier, live.map(|l| l.saturating_sub(period)))
                .is_ok()
        );
    }

    #[test]
    fn only_ecall_can_terminate_the_state_channel() {
        // Fixture: `a0 = 42; exit`, and the same program with the exit replaced by `j halt`.
        let original = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 42).exit().finish();
        let honest_program = Program::new(&original, Region::TEXT.base(), vec![], 2, 0).expect("valid exit program");
        let halt = honest_program.rv.halt_pc();
        let exit_index = original.len() - 1;
        let pc = honest_program.rv.pc_of(exit_index);
        let mut text = original;
        text[exit_index] = Instruction::j(Reg::ZERO, (halt - pc) as i32).bits();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid jump program");
        assert!(matches!(program.execute(&[]), Err(ProveError::Trap(Trap::Illegal { pc })) if pc == halt));

        // Mutation: the exit's row becomes the jump's, bypassing the interpreter's trap; it writes its link to the sink.
        let mut execution = honest_program.execute(&[]).unwrap();
        let row = (execution.trace.rows[TableId::ALU].iter_mut())
            .find(|r| r.index as usize == exit_index)
            .unwrap();
        let honest = std::mem::replace(&mut row.out, pc + 4);
        let cycle = log_row(row.time);
        rewrite(&mut execution.trace.registers, cycle, honest, pc + 4);

        // The jump is not the exit: the final state is left, and the jump's push of a state no row pulls.
        let witness = Witness::build(&program, &execution);
        let unmatched = unmatched(&witness);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(
            unmatched.contains(&("pull", Framework::State as usize, 0)),
            "{unmatched:?}"
        );
        assert_unbalanced(&program, witness, execution.output.into());
    }

    /// The jump's column on the ALU's state push, `pc + 4` plus the jump: a port of its class circuit.
    fn jump_column() -> usize {
        let alu = TableId::ALU;
        let push = alu.class_table().flushes().push.swap_remove(0);
        let Coord::Sum(terms) = &push[1] else {
            panic!("pc + 4 plus the jump")
        };
        let [_, Coord::Col(jump)] = terms[..] else {
            panic!("pc + 4 plus the jump")
        };
        Schema::get().spans[alu].0 + jump
    }

    /// Prove a forged run of `program` whose ALU jump at `row` is `value` on the bus alone, the circuit's witness keeping
    /// what its inputs give.
    ///
    /// The bus is unbalanced until that column is forged, and balanced after, so what refuses it is the verifier.
    fn forged_jump(program: &Program, forged: &Execution, row: usize, value: u64) -> CpuError {
        let mut w = Witness::build(program, forged);
        // The row's state push, and the next row's pull.
        let left = unmatched(&w);
        assert_eq!(left.len(), 2, "{left:?}");
        column_mut(&mut w, jump_column())[row] = F64(value);
        assert!(unmatched(&w).is_empty());
        let proof = program.prove_witness(w, forged.output.into(), Rate::MIN);
        program
            .verify_core(forged.output.into(), &proof)
            .expect_err("a forged successor is refused")
    }

    #[test]
    fn a_forged_branch_is_refused() {
        // Invariant: a row goes where its circuit decides, the bus carrying the circuit's jump, never a free column.
        //
        // Fixture: `bne x0, x0, skip; a0 = 1; skip: exit`, which never branches, and the same with `beq`, which does.
        let text = |op| {
            Asm::new()
                .branch(op, Reg::ZERO, Reg::ZERO, "skip")
                .i(Addi, Reg::A0, Reg::ZERO, 1)
                .label("skip")
                .exit()
                .finish()
        };
        let program = Program::new(&text(Bne), Region::TEXT.base(), vec![], 2, 0).expect("a valid program");
        let taken = Program::new(&text(Beq), Region::TEXT.base(), vec![], 2, 0).expect("a valid program");
        assert_eq!(program.execute(&[]).unwrap().output[0], 1);

        // Mutation: the run of `beq` as one of `bne`, which outputs a0 = 0, its circuit deciding not to branch.
        //
        // Its push names `pc + 4`, which the exit's pull does not meet, until the bus's jump is forged to the offset.
        let mut forged = taken.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = forged.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        forged.trace.rows[alu][row].taken = false;
        let error = forged_jump(&program, &forged, row, program.rv.dt_of(0));
        assert!(matches!(error, CpuError::Open(_)), "{error}");
    }

    #[test]
    fn a_forged_jalr_target_is_refused() {
        // Invariant: a `jalr` goes to the target its circuit computes from its register and immediate.
        //
        // Fixture: `t0 = &L; jalr x0, 0(t0); L: a0 = 1; exit`, and the same with offset 4, which skips `L`.
        let target = Region::TEXT.base() + 12;
        let text = |offset| {
            Asm::new()
                .li(Reg::T0, target)
                .jalr(Reg::ZERO, Reg::T0, offset)
                .i(Addi, Reg::A0, Reg::ZERO, 1)
                .exit()
                .finish()
        };
        let program = Program::new(&text(0), Region::TEXT.base(), vec![], 2, 0).expect("a valid program");
        let skipping = Program::new(&text(4), Region::TEXT.base(), vec![], 2, 0).expect("a valid program");
        assert_eq!(program.rv.pc_of(3), target);
        assert_eq!(program.execute(&[]).unwrap().output[0], 1);

        // Mutation: the run with offset 4 as one with offset 0, which outputs a0 = 0, its circuit computing `L`.
        //
        // Its push names `L`, which the exit's pull does not meet, until the bus's jump is forged to the exit's.
        let forged = skipping.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let jalr = (0..)
            .find(|&i| program.rv.entries()[i].flags == Alu::INDIRECT | Alu::ALWAYS)
            .unwrap();
        let row = forged.trace.rows[alu]
            .iter()
            .position(|r| r.index as usize == jalr && r.time != 0)
            .unwrap();
        let pc4 = program.rv.pc_of(jalr) + 4;
        let error = forged_jump(&program, &forged, row, (target + 4) ^ pc4);
        assert!(matches!(error, CpuError::Open(_)), "{error}");
    }

    #[test]
    fn a_stale_read_unbalances_the_bus() {
        // Invariant: a row reads a register's value at its own time, which only the register log says.
        //
        // Fixture state: `t0 = 5; t0 = 9; t1 = 3; a0 = t0 + t1`, which proves.
        let text = Asm::new()
            .i(Addi, Reg::T0, Reg::ZERO, 5)
            .i(Addi, Reg::T0, Reg::ZERO, 9)
            .i(Addi, Reg::T1, Reg::ZERO, 3)
            .r(Add, Reg::A0, Reg::T0, Reg::T1)
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let honest = program.execute(&[]).unwrap();
        assert_eq!(honest.output, [12, 0, 0, 0]);
        let (proof, _) = program.prove_execution(&honest, Rate::MIN);
        program
            .verify(honest.output.into(), &proof)
            .expect("the honest run verifies");

        // Mutation: the add reads the first write's 5, and `a0`'s write and the output follow it.
        //
        //     table pulls (t0, tau_4, ..., v1 = 5, ..., 8)
        //     log pushes  (t0, tau_4, ..., v1 = 9, ..., 8)
        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[TableId::ALU][3];
        assert_eq!(row.v1, 9);
        (row.v1, row.out) = (5, 8);
        let cycle = log_row(row.time);
        rewrite(&mut forged.trace.registers, cycle, 12, 8);
        forged.output[0] = 8;
        let w = Witness::build(&program, &forged);
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_forged_load_unbalances_the_bus() {
        // Invariant: a load returns what the memory log says its cell holds.
        //
        // Mutation: the load returns 7 from a cell holding 5, and `a0`'s write follows it.
        for (store, load, classes) in STORE_LOAD {
            let (program, mut forged, [_, table]) = store_then_load(store, load, classes);
            let row = real(&mut forged.trace.rows[table]);
            (row.ram.old, row.ram.new, row.out) = (7, 7, 7);
            let cycle = log_row(row.time);
            rewrite(&mut forged.trace.registers, cycle, 5, 7);
            // The load's pull of the 7, and the memory log's push of the 5.
            let unmatched = unmatched_run(&program, &forged);
            assert_eq!(unmatched.len(), 2, "{}: {unmatched:?}", load.mnemonic());
        }
    }

    #[test]
    fn a_forged_store_unbalances_the_bus() {
        // Invariant: a store cannot write a value its `rs2` does not hold.
        //
        // Mutation: the store writes 7, and the memory log, the load and `a0` follow it.
        // So only the store's read of `t1` is left to refuse it.
        for (store, load, classes) in STORE_LOAD {
            let (program, mut forged, tables) = store_then_load(store, load, classes);
            let [store_rows, load_rows] = forged.trace.rows.get_disjoint_mut(tables).unwrap();
            let (store_row, load_row) = (real(store_rows), real(load_rows));
            (store_row.v2, store_row.ram.new) = (7, 7);
            (load_row.ram.old, load_row.ram.new, load_row.out) = (7, 7, 7);
            let (written, loaded) = (log_row(store_row.position), log_row(load_row.time));
            rewrite(&mut forged.trace.memory, written, 5, 7);
            rewrite(&mut forged.trace.registers, loaded, 5, 7);
            // The store's register pull of a `t1` of 7, and the register log's push of the 5.
            let unmatched = unmatched_run(&program, &forged);
            assert_eq!(unmatched.len(), 2, "{}: {unmatched:?}", store.mnemonic());
        }
    }

    #[test]
    fn a_doubleword_moves_its_value_unchanged() {
        // Invariant: `ld`'s `rd` receives the cell it reads, and `sd`'s cell the `v2` it reads, one column on both tuples.
        //
        // Fixture state: `t1 = 5` is stored in RAM's fifth word by `sd`, then loaded into `a0` by `ld`.
        let (program, honest, tables) = store_then_load(Sd, Ld, [Class::Sd, Class::Ld]);

        // Mutation: the load gives `a0` 7 from a cell holding 5, the register log following it.
        // The row's write pushes the cell's 5, which the log's 7 does not meet.
        let mut forged = program.execute(&[]).unwrap();
        let load = real(&mut forged.trace.rows[tables[1]]);
        load.out = 7;
        let cycle = log_row(load.time);
        rewrite(&mut forged.trace.registers, cycle, 5, 7);
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "ld: {unmatched:?}");

        // Mutation: the store leaves 7 from a `t1` holding 5, the memory log, the load and `a0` following it.
        // The row's access pushes its `v2`, 5, which the log's 7 does not meet.
        let mut forged = honest;
        let [store, load] = forged.trace.rows.get_disjoint_mut(tables).unwrap();
        let store = real(store);
        store.ram.new = 7;
        let load = real(load);
        (load.ram.old, load.ram.new, load.out) = (7, 7, 7);
        let (written, loaded) = (log_row(store.position), log_row(load.time));
        rewrite(&mut forged.trace.memory, written, 5, 7);
        rewrite(&mut forged.trace.registers, loaded, 5, 7);
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "sd: {unmatched:?}");
    }

    #[test]
    fn a_misaligned_doubleword_names_no_cell() {
        // Invariant: a doubleword's bus address is its sum itself, so a misaligned `ld` or `sd` names no cell.
        //
        // Fixture state: `t0` is RAM's fifth word, then `ld a0, 0(t0)` or `sd t1, 0(t0)`, run honestly.
        // Mutation: the program's access has immediate 1, which the interpreter refuses; the row is the honest one at the
        // address its circuit computes, a byte past the cell the memory log names.
        let cell = Region::RAM.base() + 32;
        for class in [Class::Ld, Class::Sd] {
            let text = |offset| {
                let mut a = Asm::new();
                a.li(Reg::T0, cell).i(Addi, Reg::T1, Reg::ZERO, 5);
                match class {
                    Class::Ld => a.load(Ld, Reg::A0, offset, Reg::T0),
                    _ => a.store(Sd, Reg::T1, offset, Reg::T0),
                };
                a.exit().finish()
            };
            let program =
                |offset| Program::new(&text(offset), Region::TEXT.base(), vec![], 3, 0).expect("valid program");
            let misaligned = program(1);
            assert!(matches!(
                misaligned.execute(&[]),
                Err(ProveError::Trap(Trap::Misaligned { address, .. })) if address == cell + 1
            ));
            let mut forged = program(0).execute(&[]).unwrap();
            real(&mut forged.trace.rows[TableId::of(class).unwrap()]).ram.address = cell + 1;
            let w = Witness::build(&misaligned, &forged);
            // The row's access, and the memory log's at the cell.
            assert_eq!(unmatched(&w).len(), 2, "{class:?}: {:?}", unmatched(&w));
            assert_unbalanced(&misaligned, w, forged.output.into());
        }
    }

    #[test]
    fn a_forged_padding_row_unbalances_the_bus() {
        // Invariant: a padding row is at time zero, which no log row has, so it pulls only the public padding tuples.
        //
        // Mutation: a padding row of ALU claims to read 7 from `x0`, its circuit's outputs following it.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let row = forged.trace.rows[TableId::ALU]
            .iter_mut()
            .find(|r| r.time == 0)
            .expect("ALU has padding rows");
        let index = row.index as usize;
        let Outcome { out, taken, .. } = program.rv.entries()[index].evaluate(program.rv.pc_of(index), 7, row.v2, 0);
        (row.v1, row.out, row.taken) = (7, out, taken);

        // Its register pull, and the padding producer's push of the tuple it should have pulled.
        let w = Witness::build(&program, &forged);
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        let padding = w.layout.push.len() + Lookup::Padding as usize;
        assert!(
            unmatched
                .iter()
                .any(|&(side, block, _)| (side, block) == ("push", padding)),
            "{unmatched:?}"
        );
        assert_unbalanced(&program, w, forged.output.into());
    }

    /// The verifier's verdict on the proof of a run forged into `exec`, whose bus balances.
    fn verdict(program: &Program, exec: &Execution) -> Result<(), CpuError> {
        let w = Witness::build(program, exec);
        let unmatched = unmatched(&w);
        assert!(unmatched.is_empty(), "the forged run balances: {unmatched:?}");
        let proof = program.prove_witness(w, exec.output.into(), Rate::MIN);
        program.verify_to_raw(exec.output.into(), &proof).map(drop)
    }

    /// Make an extension-field row write `c` in place of its product, the memory log following it.
    fn forge_product(exec: &mut Execution, at: usize, c: [u64; 3]) {
        let (row, x) = (&exec.trace.rows[TableId::EXT][at], &mut exec.trace.ext[at]);
        let first = log_row(row.position) + Ext::LIMBS - 3;
        for (k, (&honest, &forged)) in x.c.iter().zip(&c).enumerate() {
            rewrite(&mut exec.trace.memory, first + k, honest, forged);
        }
        x.c = c;
    }

    #[test]
    fn a_forged_extension_product_is_refused() {
        // Invariant: an extension-field row writes its product, which only the table's identities say.
        //
        // Fixture state: the honest run proves.
        let program = extension_products();
        let honest = program.execute(&[]).unwrap();
        assert_eq!(verdict(&program, &honest), Ok(()));

        // Mutation: the last row's d forged in two limbs, and the memory log following it, so the bus balances.
        let mut forged = program.execute(&[]).unwrap();
        let at = forged.trace.rows[TableId::EXT]
            .iter()
            .rposition(|r| r.time != 0)
            .unwrap();
        let mut d = forged.trace.ext[at].c;
        (d[0], d[2]) = (d[0] ^ 1, d[2] ^ 1 << 63);
        forge_product(&mut forged, at, d);
        assert_eq!(
            verdict(&program, &forged),
            Err(CpuError::Constraint(constraints::ConstraintError::FinalMismatch))
        );
    }

    #[test]
    fn a_forged_extension_operand_unbalances_the_bus() {
        // Invariant: an extension-field row multiplies what memory holds.
        //
        // Mutation: the last row reads b_0 = y_0 ^ 5, and its product and the memory log follow it, so the identities hold.
        //
        //     table pulls (y_0's address, position, y_0 ^ 5, y_0 ^ 5)
        //     log pushes  (y_0's address, position, y_0, y_0)
        let program = extension_products();
        let mut forged = program.execute(&[]).unwrap();
        let at = forged.trace.rows[TableId::EXT]
            .iter()
            .rposition(|r| r.time != 0)
            .unwrap();
        let x = &mut forged.trace.ext[at];
        x.instance.limbs[3] ^= 5;
        let c = x.instance.eval();
        forge_product(&mut forged, at, c);
        let w = Witness::build(&program, &forged);
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_base_field_operand_has_no_high_limbs() {
        // Invariant: `extmulk` multiplies by a base-field element, whose high limbs are no access: they pull the absent
        // limb, all zeros.
        //
        // Mutation: the row claims b_1 = 1, as if b were (9, 1, 0), and c and the memory log follow it.
        let program = base_field_product();
        let mut forged = program.execute(&[]).unwrap();
        let at = forged.trace.rows[TableId::EXT]
            .iter()
            .position(|r| r.time != 0)
            .unwrap();
        let x = &mut forged.trace.ext[at];
        x.instance.limbs[4] = 1;
        let c = x.instance.eval();
        // A base-field row's c follows its two absent limbs, so it sits two positions earlier.
        let first = log_row(forged.trace.rows[TableId::EXT][at].position) + Ext::LIMBS - 5;
        let x = &mut forged.trace.ext[at];
        for (k, (&honest, &forged_word)) in x.c.iter().zip(&c).enumerate() {
            rewrite(&mut forged.trace.memory, first + k, honest, forged_word);
        }
        forged.trace.ext[at].c = c;

        // b_1's pull of a 1, and one of the absent limb's two pushes.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
    }

    #[test]
    fn a_forged_extension_padding_row_unbalances_the_bus() {
        // Invariant: a padding row's accesses are the public padding tuples, its product among them.
        //
        // Mutation: a padding row of EXT multiplies a = b = 1, and claims the product its padding tuple holds.
        let program = extension_products();
        let mut forged = program.execute(&[]).unwrap();
        let at = forged.trace.rows[TableId::EXT]
            .iter()
            .position(|r| r.time == 0)
            .unwrap();
        let x = &mut forged.trace.ext[at];
        (x.instance.limbs[0], x.instance.limbs[3]) = (1, 1);
        let w = Witness::build(&program, &forged);
        assert!(!unmatched(&w).is_empty());
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_forged_bytecode_read_unbalances_the_bus() {
        // Invariant: a row reads only an instruction the program has.
        //
        // Mutation: the `addi` row claims a branch offset of 8, which reaches no other tuple of a row that does not
        // branch; the multiplicities count what the rows now read.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = exec.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        let mut w = Witness::build(&program, &exec);
        // Bytecode slot 9 binds the decoded branch target offset.
        let bus = alu.class_table().flushes();
        let Coord::Col(branch_offset) = bus.pull[1][9] else {
            panic!("the ALU binds its branch offset to a column");
        };
        let offset = Schema::get().spans[alu].0 + branch_offset;
        column_mut(&mut w, offset)[row] = F64(8);
        column_mut(&mut w, Shared::BytecodeMult.col())[0].0 -= 1;

        // The row's bytecode read, and nothing else.
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 1, "{unmatched:?}");
        let (side, block, at) = unmatched[0];
        assert_eq!((side, at), ("pull", row));
        assert!(matches!(w.layout.pull[block].coords[0], Coord::Const(sep) if sep == Separator::Bytecode.value()));
        assert_unbalanced(&program, w, exec.output.into());
    }

    #[test]
    fn a_wrong_multiplicity_unbalances_the_bus() {
        // Invariant: the multiplicities are a producer's whole claim, so one bit off leaves its entry unmatched.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        for (p, lookup) in Lookup::ALL.into_iter().enumerate() {
            let col = lookup.multiplicity().col();
            for flip in [1u64, 2, 4] {
                let mut w = Witness::build(&program, &exec);
                assert_eq!(w.layout.producers[p].col, col);
                column_mut(&mut w, col)[0].0 ^= flip;
                // What is left is that entry's pushes and the reads of it, and nothing else.
                let unmatched = unmatched(&w);
                assert!(!unmatched.is_empty());
                let producer = w.layout.push.len() + p;
                assert!(
                    unmatched
                        .iter()
                        .all(|&(side, block, row)| side == "pull" || (block, row) == (producer, 0)),
                    "{unmatched:?}"
                );
                assert_unbalanced(&program, w, exec.output.into());
            }
        }
    }

    #[test]
    fn a_forged_register_number_unbalances_the_bus() {
        // Invariant: a row's register numbers are its entry's, which only the bytecode lookup says.
        //
        // Fixture state: `addi a0, x0, 5` reads `x0` first, then the exit.
        // Mutation: the row's first read names `ra`, which holds zero too: its column, its packed word and the register
        // log agree, and the entry's count follows the reads, which no longer include this one.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = forged.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        let cycle = log_row(forged.trace.rows[alu][row].time);
        forged.trace.registers.cells[0][cycle] = Reg::RA.index() as u32;
        let mut w = Witness::build(&program, &forged);
        let a1 = Schema::get().spans[alu].0 + alu.class_table().register_bits().fields[0].col;
        virtual_mut(&mut w, a1)[row] = F64(Reg::RA.index() as u64);
        column_mut(&mut w, Schema::get().registers[alu])[row].0 ^= Reg::RA.index() as u64;
        column_mut(&mut w, Shared::BytecodeMult.col())[0].0 -= 1;

        // The row's bytecode read, and nothing else.
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 1, "{unmatched:?}");
        let (side, block, at) = unmatched[0];
        assert_eq!((side, at), ("pull", row));
        assert!(matches!(w.layout.pull[block].coords[0], Coord::Const(sep) if sep == Separator::Bytecode.value()));
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_packed_register_word_is_its_slices() {
        // Invariant: the opening binds a row's packed word to the bits the table sumcheck read, its unused bits to zero.
        //
        // Fixture state: `addi a0, x0, 5; exit`, whose rows' register numbers are honest everywhere.
        // Mutation: one bit of the `addi` row's packed word: `a1`'s lowest, the next table's first where one shares it,
        // the first no table uses, then the top one.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = exec.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        // The ALU opens its word, which the tables of its height share after it.
        let word = Witness::build(&program, &exec).layout.registers.swap_remove(0);
        assert_eq!(word.tables[0], alu);
        let bits = |t: TableId| t.class_table().register_bits().n_slices();
        let used: usize = word.tables.iter().map(|&t| bits(t)).sum();
        let mut flipped = vec![0, bits(alu), used, 63];
        flipped.dedup();
        for bit in flipped {
            let mut w = Witness::build(&program, &exec);
            column_mut(&mut w, word.col)[row].0 ^= 1 << bit;
            assert!(
                unmatched(&w).is_empty(),
                "the bus reads the register numbers, not the word"
            );
            let proof = program.prove_witness(w, exec.output.into(), Rate::MIN);
            assert!(
                matches!(
                    program.verify_to_raw(exec.output.into(), &proof),
                    Err(CpuError::Open(_))
                ),
                "bit {bit}"
            );
        }
    }

    /// A column of a built witness, to forge it: its window in the stack, or a port's own buffer.
    fn column_mut(w: &mut Witness, col: usize) -> &mut [F64] {
        match w.layout.placements[col].window() {
            Some(window) => &mut w.q[window.offset..window.offset + (1 << window.n_vars)],
            None => virtual_mut(w, col),
        }
    }

    /// A column the stack does not hold, a port or a register number, of a built witness, to forge it.
    fn virtual_mut(w: &mut Witness, col: usize) -> &mut [F64] {
        let (_, values) = w
            .virt
            .iter_mut()
            .find(|(c, _)| *c == col)
            .expect("a forged column is virtual");
        values
    }
}
