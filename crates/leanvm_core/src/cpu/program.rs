//! A program as the proof sees it: the decoded program, its fill blocks, and the digest of its public statement.
//!
//! It runs, is proven, and is verified against its digest.

use super::batch::{Batch, FormPowers};
use super::deferred::DeferredClaims;
use super::error::{CpuError, ProveError, VerifyError};
use super::execute::{Execution, Recorder, RowCounter, TraceBuilder};
use super::filler::{FillBlocks, Plan};
use super::layout::{Announcement, Lookup, Schema, Sizes};
use super::reduce::TableClaims;
use super::witness::Witness;
use super::{Output, Proof};
use crate::class_flock::FlockId;
use crate::constraints::{Claims, Columns};
use crate::pcs::{Committed, Rate};
use crate::rv::{ElfError, Guest, Machine, ProgramError, Region, RiscvProgram};
use crate::tables::{ClassTable, Clock, PerTable, TableId};
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
    const DIGEST_DOMAIN: &'static [u8] = b"leanvm-rv64im-11";

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
        Ok(Self {
            digest: Self::digest_of(&rv),
            rv,
            filler,
        })
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
        let mut trace = TraceBuilder::new(p, m.memory().advice());
        let ts = self.run(&mut m, &mut trace)?;
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

        let trace = trace.finish(p, &m, ts);
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

    /// Run `m` to its halt, handing every step to `recorder`, and return the clock it stopped at.
    ///
    /// Every so many cycles the rows so far are checked against one commitment.
    ///
    /// So a run too long for one proof is refused while it runs, before its trace outgrows memory.
    #[inline(always)]
    fn run<R: Recorder>(&self, m: &mut Machine<'_>, recorder: &mut R) -> Result<u64, ProveError> {
        // The clock starts on cycle 1, so that the first access comes strictly after the seeds.
        let mut ts = Clock::CLOCK_START;

        // The heights last checked: the stack grows only when one of them does.
        let mut checked = PerTable::default();
        while !m.halted() {
            let cycle = ts >> Clock::SLOT_BITS & Clock::MAX_CYCLES;

            // The cycle count must not carry into the live bit.
            if cycle == Clock::MAX_CYCLES {
                return Err(ProveError::TooLong);
            }
            if cycle.is_multiple_of(Self::SIZE_CHECK_PERIOD) {
                let counts = recorder.row_counts();
                let heights = PerTable::from_fn(|t: TableId| t.spec().provable_height(counts[t]));
                if heights != checked {
                    self.committed_size(heights)?;
                    checked = heights;
                }
            }
            let step = m.step()?;
            recorder.record(&self.rv, m, step, ts);
            ts += Clock::CYCLE;
        }
        Ok(ts)
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
            committed: self.committed_size(counts)?,
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
            rate,
            ts_final: w.ts_final,
        };
        announcement.write(&mut ps);
        let committed = info_span!("Commit")
            .in_scope(|| Committed::new(&mut ps, &w.q, w.layout.shape, rate).expect("the witness matches its layout"));

        // The bus, then the linear tables' columns at its point, then the one batch over the other tables and the
        // producers, all reading the stack's windows in place.
        let spans = &Schema::get().spans;
        let (bus_claims, table_claims) = {
            let l = &w.layout;
            let cols = w.columns();
            let mut bus = info_span!("Prove bus").in_scope(|| {
                leaf::prove_balance(
                    &l.push,
                    &l.pull,
                    &l.producers,
                    l.grinding,
                    &cols,
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
            (bus.claims, TableClaims::new(settled, summed))
        };
        let l = &w.layout;
        let slots = l.opening_claims(
            &mut Native,
            bus_claims,
            &table_claims.columns,
            &output.words().map(|o| F192::from(F64(o))),
        );

        // Flock's reductions, batched over every class circuit then every clock circuit under shared challenges.
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
        let rings = l.rings(slices, &table_claims.producers, &table_claims.summed, F192::ZERO);
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
        let l = announcement.layout(&self.rv)?;
        let clock = F192::from(F64(announcement.ts_final));
        let output = output.words().map(|o| F192::from(F64(o)));
        let claims = l.verify_core(&mut vs, clock, &output, announcement.rate)?;
        Ok((claims, vs.into_raw_proof()))
    }

    /// The decoded text, memory image and region sizes.
    #[doc(hidden)]
    pub const fn rv(&self) -> &RiscvProgram {
        &self.rv
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
    pub(super) fn committed_size(&self, row_counts: PerTable<usize>) -> Result<usize, ProveError> {
        let taus = PerTable::from_fn(|t: TableId| crate::log2_strict_usize(t.spec().provable_height(row_counts[t])));
        let (placements, shape) = Sizes::of(&self.rv).stack(&taus);
        if shape.mu > crate::pcs::MAX_MU {
            return Err(ProveError::TooLong);
        }
        Ok(crate::witness::committed_len(&placements))
    }

    /// The digest of `rv`'s public statement.
    ///
    /// Every variable-length part is length-framed, so the preimage parses one way.
    fn digest_of(rv: &RiscvProgram) -> [u8; 32] {
        let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let table = Lookup::Bytecode.table(rv);
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
    use crate::cpu::filler::JUMP;
    use crate::cpu::layout::{Framework, Shared};
    use crate::leaf::Coord;
    use crate::leaf::tests::unmatched_leaves;
    use crate::pcs::Rate;
    use crate::rv::asm::*;
    use crate::rv::semantics::Outcome;
    use crate::rv::{Alu, Class, Machine, ProgramError, Reg, RegisterFile, Trap};
    use crate::tables::{ClassSpec, ClassTable, Clock, Separator};
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
    fn unmatched(w: &Witness) -> Vec<(&'static str, usize, usize)> {
        unmatched_leaves(&w.layout.push, &w.layout.pull, &w.layout.producers, &w.columns())
    }

    /// A column of a built witness, to forge it: its window in the stack, or a port's own buffer.
    fn column_mut(w: &mut Witness, col: usize) -> &mut [F64] {
        match w.layout.placements[col].window() {
            Some(window) => &mut w.q[window.offset..window.offset + (1 << window.n_vars)],
            None => {
                &mut w
                    .virt
                    .iter_mut()
                    .find(|(i, _)| *i == col)
                    .expect("a port has a buffer")
                    .1
            }
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

    /// Put `row` in place of a padding row of `ALU` that is the lone jump of its fill, a jump to itself.
    ///
    /// Both are closed walks of one row at clock zero, so the state channel does not see the swap.
    fn replace_lone_jump(program: &Program, exec: &mut Execution, row: Row) {
        let lone = program.filler.get(JUMP, 0).expect("ALU has a lone jump").index;
        let at = exec.trace.rows[TableId::ALU]
            .iter()
            .position(|r| r.index as usize == lone)
            .expect("the fill traverses the lone jump");
        exec.trace.rows[TableId::ALU][at] = row;
    }

    /// The padding row a jump to itself makes, `jal rd, 0` at entry `index`, at clock zero.
    fn padding_jump(program: &Program, index: usize) -> Row {
        let e = &program.rv.entries()[index];
        let Outcome { out, taken, access } = e.evaluate(program.rv.pc_of(index), 0, 0, 0);
        let ram = access.unwrap_or_default();
        let slots: Vec<u64> = ClassSpec::ALU.slots().into_iter().map(u64::from).collect();
        Row {
            index: index as u32,
            ts: 0,
            v1: 0,
            v2: 0,
            out,
            taken,
            vd_old: program.rv.pc_of(index) + 4,
            ram,
            prev: [slots[0], slots[1], slots[2], 0],
        }
    }

    /// The tuples a run leaves unmatched, as `(side, block, row)`.
    fn unmatched_run(program: &Program, exec: &Execution) -> Vec<(&'static str, usize, usize)> {
        unmatched(&Witness::build(program, exec))
    }

    /// An honest run's bus balances tuple by tuple, which says more than the proof
    /// failing would: the blocks left unmatched are named.
    #[test]
    fn an_honest_run_balances() {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let w = Witness::build(&program, &program.execute(&[]).unwrap());
        let unmatched = unmatched(&w);
        assert!(
            unmatched.is_empty(),
            "unmatched (side, block, row): {:?}",
            &unmatched[..unmatched.len().min(12)]
        );
    }

    #[test]
    fn a_run_too_long_for_one_proof_is_refused_while_it_runs() {
        // Fibonacci for 2^63 steps: only the cycle cap would stop it, after 2^35 rows.
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
        let counts = counter.row_counts();
        let rows: usize = counts.values().sum();
        assert!(rows < 1 << crate::pcs::MAX_MU, "{rows} rows counted");
        assert_eq!(program.committed_size(counts), Err(ProveError::TooLong));

        // A period earlier, no table had more than these rows, and they fit.
        let earlier = counts.map(|c| c.saturating_sub(Program::SIZE_CHECK_PERIOD as usize));
        assert!(program.committed_size(earlier).is_ok());
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
        let row = execution.trace.rows[TableId::ALU]
            .iter_mut()
            .find(|r| r.index as usize == exit_index)
            .unwrap();
        row.out = pc + 4;
        execution.trace.reg_fin[RegisterFile::SINK as usize] = F64(pc + 4);
        let witness = Witness::build(&program, &execution);
        let unmatched = unmatched(&witness);
        // The final state on the pull side, and the ALU's state push, the push side's
        // first block past its four framework blocks.
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(unmatched.iter().all(|(_, block, _)| *block == 0 || *block == 4));
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
        assert!(
            left.iter().all(|&(_, block, _)| block >= Framework::ALL.len()),
            "{left:?}"
        );
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
            .position(|r| r.index as usize == jalr && r.ts != 0)
            .unwrap();
        let pc4 = program.rv.pc_of(jalr) + 4;
        let error = forged_jump(&program, &forged, row, (target + 4) ^ pc4);
        assert!(matches!(error, CpuError::Open(_)), "{error}");
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

    /// The first row of the run among `rows`, past the padding rows at clock zero.
    fn real(rows: &mut [Row]) -> &mut Row {
        rows.iter_mut().find(|r| r.ts != 0).unwrap()
    }

    /// A load cannot return what its cell does not hold. The forged run is consistent
    /// everywhere else (the circuit's instance, the register written, the output), so
    /// what is left unmatched is RAM's: the load pulls a tuple no store pushed.
    #[test]
    fn a_forged_load_unbalances_the_bus() {
        for (store, load, classes) in STORE_LOAD {
            let (program, mut forged, [_, table]) = store_then_load(store, load, classes);
            let row = real(&mut forged.trace.rows[table]);
            (row.ram.old, row.ram.new, row.out) = (7, 7, 7);
            forged.trace.reg_fin[Reg::A0.index()] = F64(7);
            forged.trace.ram_fin[4] = F64(7);
            let unmatched = unmatched_run(&program, &forged);
            // The load's pull and the store's push, which it should have met.
            assert_eq!(unmatched.len(), 2, "{}: {unmatched:?}", load.mnemonic());
        }
    }

    #[test]
    fn a_base_field_operand_has_no_high_limbs() {
        // Invariant: `extmulk` multiplies by a base-field element, its high limbs read from `x0`, which holds zero.
        //
        // Fixture state: a = (3, 5, 7) at RAM's base, the base-field b = 9 right after it, c after that, packed.
        let image = vec![3, 5, 7, 9, 0, 0, 0];
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T0, ram)
            .li(Reg::T1, ram + 24)
            .li(Reg::T2, ram + 32)
            .ext(Extmulk, Reg::T2, Reg::T0, Reg::T1)
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), image, 3, 0).expect("valid instruction program");
        assert!(unmatched_run(&program, &program.execute(&[]).unwrap()).is_empty());

        // Mutation: the row claims b_1 = 1, as if b were (9, 1, 0), and c and RAM follow it, so the identities hold.
        let mut forged = program.execute(&[]).unwrap();
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().position(|r| r.ts != 0).unwrap();
        let x = &mut forged.trace.ext[at];
        x.instance.limbs[4] = 1;
        x.c = x.instance.eval();
        for (k, word) in x.c.into_iter().enumerate() {
            forged.trace.ram_fin[4 + k] = F64(word);
        }

        // Two tuples on each side: b_1's read of x0, and b_2's read right after it.
        //
        //     b_1 pulls a 1 nothing pushed, and pushes a 1
        //     b_2 pulls the 0 it found, which nothing pushed, and leaves the 1 unpulled
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 4, "{unmatched:?}");
    }

    #[test]
    fn a_write_to_x0_unbalances_the_bytecode_read() {
        // Invariant: no row writes `x0`, so a base-field operand's high limbs, which read it, are zero.
        //
        // Fixture state: `t3 = 1`, then `extmulk` of a = (3, 5, 7) by the base-field b = 9, then the `ecall`.
        let image = vec![3, 5, 7, 9, 0, 0, 0];
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T0, ram)
            .li(Reg::T1, ram + 24)
            .li(Reg::T2, ram + 32)
            .i(Addi, Reg::A7, Reg::ZERO, 93)
            .i(Addi, Reg::T3, Reg::ZERO, 1)
            .ext(Extmulk, Reg::T2, Reg::T0, Reg::T1)
            .ecall()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), image, 3, 0).expect("valid instruction program");
        assert!(unmatched_run(&program, &program.execute(&[]).unwrap()).is_empty());
        let (addi, ecall) = (text.len() as u32 - 3, text.len() as u32 - 1);

        // Mutation: the `addi` writes its 1 to `x0` instead of `t3`, and everything after reads it.
        //
        //     addi   writes x0 after its own read of it in slot 1; t3 keeps its seed
        //     ext    reads b = (9, 1, 1), and c and RAM follow it
        //     ecall  reads 1 twice, and writes 1 + 1 to the sink
        let mut forged = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let write = forged.trace.rows[alu].iter_mut().find(|r| r.index == addi).unwrap();
        let ts = write.ts;
        (write.prev[2], write.vd_old) = (ts | 1, 0);
        let t3 = Reg::T3.index();
        (forged.trace.reg_fin[t3], forged.trace.reg_ts[t3]) = (F64::ZERO, F64(Clock::SEED_CLOCK));
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().position(|r| r.ts != 0).unwrap();
        let x = &mut forged.trace.ext[at];
        (x.instance.limbs[4], x.instance.limbs[5]) = (1, 1);
        x.prev[3 + 4] = ts | 3;
        x.c = x.instance.eval();
        for (k, word) in x.c.into_iter().enumerate() {
            forged.trace.ram_fin[4 + k] = F64(word);
        }
        let exit = forged.trace.rows[alu].iter_mut().find(|r| r.index == ecall).unwrap();
        (exit.v1, exit.v2, exit.out) = (1, 1, 2);
        forged.trace.reg_fin[0] = F64(1);
        forged.trace.reg_fin[RegisterFile::SINK as usize] = F64(2);
        let mut w = Witness::build(&program, &forged);
        let bus = alu.class_table().flushes();
        let Coord::Col(destination) = bus.pull[1][ClassTable::DESTINATION_SLOT] else {
            panic!("the ALU binds its destination to a column");
        };
        let row = forged.trace.rows[alu].iter().position(|r| r.index == addi).unwrap();
        // The destination is a register number: its column and its field of the packed word both name `x0`.
        virtual_mut(&mut w, Schema::get().spans[alu].0 + destination)[row] = F64::ZERO;
        // The ALU's fields come first in its word, so its destination's sits after the reads'.
        let fields = alu.class_table().register_bits().fields;
        let at = fields.iter().position(|f| f.col == destination).unwrap();
        let shift: usize = fields[..at].iter().map(|f| f.width).sum();
        let mask = (1 << fields[at].width) - 1;
        column_mut(&mut w, Schema::get().registers[alu])[row].0 &= !(mask << shift);
        column_mut(&mut w, Shared::BytecodeMult.col())[addi as usize].0 -= 1;

        // Registers, RAM and the multiplicities balance: only the read of an entry whose destination is 0 is left.
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 1, "{unmatched:?}");
        let (side, block, at) = unmatched[0];
        assert_eq!((side, at), ("pull", row));
        assert!(matches!(w.layout.pull[block].coords[0], Coord::Const(sep) if sep == Separator::Bytecode.value()));
        assert_unbalanced(&program, w, forged.output.into());
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

    /// The verifier's verdict on the proof of a run forged into `exec`, whose bus balances.
    fn verdict(program: &Program, exec: &Execution) -> Result<(), CpuError> {
        let w = Witness::build(program, exec);
        let unmatched = unmatched(&w);
        assert!(unmatched.is_empty(), "the forged run balances: {unmatched:?}");
        let proof = program.prove_witness(w, exec.output.into(), Rate::MIN);
        program.verify_to_raw(exec.output.into(), &proof).map(drop)
    }

    #[test]
    fn a_forged_extension_product_is_refused() {
        // Invariant: an extension-field row writes its product, which only the table's identities say.
        //
        // Fixture state: the honest run proves.
        let program = extension_products();
        let honest = program.execute(&[]).unwrap();
        assert_eq!(verdict(&program, &honest), Ok(()));

        // Mutation: the last row's d forged in two limbs, and d's final words following it, so the bus balances.
        let mut forged = program.execute(&[]).unwrap();
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().rposition(|r| r.ts != 0).unwrap();
        let x = &mut forged.trace.ext[at];
        for (k, bit) in [(0, 1), (2, 1 << 63)] {
            x.c[k] ^= bit;
            forged.trace.ram_fin[10 + k].0 ^= bit;
        }
        assert_eq!(
            verdict(&program, &forged),
            Err(CpuError::Constraint(constraints::ConstraintError::FinalMismatch))
        );
    }

    #[test]
    fn a_forged_extension_padding_row_is_refused() {
        // Invariant: a padding row is off the bus, so the identities are all that hold it.
        //
        // Mutation: a padding row of EXT multiplies a = b = 1 and claims c' = 0, every access still pulling what it pushes.
        let program = extension_products();
        let mut forged = program.execute(&[]).unwrap();
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().position(|r| r.ts == 0).unwrap();
        let x = &mut forged.trace.ext[at];
        (x.instance.limbs[0], x.instance.limbs[3]) = (1, 1);
        assert_eq!(
            verdict(&program, &forged),
            Err(CpuError::Constraint(constraints::ConstraintError::FinalMismatch))
        );
    }

    #[test]
    fn a_forged_extension_operand_unbalances_the_bus() {
        // Invariant: an extension-field row multiplies what memory holds.
        //
        // Mutation: the last row reads b_0 = y_0 ^ 5, and its product and d's final words follow it, so the identities hold.
        // Its a is the same element, read first, so the forgery is two accesses to y_0's word:
        //
        //     a_0 pushes (y_0, ts ^ 4)     which b_0 should pull, and pulls (y_0 ^ 5, ts ^ 4) instead
        //     b_0 pushes (y_0 ^ 5, ts ^ 7) which the final word should pull, and pulls (y_0, ts ^ 7) instead
        let program = extension_products();
        let mut forged = program.execute(&[]).unwrap();
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().rposition(|r| r.ts != 0).unwrap();
        let x = &mut forged.trace.ext[at];
        x.instance.limbs[3] ^= 5;
        x.c = x.instance.eval();
        for (k, word) in x.c.into_iter().enumerate() {
            forged.trace.ram_fin[10 + k] = F64(word);
        }
        let w = Witness::build(&program, &forged);
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 4, "{unmatched:?}");
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_misaligned_extension_operand_unbalances_the_bus() {
        // Invariant: a limb is a word, so an operand off its word names no cell.
        //
        // Fixture state: a's address comes from the advice, then `c = a b`; the advice holds RAM's base.
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T5, Region::ADVICE.base())
            .load(Ld, Reg::T0, 0, Reg::T5)
            .li(Reg::T1, ram + 24)
            .li(Reg::T3, ram + 48)
            .ext(Extmul, Reg::T3, Reg::T0, Reg::T1)
            .exit()
            .finish();
        let image = vec![11, 13, 17, 19, 23, 29, 0, 0, 0];
        let program = Program::new(&text, Region::TEXT.base(), image, 4, 0).expect("valid instruction program");
        let misaligned = ram + 4;
        assert!(matches!(
            program.execute(&[misaligned]),
            Err(ProveError::Trap(Trap::Misaligned { address, .. })) if address == misaligned
        ));

        // Mutation: the honest run with the advice holding `ram + 4`, and everything that follows from it: the load,
        // `t0` and the row's pointer. a's limbs keep the values and timestamps of the words at `ram + 8j`.
        let mut forged = program.execute(&[ram]).unwrap();
        (forged.trace.adv_init[0], forged.trace.adv_fin[0]) = (F64(misaligned), F64(misaligned));
        forged.trace.reg_fin[Reg::T0.index()] = F64(misaligned);
        let load = TableId::LD;
        let row = forged.trace.rows[load].iter_mut().find(|r| r.ts != 0).unwrap();
        (row.ram.old, row.ram.new, row.out) = (misaligned, misaligned, misaligned);
        let ext = TableId::EXT;
        let at = forged.trace.rows[ext].iter().position(|r| r.ts != 0).unwrap();
        forged.trace.rows[ext][at].v1 = misaligned;
        forged.trace.ext[at].instance.pointers[0] = misaligned;

        // Each of a's limbs is at `ram + 4 + 8j`, which no cell is: the row's pull and push there, and the seed push
        // and final pull of the word at `ram + 8j`, which the row no longer meets.
        let w = Witness::build(&program, &forged);
        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 12, "{unmatched:?}");
        assert_unbalanced(&program, w, forged.output.into());
    }

    #[test]
    fn a_forged_store_unbalances_the_bus() {
        // Invariant: a store cannot write a value its `rs2` does not hold.
        //
        // Fixture state: `t1 = 5` is stored in RAM's fifth word, then loaded into `a0`.
        // Mutation: the store writes 7, and the circuit's instance, the cell, the load and the output follow it.
        // So only the store's read of `t1` is left to refuse it.
        for (store, load, classes) in STORE_LOAD {
            let (program, mut forged, tables) = store_then_load(store, load, classes);
            let [store_rows, load_rows] = forged.trace.rows.get_disjoint_mut(tables).unwrap();
            let (store_row, load_row) = (real(store_rows), real(load_rows));
            (store_row.v2, store_row.ram.new) = (7, 7);
            (load_row.ram.old, load_row.ram.new, load_row.out) = (7, 7, 7);
            forged.trace.reg_fin[Reg::A0.index()] = F64(7);
            forged.trace.ram_fin[4] = F64(7);
            let unmatched = unmatched_run(&program, &forged);
            // The read, pulled and pushed back as 7, meets neither `t1`'s write nor its final value.
            // That leaves two tuples on each side.
            assert_eq!(unmatched.len(), 4, "{}: {unmatched:?}", store.mnemonic());
        }
    }

    #[test]
    fn a_doubleword_moves_its_value_unchanged() {
        // Invariant: a doubleword load's `rd` receives the cell it reads, and a doubleword store's cell the `v2` it reads.
        //
        // Fixture state: `t1 = 5` is stored in RAM's fifth word by `sd`, then loaded into `a0` by `ld`.
        // Mutation: the load gives `a0` 7 from a cell holding 5, or the store leaves 7 from a `t1` holding 5, what follows agreeing.
        // Neither class has a column for the value it moves other than the one it reads, so the 5 is what it pushes.
        let (program, honest, tables) = store_then_load(Sd, Ld, [Class::Sd, Class::Ld]);
        let mut forged = program.execute(&[]).unwrap();
        real(&mut forged.trace.rows[tables[1]]).out = 7;
        forged.trace.reg_fin[Reg::A0.index()] = F64(7);
        // The write's push of 5 and `a0`'s final 7.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "ld: {unmatched:?}");

        let mut forged = honest;
        let [store, load] = forged.trace.rows.get_disjoint_mut(tables).unwrap();
        real(store).ram.new = 7;
        let load = real(load);
        (load.ram.old, load.ram.new, load.out) = (7, 7, 7);
        forged.trace.reg_fin[Reg::A0.index()] = F64(7);
        forged.trace.ram_fin[4] = F64(7);
        // The store's push of 5 and the load's pull of 7.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "sd: {unmatched:?}");
    }

    #[test]
    fn a_misaligned_doubleword_names_no_cell() {
        // Invariant: a doubleword's bus address is its sum itself, so a misaligned `ld` or `sd` names no cell.
        //
        // Fixture state: `t0` is RAM's fifth word, then `ld a0, 0(t0)` or `sd t1, 0(t0)`, run honestly.
        // Mutation: the program's access has immediate 1, which the interpreter refuses; the row is the honest one at the
        // address its circuit computes, a byte past the cell, and the cell it should have touched keeps its seed.
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
            let row = real(&mut forged.trace.rows[TableId::of(class).unwrap()]);
            row.ram.address = cell + 1;
            (forged.trace.ram_fin[4], forged.trace.ram_ts[4]) = (F64::ZERO, F64(Clock::SEED_CLOCK));
            let w = Witness::build(&misaligned, &forged);
            // The access's pull and push, at an address no cell has.
            assert_eq!(unmatched(&w).len(), 2, "{class:?}: {:?}", unmatched(&w));
            assert_unbalanced(&misaligned, w, forged.output.into());
        }
    }

    /// The point of the timestamps: a register written twice cannot be read as of its
    /// first write. The forged run is consistent everywhere else (the stale value
    /// flows into the result and the final registers, and the read is in order), so
    /// what fails is the register multiset itself: the first write's tuple is pulled twice.
    #[test]
    fn a_stale_read_unbalances_the_bus() {
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

        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[TableId::ALU][3];
        // The read happens at cycle 4; the first write happened at cycle 1, the second at 2, each in slot 3.
        let write = |cycle: u64| Clock::SEED_CLOCK | (cycle * Clock::CYCLE) | 3;
        assert_eq!((row.v1, row.prev[0]), (9, write(2)));
        (row.v1, row.out, row.prev[0]) = (5, 8, write(1));
        forged.output[0] = 8;
        forged.trace.reg_fin[Reg::A0.index()] = F64(8);
        // The multiplicities follow the forged gap, so no producer is left unmatched.
        let w = Witness::build(&program, &forged);
        let push = w.layout.push.len();
        assert!(
            unmatched(&w)
                .iter()
                .all(|&(side, block, _)| side == "pull" || block < push)
        );
        assert_unbalanced(&program, w, forged.output.into());
    }

    /// A row can only read an instruction the program has: one claiming a branch offset
    /// its entry does not hold reads no entry. The offset reaches no other tuple of a
    /// branch not taken, so the forged row is consistent everywhere else, and recounting
    /// the multiplicities for what the rows now read leaves its bytecode read unmatched.
    #[test]
    fn a_forged_bytecode_read_unbalances_the_bus() {
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

        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 1, "{unmatched:?}");
        let (side, block, at) = unmatched[0];
        assert_eq!((side, at), ("pull", row));
        assert!(matches!(w.layout.pull[block].coords[0], Coord::Const(sep) if sep == Separator::Bytecode.value()));
        assert_unbalanced(&program, w, exec.output.into());
    }

    /// The multiplicities are the producers' whole claim, so one that does not count the
    /// reads, in any bit, leaves its entry unmatched: what is left is that entry's pushes
    /// and the reads of it, and nothing else.
    #[test]
    fn a_wrong_multiplicity_unbalances_the_bus() {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        for (p, col) in Lookup::ALL
            .map(|lookup| lookup.multiplicity().col())
            .into_iter()
            .enumerate()
        {
            for flip in [1u64, 2, 4] {
                let mut w = Witness::build(&program, &exec);
                assert_eq!(w.layout.producers[p].col, col);
                column_mut(&mut w, col)[0].0 ^= flip;
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
        // Fixture state: `addi a0, x0, 5` at cycle 1, reading `x0` in slots 0 and 1, then the exit.
        // Mutation: the `addi` row's slot-0 read names `ra` in place of `x0`, its packed word and its `a1` agreeing.
        // `ra` holds zero too, and the timestamps follow: that read pulls `ra`'s seed, `ra` ends at the row's clock,
        // and the slot-1 read of `x0` pulls `x0`'s seed.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = forged.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        let addi = &mut forged.trace.rows[alu][row];
        assert_eq!(addi.prev[..2], [Clock::SEED_CLOCK, addi.ts]);
        addi.prev[1] = Clock::SEED_CLOCK;
        forged.trace.reg_ts[Reg::RA.index()] = F64(addi.ts);
        let mut w = Witness::build(&program, &forged);
        let table = alu.class_table();
        let a1 = Schema::get().spans[alu].0 + table.register_bits().fields[0].col;
        virtual_mut(&mut w, a1)[row] = F64(Reg::RA.index() as u64);
        column_mut(&mut w, Schema::get().registers[alu])[row].0 ^= Reg::RA.index() as u64;
        // The entry's count follows the reads, which no longer include this one.
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
        // Mutation: one bit of the `addi` row's packed word: `a1`'s lowest, the next table's first, the first no table
        // uses, then the top one.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let alu = TableId::ALU;
        let row = exec.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        // The ALU opens its word, which the tables of its height share after it.
        let word = Witness::build(&program, &exec).layout.registers.swap_remove(0);
        assert_eq!(word.tables[0], alu);
        assert!(word.tables.len() > 1, "the tables of one height share the word");
        let bits = |t: TableId| t.class_table().register_bits().n_slices();
        let used: usize = word.tables.iter().map(|&t| bits(t)).sum();
        for bit in [0, bits(alu), used, 63] {
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

    #[test]
    fn a_read_of_its_own_push_is_out_of_order() {
        // Invariant: an access cannot pull the tuple it pushes, which would let a read return anything.
        //
        // Fixture state: `t0 = 5`, then `a0 = t0 + x0` at cycle 2.
        // Mutation: the read of `t0` pulls `(t0, ts, 9)`, which it pushes back, and `t0`'s write meets its final instead.
        // The registers then balance, and only the clock circuit's order check is left to refuse it.
        let text = Asm::new()
            .i(Addi, Reg::T0, Reg::ZERO, 5)
            .r(Add, Reg::A0, Reg::T0, Reg::ZERO)
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[TableId::ALU][1];
        (row.v1, row.out, row.prev[0]) = (9, 9, row.ts);
        forged.output[0] = 9;
        forged.trace.reg_fin[Reg::A0.index()] = F64(9);
        forged.trace.reg_ts[Reg::T0.index()] = F64(Clock::CLOCK_START | 3);
        // The read's row pushes a failed clock, which the next row's pull does not meet.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(unmatched.iter().all(|&(_, block, _)| block == Framework::ALL.len()));
    }

    #[test]
    fn a_padding_row_cannot_pull_a_seed() {
        // Invariant: a row at clock zero touches no tuple of the run, the seeds included.
        //
        // Fixture state: the run sets `a0 = 42` and exits, never touching `a1`.
        // Past the exit sits `jal a1, 0`, a jump to itself, which the run never reaches.
        // The two no-ops size ALU's fill so that it ends on the lone jump.
        // Mutation: a padding instance of it takes the place of the fill's lone jump, its write pulling `a1`'s seed.
        // `a1`'s final value is what it pushes, so the output claims `a1 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .i(Addi, Reg::ZERO, Reg::ZERO, 0)
            .i(Addi, Reg::ZERO, Reg::ZERO, 0)
            .exit()
            .label("spin")
            .jal(Reg::A1, "spin")
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let mut row = padding_jump(&program, spin);
        (row.prev[2], row.vd_old) = (Clock::SEED_CLOCK, 0);
        replace_lone_jump(&program, &mut forged, row);
        let link = program.rv.pc_of(spin) + 4;
        forged.output[1] = link;
        forged.trace.reg_fin[Reg::A1.index()] = F64(link);
        forged.trace.reg_ts[Reg::A1.index()] = F64(3);
        // The row's failed clock leaves its own state tuples unmatched, and nothing else.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(unmatched.iter().all(|&(_, block, _)| block == Framework::ALL.len()));
    }

    #[test]
    fn a_live_row_cannot_pull_a_padding_tuple() {
        // Invariant: a row of the run pulls only timestamps of the run, which have the live bit.
        //
        // Fixture state: `t0 = 5`, then `a0 = t0 + x0`; past the exit sits `jal t0, 0`, a jump to itself.
        // The two no-ops size ALU's fill so that it ends on the lone jump.
        // Mutation: a padding instance of the jump pulls `t0`'s write and pushes `(t0, 3, pc + 4)`, which the run's read pulls.
        // The read's `prev` is 3, live bit clear, and the output claims `a0 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::T0, Reg::ZERO, 5)
            .r(Add, Reg::A0, Reg::T0, Reg::ZERO)
            .i(Addi, Reg::T1, Reg::ZERO, 0)
            .i(Addi, Reg::ZERO, Reg::ZERO, 0)
            .i(Addi, Reg::ZERO, Reg::ZERO, 0)
            .exit()
            .label("spin")
            .jal(Reg::T0, "spin")
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let link = program.rv.pc_of(spin) + 4;
        let read = &mut forged.trace.rows[TableId::ALU][1];
        let write = read.prev[0];
        (read.v1, read.out, read.prev[0]) = (link, link, 3);
        let mut row = padding_jump(&program, spin);
        (row.prev[2], row.vd_old) = (write, 5);
        replace_lone_jump(&program, &mut forged, row);
        forged.output[0] = link;
        forged.trace.reg_fin[Reg::A0.index()] = F64(link);
        forged.trace.reg_fin[Reg::T0.index()] = F64(link);
        // Both rows push failed clocks: the read's, and the padding row's, each a state tuple pushed and one not pulled.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 4, "{unmatched:?}");
        assert!(unmatched.iter().all(|&(_, block, _)| block == Framework::ALL.len()));
    }

    #[test]
    fn the_final_clock_cannot_carry_a_failure() {
        // Invariant: the exit row's failed clock is refused, though it is the one the final state meets.
        //
        // Fixture state: `a0 = 42`, then the exit, which writes the sink at slot 3 of cycle 3.
        // Mutation: the exit's write pulls the tuple it pushes, the sink's seed meeting its final.
        // Its clock circuit flags the failure, and the announced final clock carries it, so the bus balances.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 42).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let exit = forged.trace.rows[TableId::ALU]
            .iter_mut()
            .find(|r| r.index == 2)
            .unwrap();
        (exit.prev[2], exit.vd_old) = (exit.ts | 3, exit.out);
        let sink = RegisterFile::SINK as usize;
        (forged.trace.reg_ts[sink], forged.trace.reg_fin[sink]) = (F64(Clock::SEED_CLOCK), F64::ZERO);
        forged.trace.ts_final |= 1 << Clock::FAIL_BIT;
        assert!(unmatched_run(&program, &forged).is_empty());
        let (proof, _) = program.prove_execution(&forged, Rate::MIN);
        assert_eq!(
            program.verify(forged.output.into(), &proof),
            Err(CpuError::FinalClock.into())
        );
    }
}
