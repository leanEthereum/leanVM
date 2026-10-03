//! A program as the proof sees it: the decoded program, its padding entries, and the digest of its public statement.
//!
//! It runs, is proven, and is verified against its digest.

use super::batch::{Batch, FormPowers};
use super::error::{CpuError, ProveError};
use super::execute::{Execution, TraceBuilder};
use super::layout::{Announcement, Lookup, Schema, Sizes, ring_terms, tau_of};
use super::padding;
use super::witness::Witness;
use crate::class_flock;
use crate::constraints;
use crate::leaf;
use crate::pcs;
use crate::rv::{self, Machine, Region};
use crate::tables::{self, CLOCK_START, CYCLE, MAX_CYCLES};
use ::pcs::pack::PACKING_WIDTH;
use fiat_shamir::transcript::{Challenger, Proof, ProverState, RawProof, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192};

/// A validated program, its padding entries, and the digest of everything public about it.
///
/// The decoded program is read-only, so the digest always describes what is proven.
#[derive(Clone)]
pub struct Program {
    /// The decoded program, the padding entries appended to its text.
    pub(super) rv: rv::Program,
    /// The digest of the public statement, which seeds the transcript.
    pub(super) digest: [u8; 32],
    /// Each table's padding entry, a no-op of its class.
    pub(super) noops: [usize; tables::N_TABLES],
}

// Why: the digest reads tables of words as bytes, which is their little-endian image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// The domain separator of the digest, versioned with the statement's format.
    const DIGEST_DOMAIN: &'static [u8] = b"leanvm-rv64im-7";

    /// The program of a guest's ELF executable.
    ///
    /// # Errors
    ///
    /// Refuses a file that is no guest, or whose text and RAM form no program.
    pub fn from_elf(elf: &[u8]) -> Result<Self, rv::ElfError> {
        let guest = rv::Guest::from_elf(elf)?;
        Self::new(
            &guest.text,
            guest.entry_pc,
            guest.image,
            guest.log_ram,
            guest.log_advice,
        )
        .map_err(rv::ElfError::Program)
    }

    /// The program of instruction words, an entry point, a RAM image and the memory sizes.
    ///
    /// The text gets an illegal word, then the padding entries.
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
    ) -> Result<Self, rv::ProgramError> {
        // Check the shape on the supplied text, before anything is appended to it.
        rv::Program::validate(text.len(), entry_pc, image.len(), log_ram, log_advice)?;

        // What gets appended must fit too: the illegal word, the padding entries, then the illegal slot and the halt slot.
        let fits = text
            .len()
            .checked_add(1 + padding::WORDS + 2)
            .and_then(usize::checked_next_power_of_two)
            .is_some_and(|total| total <= 1 << Region::TEXT.max_log_words());
        if !fits {
            return Err(rv::ProgramError::TextTooLarge);
        }

        // A run falling off the program's own text must trap, not slide into a padding entry.
        let mut text = text.to_vec();
        text.push(0);
        let noops = padding::append_noops(&mut text);
        let rv = rv::Program::new(&text, entry_pc, image, log_ram, log_advice)?;
        Ok(Self {
            digest: Self::digest_of(&rv),
            rv,
            noops,
        })
    }

    /// Run the program on `advice`, recording every row, then write out each table's padding row.
    ///
    /// Every row from a table's height up to its proven size repeats that row (§sec:jagged), which is stored once.
    ///
    /// # Errors
    ///
    /// Refuses more advice than the program's region holds, a run that traps, and one that outruns the clock.
    pub fn execute(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let max = 1 << p.log_advice();
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        let mut m = Machine::new(p, advice);
        let mut trace = TraceBuilder::new(p, m.memory().advice());

        // The clock starts on cycle 1, so that the first access comes strictly after the seeds.
        let mut ts = CLOCK_START;
        while !m.halted() {
            // The cycle count must not carry into the live bit.
            if ts >> tables::SLOT_BITS & MAX_CYCLES == MAX_CYCLES {
                return Err(ProveError::TooLong);
            }
            let step = m.step()?;
            trace.record(p, &m, step, ts);
            ts += CYCLE;
        }
        let output = m.output()?;

        // The padding rows, written out rather than executed: one per table that is short of its proven size.
        let heights = trace.row_counts();
        let mut cycles = 0;
        for (t, &height) in heights.iter().enumerate() {
            let proven = 1 << tau_of(t, height);
            cycles += proven;
            if height < proven {
                trace.pad(p, self.noops[t]);
            }
        }

        let trace = trace.finish(p, &m, heights, ts);
        Ok(Execution {
            output,
            cycles,
            base_counts: heights,
            trace,
        })
    }

    /// Prove a run of the program on `advice`, the advice region's first words, at commitment rate `rate`.
    ///
    /// The statement says nothing about the advice.
    ///
    /// Returns the proof, the run's public output (`a0` to `a3` at the exit), and its statistics.
    ///
    /// # Errors
    ///
    /// Refuses a run that traps, one too long for one proof, and more advice than the program's region holds.
    #[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate = rate.log_inv_rate()))]
    pub fn prove(&self, advice: &[u64], rate: pcs::Rate) -> Result<(Proof, [u64; 4], Stats), ProveError> {
        // One proof is one arena phase: every transient buffer below is reclaimed wholesale when it ends.
        //
        // The returned proof is system-allocated, so it survives the next phase.
        let _phase = zk_alloc::enter_phase();
        let exec = crate::stage!("Execute program", || self.execute(advice))?;
        if self.stack_sizes(exec.base_counts).0 > pcs::MAX_MU {
            return Err(ProveError::TooLong);
        }
        let (proof, stats) = self.prove_execution(&exec, rate);
        Ok((proof, exec.output, stats))
    }

    /// The statistics a proof of this run would report, from one execution and no proof.
    ///
    /// The table heights fix the layout, and the layout the committed size.
    ///
    /// # Errors
    ///
    /// What would refuse the proof itself, the rate aside.
    pub fn measure(&self, advice: &[u64]) -> Result<Stats, ProveError> {
        let exec = self.execute(advice)?;
        let (log_words, committed) = self.stack_sizes(exec.base_counts);
        if log_words > pcs::MAX_MU {
            return Err(ProveError::TooLong);
        }
        Ok(Stats {
            cycles: exec.cycles,
            counts: exec.trace.row_counts(),
            base_counts: exec.base_counts,
            committed,
        })
    }

    /// Prove a finished run, which a test may have forged.
    fn prove_execution(&self, exec: &Execution, rate: pcs::Rate) -> (Proof, Stats) {
        let w = crate::stage!("Build witness", || Witness::build(self, exec));
        let stats = Stats {
            cycles: exec.cycles,
            counts: w.layout.taus.map(|t| 1usize << t),
            base_counts: exec.base_counts,
            committed: w.committed_size(),
        };
        (self.prove_witness(w, &exec.output, rate), stats)
    }

    /// Prove a built witness, which a test may have forged.
    ///
    /// # Panics
    ///
    /// Panics if the witness's bus does not balance: an honest run's always does.
    fn prove_witness(&self, w: Witness, output: &[u64; 4], rate: pcs::Rate) -> Proof {
        // The public statement, the program's digest and the output, seeds the transcript.
        let mut ps = ProverState::new(self.fs_seed(), output.map(F64));

        // Announce the sizes, then commit, before any challenge.
        let log_inv_rate = rate.log_inv_rate().into();
        let announcement = Announcement {
            heights: w.layout.heights,
            log_inv_rate,
            ts_final: w.ts_final,
        };
        announcement.write(&mut ps);
        let committed = crate::stage!("Commit", || pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate));

        // The bus, then the one batch over every table and producer, both reading the columns in place at their committed rows.
        //
        // The batch lifts each K-column into a fresh `E` copy on its first fold and never writes the K-columns back.
        let spans = &Schema::get().spans;
        let (bus_claims, table_claims, pads) = {
            let l = &w.layout;
            let cols = w.columns();

            // Each padded table's row at its height, which its padding rows repeat (§sec:jagged).
            //
            // The bus needs its leaves, and the opening binds it to the commitment.
            let pads = padding_rows(l, &cols);
            for row in pads.iter().flatten() {
                ps.add_scalars(row);
            }
            let padding = leaf::Padding {
                heights: &l.heights,
                rows: &pads,
            };
            let mut bus = crate::stage!("Prove bus", || {
                leaf::prove_balance(&l.push, &l.pull, &l.producers, &cols, spans, padding, &mut ps)
            });
            let table_claims = crate::stage!("Prove constraints", || {
                let producers = std::mem::take(&mut bus.producers);
                let coefficients: Vec<Vec<F192>> = producers.iter().map(|p| p.coefficients.clone()).collect();

                // The batch's eq point is the bus's, which lets it settle the bus forms alongside the constraints.
                let powers = FormPowers::new(ps.sample());
                let mut sums = powers.table_sums(&bus.sigmas);
                sums.extend(producers.iter().map(|p| powers.push() * p.sigma));

                // The tables' columns in the field they are committed in, then the producers' lifted columns.
                let table_cols = spans
                    .iter()
                    .map(|&(base, n)| constraints::Columns::K((0..n).map(|c| cols[base + c]).collect()))
                    .chain(producers.into_iter().map(|p| constraints::Columns::E(p.columns)))
                    .collect();
                let batch = Batch::new(l, &bus.forms, &coefficients, &bus.weights, bus.beta, powers);
                constraints::prove(batch.airs(), table_cols, &bus.point, &sums, &mut ps)
            });
            (bus.claims, table_claims, pads)
        };

        // Nothing reads a table column again: the reductions have their own tables, and the opening reads the committed stack.
        drop(w.live);
        drop(w.virt);
        let l = &w.layout;
        let slots = l.opening_claims(bus_claims, &table_claims, &pads, output);

        // Each circuit's flock reduction, every class circuit then every clock circuit.
        //
        // Each leaves a validity claim on its packed witness, discharged in the same opening through ring-switched terms of its own.
        let reductions = w.reductions;
        let mut rings: Vec<_> = crate::stage!("Flock reductions", || {
            reductions
                .iter()
                .enumerate()
                .map(|(f, prepared)| {
                    let reduced = prepared.prove(&mut ps);
                    pcs::RingSwitchClaim {
                        terms: ring_terms(l.witness_column(f), &reduced.suffix_point),
                        suffix_point: reduced.suffix_point,
                        s_hat_v: Some(reduced.s_hat_v),
                    }
                })
                .collect()
        });
        drop(reductions);

        // Each producer's multiplicity column, ring-switched too.
        for (p, claims) in l.producers.iter().zip(&table_claims[tables::N_TABLES..]) {
            rings.push(pcs::RingSwitchClaim {
                terms: ring_terms(l.multiplicity_column(p), &claims.chi),
                suffix_point: claims.chi.clone(),
                s_hat_v: Some(claims.evals_padded::<PACKING_WIDTH>().to_vec()),
            });
        }
        crate::stage!("PCS open", || pcs::open(&mut ps, &committed, &w.q, &slots, &rings));
        ps.into_proof()
    }

    /// Verify a proof that the program exits returning `output`.
    ///
    /// It takes only public inputs, never the prover's witness.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    pub fn verify(&self, output: &[u64; 4], proof: &Proof) -> Result<(), CpuError> {
        self.verify_to_raw(output, proof).map(|_| ())
    }

    /// Verify a proof, and return it with every query's Merkle path written out, the form the Python verifier reads.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    #[tracing::instrument(name = "Verify", skip_all)]
    pub fn verify_to_raw(&self, output: &[u64; 4], proof: &Proof) -> Result<RawProof, CpuError> {
        // The public statement seeds the transcript, as on the prover's side.
        let mut vs = VerifierState::new(self.fs_seed(), proof, output.map(F64));

        // The announced sizes, then the layout they describe, then the commitment.
        let announcement = Announcement::read(&mut vs)?;
        let l = announcement.layout(&self.rv)?;
        let root = pcs::read_commitment(&mut vs)?;

        // Each padded table's row at its height, which its padding rows repeat (§sec:jagged): the bus takes its leaves from it, and the opening binds it.
        let pads: Vec<Option<Vec<F192>>> = (Schema::get().spans.iter().enumerate())
            .map(|(t, &(_, n))| l.padded(t).then(|| vs.next_scalars(n)).transpose())
            .collect::<Result<_, _>>()?;
        let padding = leaf::Padding {
            heights: &l.heights,
            rows: &pads,
        };
        let bus = leaf::verify_balance(&l.push, &l.pull, &l.producers, &Schema::get().spans, padding, &mut vs)
            .map_err(CpuError::Bus)?;

        // The tie between the batch and the bus, and why the batch's target is never sent.
        //
        // Each side's leaf claim, less its framework blocks, is the tables' and producers' share `R_s`.
        //
        // The verifier just derived those, and the batch must sum to `sum_s xi^s * R_s`.
        //
        // The challenge `xi` comes after the `R_s` are fixed, so hitting that one number forces each side's share.
        let powers = FormPowers::new(vs.sample());
        let target = powers.combine(bus.totals);
        let batch = Batch::new(&l, &bus.forms, &bus.producers, &bus.weights, bus.beta, powers);
        let table_claims =
            constraints::verify(batch.airs(), &bus.point, target, &mut vs).map_err(CpuError::Constraint)?;
        let slots = l.opening_claims(bus.claims, &table_claims, &pads, output);

        // Replay each circuit's flock reduction off the stream, to recover its validity claim on its packed witness.
        let mut replays = Vec::with_capacity(class_flock::N_FLOCKS);
        for f in 0..class_flock::N_FLOCKS {
            let (t, part) = class_flock::flock(f);
            let replay = class_flock::verify_reduction(f, l.taus[t], &mut vs).map_err(|error| CpuError::Flock {
                table: tables::CLASSES[t].name,
                part,
                error,
            })?;
            replays.push(replay);
        }

        // The ring-switched claims: each packed witness, then each producer's multiplicity column.
        let producer_claims = &table_claims[tables::N_TABLES..];
        let slices: Vec<[F192; PACKING_WIDTH]> = producer_claims.iter().map(|claims| claims.evals_padded()).collect();
        let witnesses = replays
            .iter()
            .enumerate()
            .map(|(f, replay)| pcs::RingSwitchVerifyClaim {
                suffix_point: &replay.claim.suffix_point,
                s_hat_v: replay
                    .claim
                    .s_hat_v
                    .as_slice()
                    .try_into()
                    .expect("ring-switch has 64 slices"),
                terms: ring_terms(l.witness_column(f), &replay.claim.suffix_point),
            });
        let producers = l
            .producers
            .iter()
            .zip(producer_claims)
            .zip(&slices)
            .map(|((p, claims), slices)| pcs::RingSwitchVerifyClaim {
                suffix_point: &claims.chi,
                s_hat_v: slices,
                terms: ring_terms(l.multiplicity_column(p), &claims.chi),
            });
        let rings: Vec<_> = witnesses.chain(producers).collect();

        // The one opening, then nothing may be left on the stream.
        pcs::verify(&mut vs, &slots, &rings, l.shape, announcement.log_inv_rate, &root).map_err(CpuError::Open)?;
        vs.finish()?;
        Ok(vs.into_raw_proof())
    }

    /// The decoded text, memory image and region sizes.
    pub const fn rv(&self) -> &rv::Program {
        &self.rv
    }

    /// BLAKE2s over the decoded text, the entry and halt addresses, the region sizes and the initial RAM image.
    ///
    /// ELF metadata is no part of it, and every illegal encoding decodes to the same entry.
    pub const fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The transcript's seed: the digest, as words.
    ///
    /// Every challenge depends on it, and the run's public output seeds the transcript beside it.
    pub fn fs_seed(&self) -> [F64; 4] {
        fiat_shamir::digest_words(&self.digest)
    }

    /// The base-two logarithm of the stacked witness, and its committed size, for a run of these table heights.
    ///
    /// The layout depends on the program and the heights alone, so no witness is built.
    pub(super) fn stack_sizes(&self, heights: [usize; tables::N_TABLES]) -> (usize, usize) {
        let (placements, shape) = Sizes::of(&self.rv).stack(heights);
        (shape.mu, crate::witness::committed_len(&placements))
    }

    /// The digest of `rv`'s public statement.
    ///
    /// Every variable-length part is length-framed, so the preimage parses one way.
    fn digest_of(rv: &rv::Program) -> [u8; 32] {
        let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let table = Lookup::Bytecode.table(rv);

        // SAFETY: F64 is #[repr(transparent)] over u64.
        // So the slice's bytes are the concatenation of its words' little-endian bytes on this target.
        let table_bytes: &[u8] =
            unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };

        // The domain, the bytecode table, then the scalars and the image.
        let mut h = primitives::hash::Hasher::new();
        h.update(Self::DIGEST_DOMAIN);
        h.update(&bytes(&[table.len() as u64]));
        h.update(table_bytes);
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

/// Each table's columns on the row at its height, the one its padding rows repeat, for a table that has padding rows (§sec:jagged).
fn padding_rows(l: &super::Layout, cols: &[&[F64]]) -> Vec<Option<Vec<F192>>> {
    (Schema::get().spans.iter().enumerate())
        .map(|(t, &(base, n))| {
            l.padded(t)
                .then(|| (0..n).map(|c| F192::from(cols[base + c][l.heights[t]])).collect())
        })
        .collect()
}

/// What a run costs: its cycles, its rows per table, and its committed witness size.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stats {
    /// The rows proven, padding rows included.
    pub cycles: usize,
    /// The rows per table as proven: each a power of two, the padding rows having filled them.
    pub counts: [usize; tables::N_TABLES],
    /// The rows per table before that padding, each table's height: the work the program itself does.
    pub base_counts: [usize; tables::N_TABLES],
    /// The committed witness size: the committed pieces' total length, before the stack's zero pad.
    pub committed: usize,
}

impl Stats {
    /// One line of per-table counts and shares, largest first, then the committed size.
    ///
    /// The counts are the program's own work: the proven counts are all powers of two, which say nothing of it.
    ///
    /// Tables with no rows are left out.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }

        // Each table's share of the program's own rows, largest first.
        let base_cycles: usize = self.base_counts.iter().sum();
        let mut shares: Vec<(&str, usize)> = tables::CLASSES
            .iter()
            .zip(&self.base_counts)
            .filter(|&(_, &c)| c > 0)
            .map(|(spec, &c)| (spec.name, c))
            .collect();
        shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
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
    use crate::cpu::layout::{Framework, Shared, committed_rows};
    use crate::leaf::Coord;
    use crate::rv::asm::*;
    use crate::rv::{InstructionClass, Reg};
    use crate::tables::SEP_BYTECODE;

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
                Err(rv::ProgramError::EntryPoint)
            ));
        }

        // An empty text has no entry point at all.
        assert!(matches!(
            Program::new(&[], Region::TEXT.base(), vec![], 0, 0),
            Err(rv::ProgramError::EntryPoint)
        ));

        // An image larger than RAM, RAM or the advice beyond its region.
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![0, 0], 0, 0),
            Err(rv::ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![], usize::MAX, 0),
            Err(rv::ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, Region::TEXT.base(), vec![], 0, usize::MAX),
            Err(rv::ProgramError::AdviceSize)
        ));
    }

    #[test]
    fn the_text_region_reserves_the_padding_entries() {
        // The largest text that fits, after the illegal word, the padding entries, and the two slots `rv` appends.
        let limit = (1 << Region::TEXT.max_log_words()) - 1 - padding::WORDS - 2;
        let program = |words: usize| Program::new(&vec![0; words], Region::TEXT.base(), vec![], 0, 0);
        assert!(program(limit).is_ok());

        // One word more no longer fits.
        assert!(matches!(program(limit + 1), Err(rv::ProgramError::TextTooLarge)));
    }

    #[test]
    fn illegal_encodings_share_one_identity() {
        // Two different illegal words decode to the same entry, so to the same digest.
        let program = Program::new(&[0], Region::TEXT.base(), vec![], 0, 0).unwrap();
        let same = Program::new(&[u32::MAX], Region::TEXT.base(), vec![], 0, 0).unwrap();
        assert_eq!(program.digest(), same.digest());

        // Running it traps on the first instruction.
        assert_eq!(
            rv::Machine::new(program.rv(), &[]).run_for(1),
            Err(rv::Trap::Illegal {
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
        leaf::unmatched_leaves(
            &w.layout.push,
            &w.layout.pull,
            &w.layout.producers,
            &w.columns(),
            &w.layout.heights,
        )
    }

    /// Forge a committed column of a built witness at its committed rows, and its pieces of the committed stack with it.
    fn forge(w: &mut Witness, col: usize, edit: impl FnOnce(&mut [F64])) {
        let c = w.layout.placements[col]
            .column()
            .expect("a forged column is committed")
            .clone();
        match w.windows[col] {
            Some(window) => {
                let rows = &mut w.live[window.offset..window.offset + window.len];
                edit(rows);
                for p in &c.pieces {
                    let len = 1 << p.log_rows;
                    w.q[p.offset..p.offset + len].copy_from_slice(&rows[p.first_row..p.first_row + len]);
                }
            }
            None => edit(&mut w.q[c.pieces[0].offset..c.pieces[0].offset + (1 << c.row_vars)]),
        }
    }

    /// The prover refuses a witness whose bus does not balance: its two products differ.
    fn assert_unbalanced(program: &Program, w: Witness, output: &[u64; 4]) {
        let refused = std::panic::catch_unwind(|| program.prove_witness(w, output, pcs::Rate::MIN))
            .expect_err("an unbalanced bus was proven");
        let message = refused.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(
            message.contains("two products to agree"),
            "refused for another reason: {message}"
        );
    }

    /// Put `row` among the ALU's live rows, ahead of its padding row: the table's height grows by one to take it.
    fn add_live_row(exec: &mut Execution, row: Row) {
        let height = exec.trace.heights[0];
        let tau = tau_of(0, height);
        assert!(height < 1 << tau, "the ALU has a padding row to take");
        set_height(exec, 0, height + 1, tau);
        exec.trace.rows[0][height] = row;
    }

    /// Move table `t`'s height to `height`, its rows past it repeating the row now at it, on a cube of `2^tau` rows.
    fn set_height(exec: &mut Execution, t: usize, height: usize, tau: usize) {
        let rows = &mut exec.trace.rows[t];
        let at = rows[height.min(rows.len() - 1)].clone();
        rows.truncate(height);
        rows.push(at);
        rows.truncate(committed_rows(height, tau));
        exec.trace.heights[t] = height;
    }

    /// The row a jump to itself makes, `jal rd, 0` at entry `index`, at clock zero.
    fn padding_jump(program: &Program, index: usize) -> Row {
        let e = &program.rv.entries()[index];
        let rv::Outcome { out, taken, access } = e.evaluate(0, 0, 0);
        let ram = access.unwrap_or_default();
        let slots: Vec<u64> = tables::ALU.slots().into_iter().map(u64::from).collect();
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
            hash: None,
            ext: None,
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
    fn only_ecall_can_terminate_the_state_channel() {
        // The prototype loads an address past the text's base, so its `li` takes as many words as loading the halt address does.
        let prototype = Asm::new()
            .li(Reg::T0, Region::TEXT.base() + 4)
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .finish();
        let halt = Program::new(&prototype, Region::TEXT.base(), vec![], 2, 0)
            .expect("valid exit program")
            .rv
            .halt_pc();
        let original = Asm::new()
            .li(Reg::T0, halt)
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .finish();
        let honest_program = Program::new(&original, Region::TEXT.base(), vec![], 2, 0).expect("valid exit program");
        assert_eq!(honest_program.rv.halt_pc(), halt);
        let exit_index = original.len() - 1;
        let pc = honest_program.rv.pc_of(exit_index);
        for instruction in [
            Instruction::j(Reg::ZERO, (halt - pc) as i32),
            Instruction::i(Opcode::Jalr, 0, Reg::ZERO, Reg::T0, 0),
        ] {
            let mut text = original.clone();
            text[exit_index] = instruction.bits();
            let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid jump program");
            assert!(matches!(program.execute(&[]), Err(ProveError::Trap(rv::Trap::Illegal { pc })) if pc == halt));

            // Forge the terminal row directly, bypassing the interpreter's trap.
            let mut execution = honest_program.execute(&[]).unwrap();
            let entry = program.rv.entries()[exit_index];
            if entry.jalr {
                // The jump reads `t0` in slot 0, where the exit read `x0`, which leaves `x0`'s slot-1 read pulling the cycle before.
                let ts = tables::CLOCK_START + exit_index as u64 * tables::CYCLE;
                let previous = original[..exit_index]
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(i, &word)| {
                        (rv::Entry::decode(word, program.rv.pc_of(i)).ad == Reg::T0.index() as u8)
                            .then_some((tables::CLOCK_START + i as u64 * tables::CYCLE) | 3)
                    })
                    .unwrap();
                let row = &mut execution.trace.rows[0][exit_index];
                (row.v1, row.out, row.taken) = (halt, halt, false);
                (row.prev[0], row.prev[1]) = (previous, ts - tables::CYCLE + 1);
                execution.trace.reg_ts[Reg::T0.index()] = F64(ts);
            }
            execution.trace.reg_fin[rv::RegisterFile::SINK as usize] = F64(pc + 4);
            let witness = Witness::build(&program, &execution);
            let unmatched = unmatched(&witness);
            // The final state on the pull side, and the ALU's state push, the push side's
            // first block past its four framework blocks.
            assert_eq!(unmatched.len(), 2, "{unmatched:?}");
            assert!(unmatched.iter().all(|(_, block, _)| *block == 0 || *block == 4));
            assert_unbalanced(&program, witness, &execution.output);
        }
    }

    /// The two families of loads and stores: the doubleword ones, whose value is a column, and the narrower ones, whose
    /// value is a circuit word. Each as `(store, load, their classes)`.
    const STORE_LOAD: [(StoreOp, LoadOp, [rv::Class; 2]); 2] = [
        (Sd, Ld, [rv::Class::Sd, rv::Class::Ld]),
        (Sw, Lw, [rv::Class::Store, rv::Class::Load]),
    ];

    /// `t1 = 5` stored in RAM's fifth word then loaded into `a0`, run honestly, and its store's and load's tables.
    fn store_then_load(store: StoreOp, load: LoadOp, classes: [rv::Class; 2]) -> (Program, Execution, [usize; 2]) {
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
        (program, run, classes.map(|c| tables::table_of(c).unwrap()))
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
        // Fixture state: a = (3, 5, 7) at RAM's base, the base-field b = 9 at word 4, c at word 8.
        let image = vec![3, 5, 7, 0, 9, 0, 0, 0];
        let ram = Region::RAM.base();
        let text = Asm::new()
            .li(Reg::T0, ram)
            .li(Reg::T1, ram + 32)
            .li(Reg::T2, ram + 64)
            .ext(Extmulk, Reg::T2, Reg::T0, Reg::T1)
            .exit()
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), image, 4, 0).expect("valid instruction program");
        assert!(unmatched_run(&program, &program.execute(&[]).unwrap()).is_empty());

        // Mutation: the row claims b_1 = 1, as if b were (9, 1, 0), and c and RAM follow it.
        let mut forged = program.execute(&[]).unwrap();
        let ext = tables::table_of(rv::Class::Ext).unwrap();
        let row = forged.trace.rows[ext].iter_mut().find(|r| r.ts != 0).unwrap();
        let x = row.ext.as_mut().unwrap();
        x.instance.limbs[4] = 1;
        x.result = x.instance.eval();
        for (k, word) in x.result.c.into_iter().enumerate() {
            forged.trace.ram_fin[8 + k] = F64(word);
        }

        // Two tuples on each side: b_1's read of x0, and b_2's read right after it.
        //
        //     b_1 pulls a 1 nothing pushed, and pushes a 1
        //     b_2 pulls the 0 it found, which nothing pushed, and leaves the 1 unpulled
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 4, "{unmatched:?}");
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
        let (program, honest, tables) = store_then_load(Sd, Ld, [rv::Class::Sd, rv::Class::Ld]);
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
        for class in [rv::Class::Ld, rv::Class::Sd] {
            let text = |offset| {
                let mut a = Asm::new();
                a.li(Reg::T0, cell).i(Addi, Reg::T1, Reg::ZERO, 5);
                match class {
                    rv::Class::Ld => a.load(Ld, Reg::A0, offset, Reg::T0),
                    _ => a.store(Sd, Reg::T1, offset, Reg::T0),
                };
                a.exit().finish()
            };
            let program =
                |offset| Program::new(&text(offset), Region::TEXT.base(), vec![], 3, 0).expect("valid program");
            let misaligned = program(1);
            assert!(matches!(
                misaligned.execute(&[]),
                Err(ProveError::Trap(rv::Trap::Misaligned { address, .. })) if address == cell + 1
            ));
            let mut forged = program(0).execute(&[]).unwrap();
            let row = real(&mut forged.trace.rows[tables::table_of(class).unwrap()]);
            row.ram.address = cell + 1;
            (forged.trace.ram_fin[4], forged.trace.ram_ts[4]) = (F64::ZERO, F64(tables::SEED_CLOCK));
            let w = Witness::build(&misaligned, &forged);
            // The access's pull and push, at an address no cell has.
            assert_eq!(unmatched(&w).len(), 2, "{class:?}: {:?}", unmatched(&w));
            assert_unbalanced(&misaligned, w, &forged.output);
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
        let (proof, _) = program.prove_execution(&honest, pcs::Rate::MIN);
        program.verify(&honest.output, &proof).expect("the honest run verifies");

        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[0][3];
        // The read happens at cycle 4; the first write happened at cycle 1, the second at 2, each in slot 3.
        let write = |cycle: u64| tables::SEED_CLOCK | (cycle * tables::CYCLE) | 3;
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
        assert_unbalanced(&program, w, &forged.output);
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
        let alu = tables::table_of(rv::Class::Alu).unwrap();
        let row = exec.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        let mut w = Witness::build(&program, &exec);
        let offset = Schema::get().spans[alu].0 + tables::branch_offset_column(alu);
        forge(&mut w, offset, |col| col[row] = F64(8));
        forge(&mut w, Shared::BytecodeMult.col(), |col| col[0].0 -= 1);

        let unmatched = unmatched(&w);
        assert_eq!(unmatched.len(), 1, "{unmatched:?}");
        let (side, block, at) = unmatched[0];
        assert_eq!((side, at), ("pull", row));
        assert!(matches!(w.layout.pull[block].coords[0], Coord::Const(sep) if sep == SEP_BYTECODE));
        assert_unbalanced(&program, w, &exec.output);
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
                forge(&mut w, col, |col| col[0].0 ^= flip);
                let unmatched = unmatched(&w);
                assert!(!unmatched.is_empty());
                let producer = w.layout.push.len() + p;
                assert!(
                    unmatched
                        .iter()
                        .all(|&(side, block, row)| side == "pull" || (block, row) == (producer, 0)),
                    "{unmatched:?}"
                );
                assert_unbalanced(&program, w, &exec.output);
            }
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
        let row = &mut forged.trace.rows[0][1];
        (row.v1, row.out, row.prev[0]) = (9, 9, row.ts);
        forged.output[0] = 9;
        forged.trace.reg_fin[Reg::A0.index()] = F64(9);
        forged.trace.reg_ts[Reg::T0.index()] = F64(tables::CLOCK_START | 3);
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
        // Mutation: an instance of it at clock zero joins the run's rows, its write pulling `a1`'s seed.
        // `a1`'s final value is what it pushes, so the output claims `a1 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .label("spin")
            .jal(Reg::A1, "spin")
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let mut row = padding_jump(&program, spin);
        (row.prev[2], row.vd_old) = (tables::SEED_CLOCK, 0);
        add_live_row(&mut forged, row);
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
        // Mutation: an instance of the jump at clock zero joins the run's rows, pulling `t0`'s write and pushing `(t0, 3, pc + 4)`, which the run's read pulls.
        // The read's `prev` is 3, live bit clear, and the output claims `a0 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::T0, Reg::ZERO, 5)
            .r(Add, Reg::A0, Reg::T0, Reg::ZERO)
            .i(Addi, Reg::T1, Reg::ZERO, 0)
            .exit()
            .label("spin")
            .jal(Reg::T0, "spin")
            .finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let link = program.rv.pc_of(spin) + 4;
        let read = &mut forged.trace.rows[0][1];
        let write = read.prev[0];
        (read.v1, read.out, read.prev[0]) = (link, link, 3);
        let mut row = padding_jump(&program, spin);
        (row.prev[2], row.vd_old) = (write, 5);
        add_live_row(&mut forged, row);
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
        let exit = forged.trace.rows[0].iter_mut().find(|r| r.index == 2).unwrap();
        (exit.prev[2], exit.vd_old) = (exit.ts | 3, exit.out);
        let sink = rv::RegisterFile::SINK as usize;
        (forged.trace.reg_ts[sink], forged.trace.reg_fin[sink]) = (F64(tables::SEED_CLOCK), F64::ZERO);
        forged.trace.ts_final |= 1 << tables::FAIL_BIT;
        assert!(unmatched_run(&program, &forged).is_empty());
        let (proof, _) = program.prove_execution(&forged, pcs::Rate::MIN);
        assert_eq!(program.verify(&forged.output, &proof), Err(CpuError::FinalClock));
    }

    #[test]
    fn a_forged_height_unbalances_the_bus() {
        // Invariant: a table's height names exactly the rows on the bus, so moving it moves rows on or off.
        //
        // Fixture state: `a0 = 5`, then the exit, each an ALU row.
        // Mutation: the ALU's height one lower, the exit now the row its padding repeats, or one higher, a padding no-op joining the run's rows.
        // Either way the rows past it repeat the row at it, as the commitment says.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        for delta in [-1, 1] {
            let mut forged = program.execute(&[]).unwrap();
            let tau = tau_of(0, forged.trace.heights[0]);
            let height = forged.trace.heights[0].checked_add_signed(delta).unwrap();
            set_height(&mut forged, 0, height, tau);
            let w = Witness::build(&program, &forged);
            assert!(!unmatched(&w).is_empty());
            assert_unbalanced(&program, w, &forged.output);
        }
    }

    #[test]
    fn an_announced_height_past_the_cap_is_refused() {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let (mut proof, _) = program.prove_execution(&exec, pcs::Rate::MIN);
        // The stream opens on the heights, the ALU's first.
        proof.stream[0] = F192::new((1 << crate::cpu::MAX_LOG_ROWS) + 1, 0, 0);
        assert!(matches!(
            program.verify(&exec.output, &proof),
            Err(CpuError::TableHeight { table: "ALU", .. })
        ));
    }

    /// An honest witness of `a0 = 5` and its ALU table's branch-offset column, which is committed rather than a circuit word.
    fn witness_and_column() -> (Program, Execution, Witness, usize) {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let w = Witness::build(&program, &exec);
        let alu = tables::table_of(rv::Class::Alu).unwrap();
        let col = Schema::get().spans[alu].0 + tables::branch_offset_column(alu);
        assert!(w.layout.placements[col].column().is_some());
        (program, exec, w, col)
    }

    #[test]
    fn a_padding_row_off_the_committed_one_is_refused() {
        // Invariant: the rows from a table's height on are the row at it, which the commitment holds once.
        //
        // Mutation: the padding row the bus and the table sumcheck read, and every row past it with it, differs from the committed one.
        // The bus takes it off again, but the table sumcheck sums it, and the commitment disagrees.
        let (program, exec, mut w, col) = witness_and_column();
        let padding = w.layout.heights[0];
        let window = w.windows[col].unwrap();
        assert_eq!(window.len, padding + 1);
        w.live[window.offset + padding] += F64(1);
        let proof = program.prove_witness(w, &exec.output, pcs::Rate::MIN);
        assert!(matches!(program.verify(&exec.output, &proof), Err(CpuError::Open(_))));
    }

    #[test]
    fn a_wrong_committed_word_is_refused() {
        // Invariant: what the claims are made of is what the committed stack holds.
        //
        // Mutation: the committed stack's word of a live row differs from the column the bus and the sumcheck read.
        let (program, exec, mut w, col) = witness_and_column();
        let piece = w.layout.placements[col].column().unwrap().pieces[0];
        assert_eq!(piece.first_row, 0);
        w.q[piece.offset] += F64(1);
        let proof = program.prove_witness(w, &exec.output, pcs::Rate::MIN);
        assert!(matches!(program.verify(&exec.output, &proof), Err(CpuError::Open(_))));
    }
}
