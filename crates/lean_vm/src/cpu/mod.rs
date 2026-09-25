//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state, register and bytecode buses, bound to one field-valued commitment
//! and verified oracle-free. The machine is RISC-V ([`crate::rv`]): `pc`, register
//! numbers and addresses are integers, read as the field element with those bits, while
//! timestamps and read counts are g-powers, so every increment is a free ×g. A register
//! is one `K = F64` element. What an instruction computes is a flock circuit
//! ([`crate::class_flock`]); the tables only move words between the bytecode, the
//! registers and those circuits. Challenges and transcript scalars live in `E = F192`.

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::rv;
use crate::tables::{self, FillCtx, FlushBuilder, SEP_BYTECODE, SEP_STATE};
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use crate::witness;
use primitives::field::{F64, F192};

mod execute;
pub mod filler;
pub mod layout;
mod trace;
pub use execute::Execution;
pub use layout::*;
pub(crate) use trace::{Access, HashRow, Row, Trace};

/// Each table holds at most `2^MAX_LOG_ROWS` rows (executed instructions of its
/// class). Together with the bytecode cap these are the instance caps from “Counts
/// must not wrap” in `doc/leanvm/body/06-bus-interactions.tex`: at `ord(g) = 2^64−1`
/// the memory-soundness and count-non-wrap counting arguments are theorems only
/// for instances whose total read-flush count stays far below `2^64`, so the
/// verifier rejects any announcement exceeding them before running a reduction.
pub const MAX_LOG_ROWS: usize = 32;

/// The Fiat-Shamir IV: the program's digest, which commits to everything public and
/// fixed about the statement ([`Program::new`]), hashed with the run's public input.
/// All challenges depend on it before anything else; the run's public output seeds
/// the transcript beside it.
pub fn fs_seed(program: &Program, input: &[u64; rv::INPUT_WORDS]) -> [F64; 4] {
    let mut h = primitives::hash::Hasher::new();
    h.update(&program.digest);
    for word in input {
        h.update(&word.to_le_bytes());
    }
    fiat_shamir::digest_words(&h.finalize())
}

/// Announce the prover's sizes (every table's log height, the PCS rate) by writing
/// them onto the scalar stream, which binds them into the state and lets the verifier
/// reconstruct the layout. The public statement is not announced here; it seeds the
/// transcript at construction (see [`fs_seed`]). The boundary states are derived from
/// the program, so they need no binding.
///
/// Log heights, not row counts: every table's rows are real rows, the fill blocks
/// having run each count up to a power of two (`filler`), so a height is all there is
/// to say.
fn announce_public(ps: &mut ProverState, taus: [usize; tables::N_TABLES], log_inv_rate: usize, ts_final: F64) {
    for t in taus {
        ps.add_scalar(F192::new(t as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
    // The clock the run ended on: the final state's timestamp (§sec:state).
    ps.add_scalar(F192::from(ts_final));
}

/// Verifier side of [`announce_public`]: read the announced sizes and PCS rate from
/// the stream, validate them, and reconstruct the public [`Layout`] from the program
/// and those sizes. Nothing the program fixes is read from the prover.
fn read_public(
    vs: &mut VerifierState,
    prog: &Program,
    input: &[u64; rv::INPUT_WORDS],
) -> Result<(Layout, usize), CpuError> {
    let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
        let word = vs.next_scalar().map_err(CpuError::Transcript)?;
        if word.c1 != 0 || word.c2 != 0 {
            return Err(CpuError::PublicInput);
        }
        usize::try_from(word.c0).map_err(|_| CpuError::PublicInput)
    };

    let mut taus = [0usize; tables::N_TABLES];
    for t in &mut taus {
        *t = read_size(vs)?;
    }
    let log_inv_rate = read_size(vs)?;
    let ts_final = vs.next_scalar().map_err(CpuError::Transcript)?;
    if ts_final.c1 != 0 || ts_final.c2 != 0 {
        return Err(CpuError::PublicInput);
    }
    // The public instance caps ensure that, with `ord(g) = 2^64 − 1`, the
    // counting arguments (memory soundness, count non-wrap, exponent range checks)
    // are theorems only when the announced instance keeps the total read-flush
    // count provably below `2^64 − 1`, so reject any announcement exceeding the
    // caps BEFORE running any reduction. (A table's row count is the number of
    // times its class runs, unbounded by the bytecode size since a small loop
    // body runs many times, so it gets its own cap.)
    let floors_hold = (0..tables::N_TABLES)
        // flock sizes its argument to at least `n_blocks_log(1)` instances, and a
        // table's circuit words share that instance cube, so a height below the floor
        // describes a layout the arithmetization cannot express. `python-verifier`
        // rejects it here too.
        .all(|t| (crate::class_flock::n_blocks_log(tables::CLASSES[t], 1)..=MAX_LOG_ROWS).contains(&taus[t]));
    if !floors_hold || ::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err() {
        return Err(CpuError::PublicInput);
    }
    let l = layout(&prog.rv, input, taus, F64(ts_final.c0));
    // The caps bound each announced log on its own; what the PCS is configured for
    // is the stacked size they imply, which they do not bound.
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&l.shape.mu) {
        return Err(CpuError::PublicInput);
    }
    Ok((l, log_inv_rate))
}

/// A program as the prover and the verifier hold it.
#[derive(Clone)]
pub struct Program {
    /// The decoded text, the padding blocks included, and RAM as the run finds it.
    pub rv: rv::Program,
    /// BLAKE2s over everything public and fixed: the stacked bytecode multilinear
    /// (that table is 16·2^kbc words, tens of megabytes at production sizes, so it is
    /// hashed once here rather than per proof), the entry and halt `pc`, and RAM's
    /// size and initial words. Always set by [`Program::new`], so a `Program` cannot
    /// carry a digest inconsistent with itself.
    pub(crate) digest: [u8; 32],
    /// The padding blocks in the text ([`filler`]), whose rows bring every table's
    /// row count to a power of two. Prover-side only, and no program code reaches
    /// them, so a missing or wrong entry costs the prover a run that does not fill
    /// rather than anything a verifier would accept.
    pub filler: Vec<filler::Block>,
}

/// The digest reinterprets tables of words as bytes, which is their `to_le_bytes`
/// image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// The program of a guest's ELF executable ([`rv::Guest::from_elf`]).
    pub fn from_elf(elf: &[u8]) -> Result<Self, rv::ElfError> {
        let guest = rv::Guest::from_elf(elf)?;
        // The loader's cap is on the text alone, and [`Self::new`] appends to it, so a
        // text that only just fits the region would leave the padding blocks nowhere to
        // go and panic there. Refuse it here, where a malformed file is still an error.
        if !filler::text_fits(guest.text.len()) {
            return Err(rv::ElfError("the text leaves no room for the padding blocks"));
        }
        Ok(Self::new(
            &guest.text,
            guest.entry_pc,
            guest.image,
            guest.log_ram,
            guest.log_advice,
        ))
    }

    /// A program from its text, whose first word sits at [`rv::TEXT_BASE`], where it
    /// starts, RAM's first words, and `log2` of RAM's and of the advice's sizes in
    /// words. An illegal word and then the padding blocks ([`filler`]) follow the text.
    ///
    /// Panics if an entry is malformed ([`rv::Entry::is_well_formed`]): the `x0` and
    /// sink rules are semantics the proof system takes from the table as given, so
    /// they are checked where a table enters, on the verifier's side too.
    pub fn new(text: &[u32], entry_pc: u64, image: Vec<u64>, log_ram: usize, log_advice: usize) -> Self {
        let mut text = text.to_vec();
        // A run falling off the program's own text must trap, not slide into a block.
        text.push(0);
        let filler = filler::append_blocks(&mut text);
        let rv = rv::Program::new(&text, entry_pc, image, log_ram, log_advice);
        assert!(rv.entries.iter().all(rv::Entry::is_well_formed), "a malformed entry");

        let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let table = layout::bytecode_table(&rv);
        // SAFETY: F64 is #[repr(transparent)] over u64, so the slice's byte image is
        // exactly the concatenation of its `to_le_bytes` on little-endian targets.
        let table_bytes: &[u8] =
            unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };
        // Every variable-length part is length-framed, so the preimage parses one way.
        let mut h = primitives::hash::Hasher::new();
        h.update(b"leanvm-rv64im-1");
        h.update(&bytes(&[table.len() as u64]));
        h.update(table_bytes);
        h.update(&bytes(&[
            rv.entry_pc,
            rv.halt_pc(),
            rv.log_ram as u64,
            rv.log_advice as u64,
            rv.image.len() as u64,
        ]));
        h.update(&bytes(&rv.image));
        Self {
            digest: h.finalize(),
            rv,
            filler,
        }
    }
}

/// The whole proof is the transcript: a scalar stream plus the PCS hint
/// channels (see [`crate::transcript::Proof`]).
pub use crate::transcript::Proof;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CpuError {
    Bus(leaf::Error),
    Constraint(constraints::Error),
    Open(pcs::Error),
    PublicInput,
    Transcript(crate::transcript::Error),
    /// A class's flock sub-proof failed to verify. (A missing or malformed one
    /// surfaces as [`CpuError::Transcript`] when the shared `stream`/`openings` fail
    /// to reconstruct or fully consume.)
    Flock(flock::verifier::VerifyError),
}

/// Per side, which table (if any) owns each bus block, as `(table, column base)`.
type BlockOwners = [Vec<Option<(usize, usize)>>; 3];
/// Each table's `(column base, committed column count)` in the global schema.
type TableSpans = Vec<(usize, usize)>;

/// Blocks sourced from a table's height belong to it; the boundary, register, memory,
/// bytecode and range blocks belong to none and keep their own column claims at ζ.
fn block_owners(sizes: Sizes, sides: [usize; 3]) -> BlockOwners {
    let sch = schema();
    let src = block_kappa_sources(sizes);
    let mut it = src
        .into_iter()
        .map(|(source, _)| source.checked_sub(1).map(|t| (t, sch.base[t])));
    sides.map(|n| it.by_ref().take(n).collect())
}

/// The bus's public wiring: per side which table owns each block, and each table's
/// column span. Derived from the program and the announced layout alone, so prover
/// and verifier build it identically.
fn bus_wiring(program: &Program, l: &Layout) -> (BlockOwners, TableSpans) {
    let owners = block_owners(Sizes::of(&program.rv), [l.push.len(), l.pull.len(), l.count.len()]);
    (owners, table_spans())
}

/// The table sumcheck carries every committed column of a table, because its bus
/// forms reference the flushed ones and its constraint the rest.
fn table_spans() -> TableSpans {
    let sch = schema();
    tables::tables()
        .iter()
        .enumerate()
        .map(|(t, tb)| (sch.base[t], tb.n_committed_columns()))
        .collect()
}

/// The per-table inputs to the table sumcheck (§constraints), in schema order.
/// Prover and verifier both call this, so their column order and constraint
/// closures agree by construction.
/// The airs carry every committed column of their table, so a constraint indexes the
/// value array directly and each table's three bus forms can be
/// evaluated on the same values. The identities take the air's own `η`-range; the
/// three forms take the shared powers at [`xi_form_base`], folded into the forms'
/// coefficients once rather than multiplied onto every row's form value.
fn airs(taus: &[usize; tables::N_TABLES], forms: &[Vec<leaf::BusForm>; 3], xi: F192) -> Vec<constraints::Air<'static>> {
    let form_pows = xi_form_pows(xi);
    // Each table's slice of the batch's `η`-powers, exactly as `constraints` cuts
    // them, turned into the weights its identities want once rather than per row.
    let pows = primitives::field::powers(xi, xi_form_base());
    let offsets = constraints::xi_offsets(tables::tables().iter().map(|t| t.n_constraints()));
    tables::tables()
        .iter()
        .zip(taus)
        .enumerate()
        .map(|(t, (&table, &tau))| {
            let weights = table.constraint_weights(&pows[offsets[t]..offsets[t] + table.n_constraints()]);
            let weights_k = weights.clone();
            // One form, not three: the batch adds the three sides' evaluations
            // anyway, and summing them here is a setup cost against a dot product
            // and a product list per row per node.
            let bus = leaf::BusForm::sum((0..3).map(|s| forms[s][t].scaled(form_pows[s])));
            let bus_k = bus.clone();
            constraints::Air {
                tau,
                n_cols: table.n_committed_columns(),
                n_constraints: table.n_constraints(),
                eval: Box::new(move |_, vals, quadratic| {
                    let air = <F192 as ColVal>::lift(table.eval_constraint(&weights, vals, quadratic));
                    <F192 as ColVal>::reduce(air ^ bus.eval_unreduced(vals, quadratic))
                }),
                // The same expression over K columns: the identity's K-only products
                // stay 64-bit and the bus form becomes a mixed dot product.
                eval_k: Box::new(move |_, vals, quadratic| {
                    let air = <F64 as ColVal>::lift(table.eval_constraint_k(&weights_k, vals, quadratic));
                    <F64 as ColVal>::reduce(air ^ bus_k.eval_unreduced(vals, quadratic))
                }),
            }
        })
        .collect()
}

/// Each table's claimed sum: its identities vanish, so what its summand comes to
/// is its three bus forms, `η`-weighted. Prover-side only, to build the waiting
/// line each round; the verifier needs just their total, which it derives.
fn sigmas(bus: &[Vec<F192>; 3], form_pows: [F192; 3]) -> Vec<F192> {
    (0..tables::tables().len())
        .map(|t| (0..3).fold(F192::ZERO, |acc, s| acc + form_pows[s] * bus[s][t]))
        .collect()
}

/// Where the three bus forms sit in the batch's `η`-powers: the last three, AFTER
/// every table's identity range, and shared by all tables rather than one triple
/// per table. That sharing is what keeps the batch tied to the bus: with a common
/// `η^{base+s}` per side, the batch's target is `Σ_s η^{FORM_POWS+s}·R_s` for
/// the sides' table shares `R_s`, which the verifier DERIVES from the leaf claims
/// (`xi_form_pows`; a mismatch surfaces as [`CpuError::Constraint`]). Were the
/// powers per table, the target
/// would not factor through the `R_s` and nothing would pin the tables' share of
/// the bus.
pub fn xi_form_base() -> usize {
    tables::tables().iter().map(|t| t.n_constraints()).sum()
}

/// The three shared form powers `η^{base}, η^{base+1}, η^{base+2}`.
fn xi_form_pows(xi: F192) -> [F192; 3] {
    let base = xi_form_base();
    let pows = primitives::field::powers(xi, base + 3);
    [pows[base], pows[base + 1], pows[base + 2]]
}

/// If `col` is a circuit word's column (global index), where the word lives: the
/// class's committed packed witness, the word's place within an instance (its port),
/// and the stride between instances. These columns are virtual (uncommitted): their
/// bus evaluation claims are re-routed to slot evaluations of that witness, which is
/// the whole binding: the bus-tied value IS the flock-proven word, no separate check
/// needed.
fn flock_value_slot(col: usize) -> Option<(usize, usize, usize)> {
    let sch = schema();
    (0..tables::N_TABLES).find_map(|t| {
        let (port, _) = tables::word_columns(t)
            .into_iter()
            .find(|&(_, c)| sch.base[t] + c == col)?;
        Some((q_column(t), port, crate::class_flock::stride_log(tables::CLASSES[t])))
    })
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-table counts in [`tables::CLASSES`] order, and the
/// committed witness size, the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize, // including the padding to make every instruction count a power of two
    /// Rows per table as proven: each an exact power of two, the fill blocks having
    /// filled them (`filler`).
    pub counts: [usize; tables::N_TABLES],
    /// Rows per table before that filling, i.e. the work the program itself does.
    /// What a cost measurement wants.
    pub base_counts: [usize; tables::N_TABLES],
    pub committed: usize,
}

impl Stats {
    /// One line of per-table instruction counts and shares, largest first, followed by
    /// the committed-witness size.
    ///
    /// The counts are `base_counts`, the work the program itself does, since the proven
    /// `counts` are all exact powers of two once the fill blocks have run (`filler`) and
    /// so say nothing about the workload. Zero-count tables are omitted.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }
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
        let log2 = |n: usize| primitives::pretty_f64((n.max(1) as f64).log2());
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

/// Prove a run of the program on `input`, RAM's first words, and `advice`, the advice
/// region's first words, which the statement says nothing about: execute it (witness
/// generation), then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof, the run's public
/// output (`a0..a3` at the exit) and its [`Stats`], or the trap if the run has no proof.
/// `log_inv_rate` selects the PCS rate and is announced in the Fiat-Shamir transcript
/// before the commitment.
///
/// Panics if `advice` holds more than the program's region does (`2^log_advice` words,
/// which the program fixes) or if `log_inv_rate` is not a rate the PCS supports: both
/// are the caller's to get right, like the program itself, and neither is a trap of the run.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(
    program: &Program,
    input: [u64; rv::INPUT_WORDS],
    advice: &[u64],
    log_inv_rate: usize,
) -> Result<(Proof, [u64; 4], Stats), rv::Trap> {
    ::pcs::whir::validate_log_inv_rate(log_inv_rate).expect("valid log_inv_rate");
    // One proof is one arena phase: every transient buffer below is bump-allocated
    // and reclaimed wholesale here, rather than faulted in and unmapped again per
    // proof. Bound first so it outlives them; inert unless `init_prover` opted in.
    // The returned `Proof` is system-allocated (`ps.into_proof()` builds `Vec`s),
    // so it survives the next phase.
    let _phase = zk_alloc::enter_phase();
    let exec = crate::stage!("Execute program", || program.execute(input, advice))?;
    let log_words = program.stack_log(exec.trace.row_counts());
    if log_words > pcs::MAX_MU {
        return Err(rv::Trap::TooLong { log_words });
    }
    let (proof, stats) = prove_execution(program, &exec, &input, log_inv_rate);
    Ok((proof, exec.output, stats))
}

/// [`prove`] from a finished run. Split out so a test can hand it a run no honest
/// machine produced.
fn prove_execution(
    program: &Program,
    exec: &Execution,
    input: &[u64; rv::INPUT_WORDS],
    log_inv_rate: usize,
) -> (Proof, Stats) {
    let cycles = exec.cycles;
    let w = crate::stage!("Build witness", || program.build(exec, input));
    let counts = w.layout.taus.map(|t| 1usize << t);
    let committed_size = w.committed_size();
    // The public statement (program digest + output) seeds the transcript, so
    // every challenge depends on the exact program and what the run claims to return.
    let mut ps = ProverState::new(fs_seed(program, input), exec.output.map(F64));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.layout.taus, log_inv_rate, w.ts_final);
    let committed = crate::stage!("Commit", || {
        pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate)
    });

    // Single PCS: every class's packed flock witness is a column of `w.q`, so flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE WHIR
    // over this commitment (below). A circuit's words bind through the register and
    // bytecode buses: their virtual columns route to that witness, so no separate pin
    // claims are needed. Mirrored in `verify`.
    let (owners, spans) = bus_wiring(program, &w.layout);
    // The columns are windows into `w.q`, so both stages read them in place: the
    // table sumcheck lifts each K-column into a fresh `E` copy on the round it
    // joins and never writes the K-columns back.
    let (bus, table_claims) = {
        let l = &w.layout;
        let cols = w.columns();
        let bus = crate::stage!("Prove bus", || {
            leaf::prove_balance(&l.push, &l.pull, &l.count, &cols, &owners, &spans, &mut ps)
        });
        let table_claims = crate::stage!("Prove constraints", || {
            // One sumcheck for all the tables (§constraints).
            let table_cols: Vec<Vec<&[F64]>> = spans
                .iter()
                .map(|&(base, n)| (0..n).map(|c| cols[base + c]).collect())
                .collect();
            // The eq point is the bus GKR's ζ, not a fresh one: that is what lets the
            // batch settle the bus forms alongside the constraints.
            let xi = ps.sample();
            let form_pows = xi_form_pows(xi);
            let sigma = sigmas(&bus.sigmas, form_pows);
            constraints::prove(
                &airs(&l.taus, &bus.forms, xi),
                &table_cols,
                xi,
                &bus.point,
                &sigma,
                &mut ps,
            )
        });
        (bus, table_claims)
    };
    let l = &w.layout;

    let slots = finish_claims(l, bus.claims, &table_claims, &exec.output);

    // Run each class's flock reduction (zerocheck + lincheck) over the native layouts
    // retained from the witness build; it returns the validity claim on the class's
    // committed packed witness, discharged by the PCS below in the SAME WHIR as every
    // leanVM point claim, through a ring-switched region of its own.
    let reductions = w.reductions;
    let rings: Vec<_> = crate::stage!("Flock reductions", || {
        reductions
            .iter()
            .enumerate()
            .map(|(t, prepared)| {
                let placement = &w.layout.placements[q_column(t)];
                let reduced = prepared.prove(&mut ps);
                flock::reduction::ring_switch_open(placement.n_vars, placement.offset, &reduced)
            })
            .collect()
    });
    drop(reductions);
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &rings) });
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            base_counts: exec.base_counts,
            committed: committed_size,
        },
    )
}

/// Everything the PCS has to open, in the ORDER that feeds the batch's weights:
/// the bus's framework claims, then the zerocheck's per-table column claims, then
/// the exit's claims, each located in its committed slot. Both sides assemble
/// it here, so a claim can never shift by one element.
fn finish_claims(
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    table_claims: &[constraints::Claims],
    output: &[u64; 4],
) -> Vec<pcs::SlotClaim> {
    let mut claims = bus_claims;
    let sch = schema();
    claims.reserve(sch.n - N_SHARED);
    for (t, table) in tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            claims.push(ColumnClaim {
                col: sch.base[t] + c,
                point: table_claims[t].chi.clone(),
                value: table_claims[t].evals[c],
            });
        }
    }
    // The exit (§sec:e2e-pi): the run halted on `exit`, returning `output`.
    claims.push(final_register_claim(rv::SYSCALL_REG, rv::SYS_EXIT));
    for (reg, &value) in rv::OUTPUT_REGS.into_iter().zip(output) {
        claims.push(final_register_claim(reg, value));
    }
    slot_claims(l, claims)
}

/// What register `reg` holds when the run ends: the committed final registers at the
/// Boolean point naming `reg`. Both parties know the value, so the claim is computed
/// rather than transmitted, and the opening discharges it like any other.
fn final_register_claim(reg: u8, value: u64) -> ColumnClaim {
    ColumnClaim {
        col: REG_FIN,
        point: (0..rv::LOG_REGS)
            .map(|bit| if (reg >> bit) & 1 == 1 { F192::ONE } else { F192::ZERO })
            .collect(),
        value: F192::from(F64(value)),
    }
}

/// Verify a proof against the public statement, that the program run on `input` exits
/// returning `output`: replay the transcript, reconstruct the public layout from the announced
/// sizes, read every scalar the prover wrote and pull the PCS hints, then assert the
/// stream was fully consumed. Takes only public inputs, never the prover's witness.
pub fn verify(
    program: &Program,
    input: &[u64; rv::INPUT_WORDS],
    output: &[u64; 4],
    proof: &Proof,
) -> Result<(), CpuError> {
    verify_to_raw(program, input, output, proof).map(|_| ())
}

/// [`verify`], returning the proof it accepted with every query's Merkle path
/// written out, the form `python-verifier` reads.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify_to_raw(
    program: &Program,
    input: &[u64; rv::INPUT_WORDS],
    output: &[u64; 4],
    proof: &Proof,
) -> Result<fiat_shamir::transcript::RawProof, CpuError> {
    let mut vs = VerifierState::new(fs_seed(program, input), proof, output.map(F64));
    let (l, log_inv_rate) = read_public(&mut vs, program, input)?;
    let root = pcs::read_commitment(&mut vs).map_err(CpuError::Transcript)?;

    let (owners, spans) = bus_wiring(program, &l);
    let bus = leaf::verify_balance(&l.push, &l.pull, &l.count, &owners, &spans, &mut vs).map_err(CpuError::Bus)?;

    let zc_xi = vs.sample();
    let form_pows = xi_form_pows(zc_xi);
    // THE tie between the batch and the bus, and the reason the batch's target is
    // never transmitted. Each side's leaf claim less what its framework blocks
    // account for is the tables' share `R_s`, which the verifier just derived; the
    // batch must sum to `Σ_s η^{base+s}·R_s`. Since `η` is sampled after the `R_s`
    // are fixed, hitting that one number forces `Σ_t σ_{s,t} = R_s` on all three
    // sides. A transmitted target would be a free value in its own check, and the
    // tables' bus blocks would be settled by nothing at all.
    let target = (0..3).fold(F192::ZERO, |a, s| a + form_pows[s] * bus.totals[s]);
    let table_claims = constraints::verify(&airs(&l.taus, &bus.forms, zc_xi), zc_xi, &bus.point, target, &mut vs)
        .map_err(CpuError::Constraint)?;

    let slots = finish_claims(&l, bus.claims, &table_claims, output);

    // Replay each class's flock reduction straight off the shared stream (each scalar
    // bound as it is read) to recover its validity claim on the class's packed
    // witness, then verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`).
    let mut replays = Vec::with_capacity(tables::N_TABLES);
    for (t, &tau) in l.taus.iter().enumerate() {
        replays.push(crate::class_flock::verify_reduction(t, tau, &mut vs).map_err(CpuError::Flock)?);
    }
    let rings: Vec<_> = replays
        .iter()
        .enumerate()
        .map(|(t, replay)| {
            let placement = &l.placements[q_column(t)];
            flock::reduction::ring_switch_verify(placement.n_vars, placement.offset, &replay.claim)
        })
        .collect();
    pcs::verify(&mut vs, &slots, &rings, l.shape, log_inv_rate, &root).map_err(CpuError::Open)?;
    vs.finish().map_err(CpuError::Transcript)?;
    Ok(vs.into_raw_proof())
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// A circuit word's column is virtual: it has no committed placement. A claim
/// `word_col(r) = v` (at the table's row point `r`) is re-routed to the equal slot
/// evaluation of the class's packed witness: an ordinary claim on that committed
/// column at the point freezing the low coords to the port's bits and the high
/// coords to `r`. No downstream special-casing: it folds into the one opening like
/// every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| {
            // A circuit word: its claim at the row point `c.point` is a slot value of
            // the packed witness, a boolean-selector (strided) claim, folded sparsely
            // (the table's height, not the dense witness block).
            if let Some((q_col, slot, stride_log)) = flock_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[q_col].offset,
                    slot,
                    stride_log,
                    point: c.point,
                    value: c.value,
                };
            }
            pcs::SlotClaim::Point {
                offset: l.placements[c.col].offset,
                low_point: c.point,
                value: c.value,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::*;
    use primitives::field::g_pow;

    const INPUT: [u64; 4] = [0; 4];

    /// Reassign every range read's count, as a prover would after changing a gap, so
    /// that the range arrays balance and what is left to judge is the registers.
    fn recount_range_reads(exec: &mut Execution) {
        let mask = (1u32 << tables::RANGE_LOG) - 1;
        let mut lo = vec![F64::ONE; 1 << tables::RANGE_LOG];
        let mut hi = lo.clone();
        let t = &mut exec.trace;
        let accesses = t.rows.iter_mut().enumerate().flat_map(|(table, rows)| {
            let n = tables::CLASSES[table].n_accesses();
            rows.iter_mut().flat_map(move |r| r.accesses_mut()[..n].iter_mut())
        });
        for a in accesses {
            let (l, h) = ((a.gap & mask) as usize, (a.gap >> tables::RANGE_LOG) as usize);
            (a.count_lo, a.count_hi) = (lo[l], hi[h]);
            lo[l] = primitives::field::mul_by_g(lo[l]);
            hi[h] = primitives::field::mul_by_g(hi[h]);
        }
        (t.range_lo_count, t.range_hi_count) = (lo, hi);
    }

    /// An honest run's bus balances tuple by tuple, which says more than the proof
    /// failing would: the blocks left unmatched are named.
    #[test]
    fn an_honest_run_balances() {
        let text = Asm::new().i("addi", A0, ZERO, 5).exit().finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0);
        let w = program.build(&program.execute(INPUT, &[]).unwrap(), &INPUT);
        let unmatched = leaf::unmatched_leaves(&w.layout.push, &w.layout.pull, &w.columns());
        assert!(
            unmatched.is_empty(),
            "unmatched (side, block, row): {:?}",
            &unmatched[..unmatched.len().min(12)]
        );
    }

    /// A load cannot return what its cell does not hold. The forged run is consistent
    /// everywhere else (the circuit's instance, the register written, the output), so
    /// what is left unmatched is RAM's: the load pulls a tuple no store pushed.
    #[test]
    fn a_forged_load_unbalances_the_bus() {
        let text = Asm::new()
            .li(T0, rv::RAM_BASE + 32)
            .i("addi", T1, ZERO, 5)
            .store("sd", T1, 0, T0)
            .load("ld", A0, 0, T0)
            .exit()
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 3, 0);
        let mut forged = program.execute(INPUT, &[]).unwrap();
        assert_eq!(forged.output, [5, 0, 0, 0]);
        let load = tables::table_of(rv::Class::Load).unwrap();
        let row = forged.trace.rows[load].iter_mut().find(|r| !r.ts.is_zero()).unwrap();
        (row.ram.old, row.ram.new, row.out) = (7, 7, 7);
        forged.trace.reg_fin[A0 as usize] = F64(7);
        forged.trace.ram_fin[4] = F64(7);
        let w = program.build(&forged, &INPUT);
        let unmatched = leaf::unmatched_leaves(&w.layout.push, &w.layout.pull, &w.columns());
        // The load's pull and the store's push, which it should have met.
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
    }

    /// The point of the timestamps: a register written twice cannot be read as of its
    /// first write. The forged run is consistent everywhere else (the stale value
    /// flows into the result, the final registers and the range reads), so what fails
    /// is the register multiset itself: the first write's tuple is pulled twice.
    #[test]
    fn a_stale_read_unbalances_the_bus() {
        const RATE: usize = pcs::TEST_LOG_INV_RATE;
        let text = Asm::new()
            .i("addi", T0, ZERO, 5)
            .i("addi", T0, ZERO, 9)
            .i("addi", T1, ZERO, 3)
            .r("add", A0, T0, T1)
            .exit()
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0);
        let honest = program.execute(INPUT, &[]).unwrap();
        assert_eq!(honest.output, [12, 0, 0, 0]);
        let (proof, _) = prove_execution(&program, &honest, &INPUT, RATE);
        verify(&program, &INPUT, &honest.output, &proof).expect("the honest run verifies");

        let mut forged = program.execute(INPUT, &[]).unwrap();
        let row = &mut forged.trace.rows[0][3];
        // The read happens at cycle 4; the first write happened at cycle 1, the second at 2.
        let (stride, write_slot) = (tables::CLOCK_STRIDE, tables::REG_SLOTS[2]);
        assert_eq!(
            (row.v1, row.acc[0].x, row.acc[0].gap),
            (
                9,
                g_pow((2 * stride + write_slot) as usize),
                2 * stride - write_slot - 1
            )
        );
        (row.v1, row.out) = (5, 8);
        (row.acc[0].x, row.acc[0].gap) = (g_pow((stride + write_slot) as usize), 3 * stride - write_slot - 1);
        forged.output[0] = 8;
        forged.trace.reg_fin[A0 as usize] = F64(8);
        recount_range_reads(&mut forged);
        let refused = std::panic::catch_unwind(|| prove_execution(&program, &forged, &INPUT, RATE).0)
            .expect_err("a stale read was proven");
        let message = refused.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(
            message.contains("two products to agree"),
            "refused for another reason: {message}"
        );

        // The same forgery with an honest read is a no-op: recounting alone changes
        // no product, so the refusal above is the stale read's.
        let mut recounted = program.execute(INPUT, &[]).unwrap();
        recount_range_reads(&mut recounted);
        let (proof, _) = prove_execution(&program, &recounted, &INPUT, RATE);
        verify(&program, &INPUT, &recounted.output, &proof).expect("recounting is harmless");
    }
}
