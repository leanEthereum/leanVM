//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state, register and bytecode buses, bound to one field-valued commitment
//! and verified oracle-free. The machine is RISC-V ([`crate::rv`]): `pc`, register
//! numbers, addresses and timestamps are integers, read as the field element with those
//! bits. A register
//! is one `K = F64` element. What an instruction computes is a flock circuit
//! ([`crate::class_flock`]); the tables only move words between the bytecode, the
//! registers and those circuits. Challenges and transcript scalars live in `E = F192`.

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord, Producer};
use crate::pcs;
use crate::rv;
use crate::tables::{self, FillCtx, SEP_BYTECODE, SEP_STATE};
use crate::witness;
use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192};

mod execute;
pub mod filler;
pub mod layout;
mod sparse;
mod trace;
pub use execute::Execution;
pub use layout::*;
pub(crate) use trace::{HashRow, Row, Trace};

/// Each table holds at most `2^MAX_LOG_ROWS` rows (executed instructions of its
/// class). Together with the bytecode cap these are the instance caps of
/// `doc/leanvm/body/06-bus-interactions.tex`, which the verifier checks before running a
/// reduction. No counting argument needs them: they bound the layout an announcement describes.
pub const MAX_LOG_ROWS: usize = 32;

/// The Fiat-Shamir IV: the program's digest, which commits to everything public and
/// fixed about the statement ([`Program::new`]). All challenges depend on it before
/// anything else; the run's public output seeds the transcript beside it.
pub fn fs_seed(program: &Program) -> [F64; 4] {
    fiat_shamir::digest_words(&program.digest)
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
fn announce_public(
    ps: &mut ProverState,
    taus: [usize; tables::N_TABLES],
    log_inv_rate: usize,
    ts_final: u64,
    sparse: Option<sparse::Boundary>,
) {
    for t in taus {
        ps.add_scalar(F192::new(t as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
    // The clock the run ended on: the final state's timestamp (§sec:state).
    ps.add_scalar(F192::new(ts_final, 0, 0));
    ps.add_scalar(F192::new(sparse.map_or(0, |s| s.tau + 1) as u64, 0, 0));
    ps.add_scalar(F192::new(sparse.map_or(0, |s| s.end), 0, 0));
}

/// Verifier side of [`announce_public`]: read the announced sizes and PCS rate from
/// the stream, validate them, and reconstruct the public [`Layout`] from the program
/// and those sizes. Nothing the program fixes is read from the prover.
fn read_public(vs: &mut VerifierState, prog: &Program) -> Result<(Layout, usize), CpuError> {
    let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
        let word = vs.next_scalar()?;
        if word.c1 != 0 || word.c2 != 0 {
            return Err(CpuError::NonCanonicalSize);
        }
        usize::try_from(word.c0).map_err(|_| CpuError::NonCanonicalSize)
    };

    let mut taus = [0usize; tables::N_TABLES];
    for t in &mut taus {
        *t = read_size(vs)?;
    }
    let log_inv_rate = read_size(vs)?;
    let ts_final = vs.next_scalar()?;
    // A live clock at slot zero: neither a padding row's clock nor a failed row's can end the run.
    if ts_final.c0 >> tables::LIVE_BIT != 1 || ts_final.c0 % tables::CYCLE != 0 || ts_final.c1 != 0 || ts_final.c2 != 0
    {
        return Err(CpuError::FinalClock);
    }
    // Reject an announcement exceeding the public instance caps BEFORE running any
    // reduction. (A table's row count is the number of
    // times its class runs, unbounded by the bytecode size since a small loop
    // body runs many times, so it gets its own cap.)
    for (spec, &log_rows) in tables::CLASSES.iter().zip(&taus) {
        // flock sizes its argument to at least `n_blocks_log(1)` instances, and a
        // table's circuit words share that instance cube, so a height below the floor
        // describes a layout the arithmetization cannot express. `python-verifier`
        // rejects it here too.
        let min = crate::class_flock::n_blocks_log(spec, 1);
        if !(min..=MAX_LOG_ROWS).contains(&log_rows) {
            return Err(CpuError::TableHeight {
                table: spec.name,
                log_rows,
                min,
                max: MAX_LOG_ROWS,
            });
        }
    }
    if !u8::try_from(log_inv_rate).is_ok_and(|r| pcs::Rate::new(r).is_ok()) {
        return Err(CpuError::Rate { log_inv_rate });
    }
    // Zero announces dense RAM, and `tau + 1` a sparse boundary of 2^tau rows ending at `end`.
    let (height, end) = (read_size(vs)?, read_size(vs)? as u64);
    let sparse = match height.checked_sub(1) {
        None if end == 0 => None,
        Some(tau)
            if (sparse::MIN_TAU..=prog.rv.log_ram()).contains(&tau)
                && (sparse::start(&prog.rv)..rv::RAM_BASE + (8 << prog.rv.log_ram())).contains(&end)
                && end.is_multiple_of(8) =>
        {
            Some(sparse::Boundary { tau, end })
        }
        _ => return Err(CpuError::SparseBoundary { height, end }),
    };
    let l = layout(&prog.rv, taus, ts_final.c0, sparse);
    // The caps bound each announced log on its own; what the PCS is configured for
    // is the stacked size they imply, which they do not bound.
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&l.shape.mu) {
        return Err(CpuError::WitnessSize { mu: l.shape.mu });
    }
    Ok((l, log_inv_rate))
}

/// A validated program and its cached public-statement digest.
///
/// The decoded program is read-only, so the digest always describes what is proven.
///
/// ```compile_fail
/// # use leanvm_core::cpu::Program;
/// fn change_image(program: &mut Program) {
///     program.rv.image().clear();
/// }
/// ```
///
/// ```compile_fail
/// # use leanvm_core::cpu::Program;
/// fn change_image(program: &mut Program) {
///     program.rv().image.clear();
/// }
/// ```
#[derive(Clone)]
pub struct Program {
    rv: rv::Program,
    digest: [u8; 32],
    filler: Vec<filler::Block>,
}

/// The digest reinterprets tables of words as bytes, which is their `to_le_bytes`
/// image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// The decoded text, memory image and region sizes, for inspection or interpretation.
    pub const fn rv(&self) -> &rv::Program {
        &self.rv
    }

    /// BLAKE2s over the decoded text, entry, halt, region sizes and initial RAM image.
    ///
    /// ELF metadata and unsupported instruction encodings normalized to the same illegal entry are not part of the identity.
    pub const fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The program of a guest's ELF executable ([`rv::Guest::from_elf`]).
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

    /// Construct an immutable executable from instruction words and a RAM image.
    ///
    /// Rejects an entry outside the supplied text and sizes exceeding the VM's regions.
    pub fn new(
        text: &[u32],
        entry_pc: u64,
        image: Vec<u64>,
        log_ram: usize,
        log_advice: usize,
    ) -> Result<Self, rv::ProgramError> {
        rv::Program::validate(text.len(), entry_pc, image.len(), log_ram, log_advice)?;
        if !filler::text_fits(text.len()) {
            return Err(rv::ProgramError::TextTooLarge);
        }
        let mut text = text.to_vec();
        // A run falling off the program's own text must trap, not slide into a block.
        text.push(0);
        let filler = filler::append_blocks(&mut text);
        let rv = rv::Program::new(&text, entry_pc, image, log_ram, log_advice)?;

        let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let table = layout::bytecode_table(&rv);
        // SAFETY: F64 is #[repr(transparent)] over u64, so the slice's byte image is
        // exactly the concatenation of its `to_le_bytes` on little-endian targets.
        let table_bytes: &[u8] =
            unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };
        // Every variable-length part is length-framed, so the preimage parses one way.
        let mut h = primitives::hash::Hasher::new();
        h.update(b"leanvm-rv64im-6");
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
        Ok(Self {
            digest: h.finalize(),
            rv,
            filler,
        })
    }
}

/// The whole proof is the transcript: a scalar stream plus the PCS hint
/// channels (see [`fiat_shamir::transcript::Proof`]).
pub use fiat_shamir::transcript::Proof;

/// Why a proof does not verify, by the stage that refuses it.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CpuError {
    /// An announced size is not a canonical integer.
    #[error("an announced size is not a canonical integer")]
    NonCanonicalSize,
    /// The sparse RAM boundary's announced height or last address does not fit the declared RAM.
    #[error("the sparse RAM boundary announces height {height} and last address {end:#x}, outside the declared RAM")]
    SparseBoundary { height: usize, end: u64 },
    /// A table's announced height is outside what the arithmetization expresses.
    #[error("the {table} table announces 2^{log_rows} rows, outside 2^{min}..=2^{max}")]
    TableHeight {
        table: &'static str,
        log_rows: usize,
        min: usize,
        max: usize,
    },
    /// The announced rate is one the commitment does not support.
    #[error("the announced log_inv_rate {log_inv_rate} is not in {min}..={max}", min = pcs::Rate::MIN.log_inv_rate(), max = pcs::Rate::MAX.log_inv_rate())]
    Rate { log_inv_rate: usize },
    /// The announced final clock is not a live clock: bit 40 alone above the cycle, and slot zero.
    #[error("the announced final clock is not a live clock")]
    FinalClock,
    /// The announced heights stack to a witness the commitment does not take.
    #[error("the witness has 2^{mu} words, outside 2^{min}..=2^{max}", min = pcs::MIN_MU, max = pcs::MAX_MU)]
    WitnessSize { mu: usize },
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] fiat_shamir::transcript::Error),
    /// The memory and lookup bus does not balance.
    #[error("the bus: {0}")]
    Bus(leaf::Error),
    /// The table constraints do not hold.
    #[error("the table constraints: {0}")]
    Constraint(constraints::Error),
    /// One of a table's circuit sub-proofs is rejected.
    #[error("the {table} table's {part:?} circuit: {error}")]
    Flock {
        table: &'static str,
        part: tables::Part,
        error: flock::verifier::VerifyError,
    },
    /// The commitment opening is rejected.
    #[error("the opening: {0}")]
    Open(::pcs::whir::VerifyError),
}

/// Why a run has no proof.
///
/// Every variant is a limit of the prover or a mistake of its caller, except a trap, which is the run's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ProveError {
    /// The run trapped.
    #[error(transparent)]
    Trap(#[from] rv::Trap),
    /// The run is longer than one proof holds, in cycles or in committed words.
    #[error("the run is longer than one proof holds (continuations are not implemented)")]
    TooLong,
    /// More advice words than the program's region holds.
    #[error("the advice has {got} words, and the program's region holds {max}")]
    AdviceTooLong { max: usize, got: usize },
}

/// One table's summand in the table sumcheck (§constraints): its two bus forms.
///
/// The forms are weighted by powers shared across tables, and carry every column of the table.
struct TableSummand {
    bus: leaf::BusForm,
}

/// A producer's summand (§sec:lookup): its bit `i`'s block owes the push side
/// `Σ_x eq(ζ, x)·(1 + b_i(x)·P'_i(x))` at the block's selector, and the producer has no
/// identity of its own. Its columns are its bits `b_i`, which are sent, then its public
/// `P'_i`, which the verifier computes.
struct ProducerSummand {
    /// Per bit, its block's selector, the push side's form power folded in.
    coefficients: Vec<F192>,
    producer: Producer,
    /// The fingerprint `(eq(α⃗, ·), β)` the public columns are made of.
    weights: Vec<F192>,
    beta: F192,
}

/// One air of the table sumcheck: a table's, or a lookup array's producer's.
enum Summand {
    Table(TableSummand),
    Producer(ProducerSummand),
}

impl constraints::Summand for Summand {
    #[inline(always)]
    fn eval<T: ColVal>(&self, cols: &[T], quadratic: bool) -> F192 {
        match self {
            Self::Table(s) => T::reduce(s.bus.eval_unreduced(cols, quadratic)),
            // `Σ_i c_i·(1 + b_i·P'_i)`, whose quadratic part is the products.
            Self::Producer(s) => {
                let n = s.coefficients.len();
                let products = (0..n).fold(T::lift(F192::ZERO), |acc, i| {
                    acc ^ (cols[i] * cols[n + i]).mul_e_unreduced(s.coefficients[i])
                });
                let constant = if quadratic {
                    F192::ZERO
                } else {
                    s.coefficients.iter().fold(F192::ZERO, |a, &b| a + b)
                };
                T::reduce(products) + constant
            }
        }
    }

    fn public(&self, chi: &[F192]) -> Vec<F192> {
        match self {
            Self::Table(_) => Vec::new(),
            Self::Producer(s) => leaf::producer_public_evals(&s.producer, &s.weights, s.beta, chi),
        }
    }
}

/// The producers as the table sumcheck takes them: their weights on each bit's block,
/// and the fingerprint (`eq(α⃗, ·)`, `β`) their public columns use.
#[derive(Clone, Copy)]
struct ProducerShares<'a> {
    coefficients: &'a [Vec<F192>],
    weights: &'a [F192],
    beta: F192,
}

/// The inputs to the table sumcheck, one per table in schema order, then one per
/// producer. Prover and verifier both call this, so their column order and summands
/// agree by construction.
fn airs(
    l: &Layout,
    forms: &[Vec<leaf::BusForm>; 2],
    producers: ProducerShares<'_>,
    xi: F192,
) -> Vec<constraints::Air<Summand>> {
    let form_pows = xi_form_pows(xi);
    let tables = tables::tables()
        .iter()
        .zip(&l.taus)
        .enumerate()
        .map(|(t, (table, &tau))| constraints::Air {
            tau,
            n_cols: table.n_committed_columns(),
            n_public: 0,
            summand: Summand::Table(TableSummand {
                // One form, not two: the batch adds the two sides' evaluations
                // anyway, and summing them here is a setup cost against a dot product
                // and a product list per row per node.
                bus: leaf::BusForm::sum((0..2).map(|s| forms[s][t].scaled(form_pows[s]))),
            }),
        });
    let producers = l
        .producers
        .iter()
        .zip(producers.coefficients)
        .map(|(p, coefficients)| constraints::Air {
            tau: p.kappa,
            n_cols: 2 * p.bits,
            n_public: p.bits,
            summand: Summand::Producer(ProducerSummand {
                coefficients: coefficients.iter().map(|&c| c * form_pows[0]).collect(),
                producer: p.clone(),
                weights: producers.weights.to_vec(),
                beta: producers.beta,
            }),
        });
    let sparse = l.sparse.map(|boundary| constraints::Air {
        tau: boundary.tau,
        n_cols: sparse::WIDTH,
        n_public: 0,
        summand: Summand::Table(TableSummand {
            bus: leaf::BusForm::sum((0..2).map(|s| forms[s][tables::N_TABLES].scaled(form_pows[s]))),
        }),
    });
    tables.chain(sparse).chain(producers).collect()
}

/// Each table's claimed sum: what its summand comes to is its two bus forms,
/// `η`-weighted. Prover-side only, to build the waiting
/// line each round; the verifier needs just their total, which it derives.
fn sigmas(bus: &[Vec<F192>; 2], form_pows: [F192; 2]) -> Vec<F192> {
    (0..bus[0].len())
        .map(|t| (0..2).fold(F192::ZERO, |acc, s| acc + form_pows[s] * bus[s][t]))
        .collect()
}

/// The two bus forms' weights `1, η`, shared by all tables rather than one pair per
/// table. That sharing is what keeps the batch tied to the bus: with a
/// common `η^s` per side, the batch's target is `Σ_s η^s·R_s` for the sides' table
/// shares `R_s`, which the verifier DERIVES from the leaf claims (a mismatch surfaces
/// as a constraint error). Were the powers per table, the target would not
/// factor through the `R_s` and nothing would pin the tables' share of the bus.
const fn xi_form_pows(xi: F192) -> [F192; 2] {
    [F192::ONE, xi]
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-table counts in [`tables::CLASSES`] order, and the
/// committed witness size, the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
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

/// Prove a run of the program on `advice`, the advice region's first words, which the
/// statement says nothing about: execute it (witness generation), then emit everything
/// the verifier needs through the returned [`Proof`] (scalar stream + PCS commitment /
/// opening hints). Returns the proof, the run's public output (`a0..a3` at the exit)
/// and its [`Stats`].
/// `rate` selects the PCS rate and is announced in the Fiat-Shamir transcript
/// before the commitment.
///
/// # Errors
///
/// The run's trap, a run too long for one proof, or more advice than the program's
/// region holds.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate = rate.log_inv_rate()))]
pub fn prove(program: &Program, advice: &[u64], rate: pcs::Rate) -> Result<(Proof, [u64; 4], Stats), ProveError> {
    // One proof is one arena phase: every transient buffer below is bump-allocated
    // and reclaimed wholesale here, rather than faulted in and unmapped again per
    // proof. Bound first so it outlives them; inert unless `init_prover` opted in.
    // The returned `Proof` is system-allocated (`ps.into_proof()` builds `Vec`s),
    // so it survives the next phase.
    let _phase = zk_alloc::enter_phase();
    let exec = crate::stage!("Execute program", || program.execute(advice))?;
    if program.run_layout(&exec).shape.mu > pcs::MAX_MU {
        return Err(ProveError::TooLong);
    }
    let (proof, stats) = prove_execution(program, &exec, rate);
    Ok((proof, exec.output, stats))
}

/// The statistics a proof of this run would report, without proving it: one execution.
///
/// The rows per table fix the layout, and the layout the committed size.
///
/// So the cost of a run, in cycles and in committed words, is known in the time of a run.
///
/// # Errors
///
/// What would refuse the proof itself, the rate aside.
pub fn measure(program: &Program, advice: &[u64]) -> Result<Stats, ProveError> {
    let exec = program.execute(advice)?;
    let counts = exec.trace.row_counts();
    let l = program.run_layout(&exec);
    let committed = committed_size(&l.placements);
    if l.shape.mu > pcs::MAX_MU {
        return Err(ProveError::TooLong);
    }
    Ok(Stats {
        cycles: exec.cycles,
        counts,
        base_counts: exec.base_counts,
        committed,
    })
}

/// [`prove`] from a finished run. Split out so a test can hand it a run no honest
/// machine produced.
fn prove_execution(program: &Program, exec: &Execution, rate: pcs::Rate) -> (Proof, Stats) {
    let w = crate::stage!("Build witness", || program.build(exec));
    let stats = Stats {
        cycles: exec.cycles,
        counts: w.layout.taus.map(|t| 1usize << t),
        base_counts: exec.base_counts,
        committed: w.committed_size(),
    };
    (prove_witness(program, w, &exec.output, rate), stats)
}

/// [`prove_execution`] from a built witness, which a test may have forged.
fn prove_witness(program: &Program, w: Witness, output: &[u64; 4], rate: pcs::Rate) -> Proof {
    let log_inv_rate = rate.log_inv_rate().into();
    // The public statement (program digest + output) seeds the transcript, so
    // every challenge depends on the exact program and what the run claims to return.
    let mut ps = ProverState::new(fs_seed(program), output.map(F64));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.layout.taus, log_inv_rate, w.ts_final, w.layout.sparse);
    let committed = crate::stage!("Commit", || {
        pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate)
    });

    // Single PCS: every class's packed flock witness is a column of `w.q`, so flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE WHIR
    // over this commitment (below). A circuit's words bind through the register and
    // bytecode buses: their virtual columns route to that witness, so no separate pin
    // claims are needed. Mirrored in `verify`.
    let spans = &w.layout.spans;
    // The columns are windows into `w.q`, so both stages read them in place: the
    // table sumcheck lifts each K-column into a fresh `E` copy on the round it
    // joins and never writes the K-columns back.
    let (bus_claims, table_claims) = {
        let l = &w.layout;
        let cols = w.columns();
        let mut bus = crate::stage!("Prove bus", || {
            leaf::prove_balance(&l.push, &l.pull, &l.producers, &cols, spans, &mut ps)
        });
        let table_claims = crate::stage!("Prove constraints", || {
            // One sumcheck for all the tables and producers (§constraints).
            let producers = std::mem::take(&mut bus.producers);
            let coefficients: Vec<Vec<F192>> = producers.iter().map(|p| p.coefficients.clone()).collect();
            // The eq point is the bus GKR's ζ, not a fresh one: that is what lets the
            // batch settle the bus forms alongside the constraints.
            let xi = ps.sample();
            let form_pows = xi_form_pows(xi);
            let mut sigma = sigmas(&bus.sigmas, form_pows);
            sigma.extend(producers.iter().map(|p| form_pows[0] * p.sigma));
            let table_cols = spans
                .iter()
                .map(|&(base, n)| constraints::Columns::K((0..n).map(|c| cols[base + c]).collect()))
                .chain(producers.into_iter().map(|p| constraints::Columns::E(p.columns)))
                .collect();
            let shares = ProducerShares {
                coefficients: &coefficients,
                weights: &bus.weights,
                beta: bus.beta,
            };
            constraints::prove(
                &airs(l, &bus.forms, shares, xi),
                table_cols,
                &bus.point,
                &sigma,
                &mut ps,
            )
        });
        (bus.claims, table_claims)
    };
    let l = &w.layout;

    let slots = finish_claims(l, bus_claims, &table_claims, output);

    // Run each circuit's flock reduction (zerocheck + lincheck), every class circuit
    // then every clock circuit, over the native layouts retained from the witness
    // build; it returns the validity claim on the circuit's committed packed witness,
    // discharged by the PCS below in the SAME WHIR as every leanVM point claim,
    // through a ring-switched region of its own. The producer's bits join them, its
    // multiplicity column a ring-switched region too.
    let reductions = w.reductions;
    let mut rings: Vec<_> = crate::stage!("Flock reductions", || {
        reductions
            .iter()
            .enumerate()
            .map(|(f, prepared)| {
                let window = w.layout.witness_window(f);
                let reduced = prepared.prove(&mut ps);
                flock::reduction::ring_switch_open(window.n_vars, window.offset, &reduced)
            })
            .collect()
    });
    drop(reductions);
    if let Some(prepared) = w.sparse_reduction {
        let window = l.placements[schema().n].window().expect("sparse witness is committed");
        let reduced = crate::stage!("RAM boundary reduction", || prepared.prove(&mut ps));
        rings.push(flock::reduction::ring_switch_open(
            window.n_vars,
            window.offset,
            &reduced,
        ));
    }
    for (p, claims) in l.producers.iter().zip(&table_claims[l.spans.len()..]) {
        let window = l.multiplicity_window(p);
        rings.push(::pcs::stack_open::RingSwitchOpen {
            offset: window.offset,
            qflock_vars: window.n_vars,
            claims: vec![::pcs::stack_open::RingSwitchClaim {
                suffix_point: claims.chi.clone(),
                s_hat_v: Some(multiplicity_slices(claims).to_vec()),
            }],
        });
    }
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &rings) });
    ps.into_proof()
}

/// A producer's claims as the 64 bit slices of its multiplicity column at its point:
/// the bits the bus reads, then zeros, every multiplicity being below `2^bits`.
fn multiplicity_slices(claims: &constraints::Claims) -> [F192; ::pcs::pack::PACKING_WIDTH] {
    let mut slices = [F192::ZERO; ::pcs::pack::PACKING_WIDTH];
    slices[..claims.evals.len()].copy_from_slice(&claims.evals);
    slices
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
    claims.reserve(schema().n - N_SHARED);
    for (&(base, _), table) in l.spans.iter().zip(table_claims) {
        claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
            col: base + c,
            point: table.chi.clone(),
            value,
        }));
    }
    // The exit (§sec:e2e-pi): the run halted on `exit`, returning `output`.
    claims.push(final_register_claim(rv::Reg::SYSCALL, rv::Syscall::Exit.number()));
    for (reg, &value) in rv::Reg::OUTPUTS.into_iter().zip(output) {
        claims.push(final_register_claim(reg, value));
    }
    slot_claims(l, claims)
}

/// What register `reg` holds when the run ends: the committed final registers at the
/// Boolean point naming `reg`. Both parties know the value, so the claim is computed
/// rather than transmitted, and the opening discharges it like any other.
fn final_register_claim(reg: rv::Reg, value: u64) -> ColumnClaim {
    ColumnClaim {
        col: Shared::RegFin.col(),
        point: (0..rv::RegisterFile::LOG_CELLS)
            .map(|bit| {
                if (reg.index() >> bit) & 1 == 1 {
                    F192::ONE
                } else {
                    F192::ZERO
                }
            })
            .collect(),
        value: F192::from(F64(value)),
    }
}

/// Verify a proof against the public statement, that the program exits returning
/// `output`: replay the transcript, reconstruct the public layout from the announced
/// sizes, read every scalar the prover wrote and pull the PCS hints, then assert the
/// stream was fully consumed. Takes only public inputs, never the prover's witness.
pub fn verify(program: &Program, output: &[u64; 4], proof: &Proof) -> Result<(), CpuError> {
    verify_to_raw(program, output, proof).map(|_| ())
}

/// [`verify`], returning the proof it accepted with every query's Merkle path
/// written out, the form `python-verifier` reads.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify_to_raw(
    program: &Program,
    output: &[u64; 4],
    proof: &Proof,
) -> Result<fiat_shamir::transcript::RawProof, CpuError> {
    let mut vs = VerifierState::new(fs_seed(program), proof, output.map(F64));
    let (l, log_inv_rate) = read_public(&mut vs, program)?;
    let root = pcs::read_commitment(&mut vs)?;

    let bus = leaf::verify_balance(&l.push, &l.pull, &l.producers, &l.spans, &mut vs).map_err(CpuError::Bus)?;

    let zc_xi = vs.sample();
    let form_pows = xi_form_pows(zc_xi);
    // THE tie between the batch and the bus, and the reason the batch's target is
    // never transmitted. Each side's leaf claim less what its framework blocks
    // account for is the tables' and producers' share `R_s`, which the verifier just
    // derived; the batch must sum to `Σ_s η^{base+s}·R_s`. Since `η` is sampled after
    // the `R_s` are fixed, hitting that one number forces `Σ_t σ_{s,t} = R_s` on both
    // sides. A transmitted target would be a free value in its own check, and the
    // tables' bus blocks would be settled by nothing at all.
    let target = (0..2).fold(F192::ZERO, |a, s| a + form_pows[s] * bus.totals[s]);
    let shares = ProducerShares {
        coefficients: &bus.producers,
        weights: &bus.weights,
        beta: bus.beta,
    };
    let table_claims = constraints::verify(&airs(&l, &bus.forms, shares, zc_xi), &bus.point, target, &mut vs)
        .map_err(CpuError::Constraint)?;

    let slots = finish_claims(&l, bus.claims, &table_claims, output);

    // Replay each circuit's flock reduction straight off the shared stream (each scalar
    // bound as it is read) to recover its validity claim on the circuit's packed
    // witness, then verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`).
    let mut replays = Vec::with_capacity(crate::class_flock::N_FLOCKS);
    for f in 0..crate::class_flock::N_FLOCKS {
        let (t, part) = crate::class_flock::flock(f);
        let replay = crate::class_flock::verify_reduction(f, l.taus[t], &mut vs).map_err(|error| CpuError::Flock {
            table: tables::CLASSES[t].name,
            part,
            error,
        })?;
        replays.push(replay);
    }
    let sparse_replay = l
        .sparse
        .map(|boundary| sparse::circuit(&program.rv).block().verify(boundary.tau, &mut vs))
        .transpose()
        .map_err(|error| CpuError::Flock {
            table: "RAM boundary",
            part: tables::Part::Class,
            error,
        })?;
    let slices: Vec<[F192; ::pcs::pack::PACKING_WIDTH]> =
        table_claims[l.spans.len()..].iter().map(multiplicity_slices).collect();
    let rings: Vec<_> = replays
        .iter()
        .enumerate()
        .map(|(f, replay)| {
            let window = l.witness_window(f);
            flock::reduction::ring_switch_verify(window.n_vars, window.offset, &replay.claim)
        })
        .chain(sparse_replay.iter().map(|replay| {
            let window = l.placements[schema().n].window().expect("sparse witness is committed");
            flock::reduction::ring_switch_verify(window.n_vars, window.offset, &replay.claim)
        }))
        .chain(
            l.producers
                .iter()
                .zip(&table_claims[l.spans.len()..])
                .zip(&slices)
                .map(|((p, claims), slices)| {
                    let window = l.multiplicity_window(p);
                    ::pcs::stack_open::RingSwitchVerify {
                        offset: window.offset,
                        qflock_vars: window.n_vars,
                        claims: vec![::pcs::stack_open::RingSwitchVerifyClaim {
                            suffix_point: &claims.chi,
                            s_hat_v: slices,
                        }],
                    }
                }),
        )
        .collect();
    pcs::verify(&mut vs, &slots, &rings, l.shape, log_inv_rate, &root).map_err(CpuError::Open)?;
    vs.finish()?;
    Ok(vs.into_raw_proof())
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on a committed column lives in
/// its window, with the claim's point as the low point.
///
/// A circuit word's column is a port: it has no window of its own. A claim
/// `word_col(r) = v` (at the table's row point `r`) is the equal slot evaluation of
/// the class's packed witness, at the point freezing the low coords to the port's bits
/// and the high coords to `r`. Folded sparsely (the table's height, not the dense
/// witness block), it joins the one opening like every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| match l.placements[c.col] {
            witness::Placement::Committed(window) => pcs::SlotClaim::Point {
                offset: window.offset,
                low_point: c.point,
                value: c.value,
            },
            witness::Placement::Port {
                offset,
                port,
                stride_log,
            } => pcs::SlotClaim::Strided {
                offset,
                slot: port,
                stride_log,
                point: c.point,
                value: c.value,
            },
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::*;

    #[test]
    fn instruction_construction_rejects_entries_in_the_padding() {
        let text = [0x0000_0073];
        for entry in [0, rv::TEXT_BASE + 2, rv::TEXT_BASE + 4, rv::TEXT_BASE + 8, u64::MAX] {
            assert!(matches!(
                Program::new(&text, entry, vec![], 0, 0),
                Err(rv::ProgramError::EntryPoint)
            ));
        }
        assert!(matches!(
            Program::new(&[], rv::TEXT_BASE, vec![], 0, 0),
            Err(rv::ProgramError::EntryPoint)
        ));
        assert!(matches!(
            Program::new(&text, rv::TEXT_BASE, vec![0, 0], 0, 0),
            Err(rv::ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, rv::TEXT_BASE, vec![], usize::MAX, 0),
            Err(rv::ProgramError::RamSize)
        ));
        assert!(matches!(
            Program::new(&text, rv::TEXT_BASE, vec![], 0, usize::MAX),
            Err(rv::ProgramError::AdviceSize)
        ));
    }

    #[test]
    fn illegal_instruction_encodings_have_normalized_identity() {
        let program = Program::new(&[0], rv::TEXT_BASE, vec![], 0, 0).unwrap();
        let same = Program::new(&[u32::MAX], rv::TEXT_BASE, vec![], 0, 0).unwrap();
        assert_eq!(program.digest(), same.digest());
        assert_eq!(
            rv::Machine::new(program.rv(), &[]).run_for(1),
            Err(rv::Trap::Illegal { pc: rv::TEXT_BASE })
        );
    }

    #[test]
    fn digest_binds_every_public_program_component() {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![1], 2, 0).expect("valid instruction program");
        assert_eq!(program.digest(), program.clone().digest());

        let mut changed_text = text.clone();
        changed_text[0] = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 6).finish()[0];
        let changed = [
            Program::new(&changed_text, rv::TEXT_BASE, vec![1], 2, 0).expect("valid instruction program"),
            Program::new(&text, rv::TEXT_BASE + 4, vec![1], 2, 0).expect("valid instruction program"),
            Program::new(&text, rv::TEXT_BASE, vec![2], 2, 0).expect("valid instruction program"),
            Program::new(&text, rv::TEXT_BASE, vec![1, 0], 2, 0).expect("valid instruction program"),
            Program::new(&text, rv::TEXT_BASE, vec![1], 3, 0).expect("valid instruction program"),
            Program::new(&text, rv::TEXT_BASE, vec![1], 2, 1).expect("valid instruction program"),
        ];
        for changed in changed {
            assert_ne!(program.digest(), changed.digest());
        }
    }

    /// The leaves a witness's bus leaves unmatched, as `(side, block, row)`.
    fn unmatched(w: &Witness) -> Vec<(&'static str, usize, usize)> {
        leaf::unmatched_leaves(&w.layout.push, &w.layout.pull, &w.layout.producers, &w.columns())
    }

    /// A committed column of a built witness, to forge it.
    fn column_mut(w: &mut Witness, col: usize) -> &mut [F64] {
        let window = w.layout.placements[col].window().expect("a forged column is committed");
        &mut w.q[window.offset..window.offset + (1 << window.n_vars)]
    }

    /// The prover refuses a witness whose bus does not balance: its two products differ.
    fn assert_unbalanced(program: &Program, w: Witness, output: &[u64; 4]) {
        let refused = std::panic::catch_unwind(|| prove_witness(program, w, output, pcs::Rate::MIN))
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
        let lone = program
            .filler
            .iter()
            .find(|b| b.size == 0)
            .expect("ALU has a lone jump")
            .index;
        let at = exec.trace.rows[0]
            .iter()
            .position(|r| r.index as usize == lone)
            .expect("the fill traverses the lone jump");
        exec.trace.rows[0][at] = row;
    }

    /// The padding row a jump to itself makes, `jal rd, 0` at entry `index`, at clock zero.
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
        }
    }

    /// The tuples a run leaves unmatched, as `(side, block, row)`.
    fn unmatched_run(program: &Program, exec: &Execution) -> Vec<(&'static str, usize, usize)> {
        unmatched(&program.build(exec))
    }

    /// An honest run's bus balances tuple by tuple, which says more than the proof
    /// failing would: the blocks left unmatched are named.
    #[test]
    fn an_honest_run_balances() {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let w = program.build(&program.execute(&[]).unwrap());
        let unmatched = unmatched(&w);
        assert!(
            unmatched.is_empty(),
            "unmatched (side, block, row): {:?}",
            &unmatched[..unmatched.len().min(12)]
        );
    }

    #[test]
    fn only_ecall_can_terminate_the_state_channel() {
        let prototype = Asm::new()
            .li(Reg::T0, rv::TEXT_BASE)
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .finish();
        let halt = Program::new(&prototype, rv::TEXT_BASE, vec![], 2, 0)
            .expect("valid exit program")
            .rv
            .halt_pc();
        let original = Asm::new()
            .li(Reg::T0, halt)
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .finish();
        let honest_program = Program::new(&original, rv::TEXT_BASE, vec![], 2, 0).expect("valid exit program");
        assert_eq!(honest_program.rv.halt_pc(), halt);
        let exit_index = original.len() - 1;
        let pc = honest_program.rv.pc_of(exit_index);
        for instruction in [
            Instruction::j(Reg::ZERO, (halt - pc) as i32),
            Instruction::i(Opcode::Jalr, 0, Reg::ZERO, Reg::T0, 0),
        ] {
            let mut text = original.clone();
            text[exit_index] = instruction.bits();
            let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid jump program");
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
            let witness = program.build(&execution);
            let unmatched = unmatched(&witness);
            // The final state on the pull side, and the ALU's state push, the push side's
            // first block past its four framework blocks.
            assert_eq!(unmatched.len(), 2, "{unmatched:?}");
            assert!(unmatched.iter().all(|(_, block, _)| *block == 0 || *block == 4));
            assert_unbalanced(&program, witness, &execution.output);
        }
    }

    /// A load cannot return what its cell does not hold. The forged run is consistent
    /// everywhere else (the circuit's instance, the register written, the output), so
    /// what is left unmatched is RAM's: the load pulls a tuple no store pushed.
    #[test]
    fn a_forged_load_unbalances_the_bus() {
        let text = Asm::new()
            .li(Reg::T0, rv::RAM_BASE + 32)
            .i(Addi, Reg::T1, Reg::ZERO, 5)
            .store(Sd, Reg::T1, 0, Reg::T0)
            .load(Ld, Reg::A0, 0, Reg::T0)
            .exit()
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 3, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        assert_eq!(forged.output, [5, 0, 0, 0]);
        let load = tables::table_of(rv::Class::Load).unwrap();
        let row = forged.trace.rows[load].iter_mut().find(|r| r.ts != 0).unwrap();
        (row.ram.old, row.ram.new, row.out) = (7, 7, 7);
        forged.trace.reg_fin[Reg::A0.index()] = F64(7);
        forged.trace.ram_fin[4] = F64(7);
        let w = program.build(&forged);
        let unmatched = unmatched(&w);
        // The load's pull and the store's push, which it should have met.
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
    }

    #[test]
    fn a_forged_store_unbalances_the_bus() {
        // Invariant: a store cannot write a value its `rs2` does not hold.
        //
        // Fixture state: `t1 = 5` is stored at `RAM_BASE + 32`, then loaded into `a0`.
        // Mutation: the store writes 7, and the circuit's instance, the cell, the load and the output follow it.
        // So only the store's read of `t1` is left to refuse it.
        let text = Asm::new()
            .li(Reg::T0, rv::RAM_BASE + 32)
            .i(Addi, Reg::T1, Reg::ZERO, 5)
            .store(Sd, Reg::T1, 0, Reg::T0)
            .load(Ld, Reg::A0, 0, Reg::T0)
            .exit()
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 3, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let tables = [rv::Class::Store, rv::Class::Load].map(|c| tables::table_of(c).unwrap());
        let [store, load] = forged.trace.rows.get_disjoint_mut(tables).unwrap();
        fn real(rows: &mut [Row]) -> &mut Row {
            rows.iter_mut().find(|r| r.ts != 0).unwrap()
        }
        let (store, load) = (real(store), real(load));
        (store.v2, store.ram.new) = (7, 7);
        (load.ram.old, load.ram.new, load.out) = (7, 7, 7);
        forged.trace.reg_fin[Reg::A0.index()] = F64(7);
        forged.trace.ram_fin[4] = F64(7);
        let w = program.build(&forged);
        let unmatched = unmatched(&w);
        // The read, pulled and pushed back as 7, meets neither `t1`'s write nor its final value.
        // That leaves two tuples on each side.
        assert_eq!(unmatched.len(), 4, "{unmatched:?}");
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
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let honest = program.execute(&[]).unwrap();
        assert_eq!(honest.output, [12, 0, 0, 0]);
        let (proof, _) = prove_execution(&program, &honest, pcs::Rate::MIN);
        verify(&program, &honest.output, &proof).expect("the honest run verifies");

        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[0][3];
        // The read happens at cycle 4; the first write happened at cycle 1, the second at 2, each in slot 3.
        let write = |cycle: u64| tables::SEED_CLOCK | (cycle * tables::CYCLE) | 3;
        assert_eq!((row.v1, row.prev[0]), (9, write(2)));
        (row.v1, row.out, row.prev[0]) = (5, 8, write(1));
        forged.output[0] = 8;
        forged.trace.reg_fin[Reg::A0.index()] = F64(8);
        // The multiplicities follow the forged gap, so no producer is left unmatched.
        let w = program.build(&forged);
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
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        let alu = tables::table_of(rv::Class::Alu).unwrap();
        let row = exec.trace.rows[alu].iter().position(|r| r.index == 0).unwrap();
        let mut w = program.build(&exec);
        let offset = schema().spans[alu].0 + tables::branch_offset_column(alu);
        column_mut(&mut w, offset)[row] = F64(8);
        column_mut(&mut w, Shared::BytecodeMult.col())[0].0 -= 1;

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
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let exec = program.execute(&[]).unwrap();
        for (p, col) in LOOKUPS
            .map(|lookup| lookup.multiplicity().col())
            .into_iter()
            .enumerate()
        {
            for flip in [1u64, 2, 4] {
                let mut w = program.build(&exec);
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
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let row = &mut forged.trace.rows[0][1];
        (row.v1, row.out, row.prev[0]) = (9, 9, row.ts);
        forged.output[0] = 9;
        forged.trace.reg_fin[Reg::A0.index()] = F64(9);
        forged.trace.reg_ts[Reg::T0.index()] = F64(tables::CLOCK_START | 3);
        // The read's row pushes a failed clock, which the next row's pull does not meet.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(unmatched.iter().all(|&(_, block, _)| block == FRAMEWORK.len()));
    }

    #[test]
    fn a_padding_row_cannot_pull_a_seed() {
        // Invariant: a row at clock zero touches no tuple of the run, the seeds included.
        //
        // Fixture state: the run sets `a0 = 42` and exits, never touching `a1`.
        // Past the exit sits `jal a1, 0`, a jump to itself, which the run never reaches.
        // Mutation: a padding instance of it takes the place of the fill's lone jump, its write pulling `a1`'s seed.
        // `a1`'s final value is what it pushes, so the output claims `a1 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::A0, Reg::ZERO, 42)
            .exit()
            .label("spin")
            .jal(Reg::A1, "spin")
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let mut row = padding_jump(&program, spin);
        (row.prev[2], row.vd_old) = (tables::SEED_CLOCK, 0);
        replace_lone_jump(&program, &mut forged, row);
        let link = program.rv.pc_of(spin) + 4;
        forged.output[1] = link;
        forged.trace.reg_fin[Reg::A1.index()] = F64(link);
        forged.trace.reg_ts[Reg::A1.index()] = F64(3);
        // The row's failed clock leaves its own state tuples unmatched, and nothing else.
        let unmatched = unmatched_run(&program, &forged);
        assert_eq!(unmatched.len(), 2, "{unmatched:?}");
        assert!(unmatched.iter().all(|&(_, block, _)| block == FRAMEWORK.len()));
    }

    #[test]
    fn a_live_row_cannot_pull_a_padding_tuple() {
        // Invariant: a row of the run pulls only timestamps of the run, which have the live bit.
        //
        // Fixture state: `t0 = 5`, then `a0 = t0 + x0`; past the exit sits `jal t0, 0`, a jump to itself.
        // Mutation: a padding instance of the jump pulls `t0`'s write and pushes `(t0, 3, pc + 4)`, which the run's read pulls.
        // The read's `prev` is 3, live bit clear, and the output claims `a0 = pc + 4`.
        let text = Asm::new()
            .i(Addi, Reg::T0, Reg::ZERO, 5)
            .r(Add, Reg::A0, Reg::T0, Reg::ZERO)
            .i(Addi, Reg::T1, Reg::ZERO, 0)
            .exit()
            .label("spin")
            .jal(Reg::T0, "spin")
            .finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let spin = text.len() - 1;
        let link = program.rv.pc_of(spin) + 4;
        let read = &mut forged.trace.rows[0][1];
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
        assert!(unmatched.iter().all(|&(_, block, _)| block == FRAMEWORK.len()));
    }

    #[test]
    fn the_final_clock_cannot_carry_a_failure() {
        // Invariant: the exit row's failed clock is refused, though it is the one the final state meets.
        //
        // Fixture state: `a0 = 42`, then the exit, which writes the sink at slot 3 of cycle 3.
        // Mutation: the exit's write pulls the tuple it pushes, the sink's seed meeting its final.
        // Its clock circuit flags the failure, and the announced final clock carries it, so the bus balances.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 42).exit().finish();
        let program = Program::new(&text, rv::TEXT_BASE, vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let exit = forged.trace.rows[0].iter_mut().find(|r| r.index == 2).unwrap();
        (exit.prev[2], exit.vd_old) = (exit.ts | 3, exit.out);
        let sink = rv::RegisterFile::SINK as usize;
        (forged.trace.reg_ts[sink], forged.trace.reg_fin[sink]) = (F64(tables::SEED_CLOCK), F64::ZERO);
        forged.trace.ts_final |= 1 << tables::FAIL_BIT;
        assert!(unmatched_run(&program, &forged).is_empty());
        let (proof, _) = prove_execution(&program, &forged, pcs::Rate::MIN);
        assert_eq!(verify(&program, &forged.output, &proof), Err(CpuError::FinalClock));
    }
}
