//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g. Machine-word arithmetic
//! is over `E = F192 = K[y]/(y³+y+1)` (XOR degree 1, MUL_NATIVE degree 2),
//! with each word carried by three committed `K = F64` limbs. `BLAKE2s`
//! adds the memory/state/bytecode plumbing for a 64→32-byte compression
//! whose relation is discharged by flock (see [`crate::hash_flock`]). All
//! Challenges and transcript scalars live in the same tower E.

use std::collections::HashMap;

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM,
    SEP_STATE,
};
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use crate::witness;
use primitives::field::{F64, F192, g_pow};

mod execute;
pub mod filler;
pub mod hints;
mod isa;
pub mod layout;
mod trace;
pub use execute::Execution;
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Brow, Drow, Jrow, Srow, Trace, Xrow};

/// Witness-gen `BLAKE2s` compression: the four message cells' eight
/// words are laid out little-endian into 64 bytes, combined with the supplied
/// chaining value and metadata, and the 32-byte result is split back into the
/// four output words `c`. Flock proves this same compression relation
/// ([`crate::hash_flock`]).
fn blake2s_compress(va: [F64; 4], vb: [F64; 4], vcv: [F64; 4], metadata: F192) -> [F64; 4] {
    crate::hash_flock::digest(&crate::hash_flock::compression(va, vb, vcv, metadata))
}

/// Data-memory size bounds (doc §Memory): memory is `2^h` cells with
/// `MIN_LOG_MEM ≤ h ≤ MAX_LOG_MEM`. The prover pads up to the minimum; the
/// verifier rejects any announced `h` outside the range. `MIN_LOG_MEM` is also
/// the static cap on range-check bounds (`compiler::Stmt::AssertLt`): a bound
/// `≤ 2^MIN_LOG_MEM` keeps the complement argument sound for every memory size
/// the prover may announce.
pub const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode). Together with `MAX_LOG_MEM` and the bytecode
/// cap these are the instance caps from “Counts must not wrap” in `doc/leanvm/body/06-memory-and-bytecode-lookups.tex`: at `ord(g) = 2^64−1`
/// the memory-soundness and count-non-wrap counting arguments are theorems only
/// for instances whose total read-flush count stays far below `2^64`, so the
/// verifier rejects any announcement exceeding them before running a reduction.
const MAX_LOG_ROWS: usize = 32;

/// Bytecode-length instance cap (see [`MAX_LOG_ROWS`]): programs are at most
/// `2^32` instructions.
const MAX_LOG_BYTECODE: usize = 32;

/// The Fiat-Shamir IV: ONE 32-byte digest, as two field words, committing to
/// everything fixed about the proving environment.
///
/// Two things go in. [`flock::hash::R1CS_DIGEST`] names the flock BLAKE2s
/// circuit, independent of the instance count: the full instance is
/// block-diagonal and the count is announced and absorbed with the other sizes,
/// so one constant covers every shape. And the bytecode enters through the hash
/// cached on `Program`, BLAKE2s over the stacked multilinear
/// ([`layout::bytecode_table`]) rather than over an assembler digest, so a
/// verifier holding only that polynomial reproduces the seed; that inner hash is
/// cached, so the table is walked once per program rather than once per proof.
///
/// The IV IS the transcript's starting chaining value ([`fiat_shamir::FiatShamirState::new`]),
/// so all challenges depend on the circuit version and the program before
/// anything else; a recursion guest carries the INNER program's IV in its public
/// input, pinning both with one word pair.
pub fn fs_seed(program: &Program) -> [F192; 2] {
    let mut h = primitives::hash::Hasher::new();
    h.update(b"leanvm");
    // Length-framed so the preimage parses one way: the domain and the bytecode
    // hash are fixed-width, so framing the digest between them is all it takes.
    h.update(&(flock::hash::R1CS_DIGEST.len() as u64).to_le_bytes());
    h.update(&flock::hash::R1CS_DIGEST);
    h.update(&program.bytecode_hash);
    let d = h.finalize();
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)]
}

/// The two 128-bit halves a digest travels in, as the four words the
/// Fiat-Shamir chain runs on. Only defined for a real digest, whose halves have
/// no third limb; [`read_public`] rejects a public input that has one, so a
/// third limb can never be silently dropped from what the transcript binds.
fn digest_words(halves: &[F192; 2]) -> [F64; 4] {
    [
        F64(halves[0].c0),
        F64(halves[0].c1),
        F64(halves[1].c0),
        F64(halves[1].c1),
    ]
}

/// Announce the prover's sizes (`log_mem`, every table's log height, the PCS rate)
/// by writing them onto the scalar stream, which binds them into the state and lets
/// the verifier reconstruct the layout. The public statement (program + input) is not
/// announced here; it seeds the transcript at construction (see [`fs_seed`]).
/// The boundary states are derived from the program, so they need no binding.
///
/// Log heights, not row counts: every table's rows are real rows, the fill blocks
/// having run each count up to a power of two (`filler`), so a height is all there is
/// to say. That also spares both sides a `log2_ceil`, which
/// in-circuit is a bit decomposition against a hinted exponent rather than a shift.
fn announce_public(ps: &mut ProverState, log_mem: usize, taus: [usize; tables::N_TABLES], log_inv_rate: usize) {
    ps.add_scalar(F192::new(log_mem as u64, 0, 0));
    for t in taus {
        ps.add_scalar(F192::new(t as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
}

/// Verifier side of [`announce_public`]: read the announced sizes and PCS
/// rate from the stream, validate them, and reconstruct the public [`Layout`]
/// from the program + sizes + public input. (The public input was already bound
/// by seeding the transcript.)
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F192; 2]) -> Result<(Layout, usize), CpuError> {
    let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
        let word = vs.next_scalar().map_err(CpuError::Transcript)?;
        if word.c1 != 0 || word.c2 != 0 {
            return Err(CpuError::PublicInput);
        }
        usize::try_from(word.c0).map_err(|_| CpuError::PublicInput)
    };

    // The transcript binds a public input as two 128-bit halves, so a third limb
    // would be dropped and two statements would share a transcript.
    if public_input.iter().any(|half| half.c2 != 0) {
        return Err(CpuError::PublicInput);
    }
    let log_mem = read_size(vs)?;
    let mut taus = [0usize; tables::N_TABLES];
    for t in &mut taus {
        *t = read_size(vs)?;
    }
    let log_inv_rate = read_size(vs)?;
    // The public instance caps ensure that, with `ord(g) = 2^64 − 1`, the
    // counting arguments (memory soundness, count non-wrap, exponent range checks)
    // are theorems only when the announced instance keeps the total read-flush
    // count provably below `2^64 − 1`, so reject any announcement exceeding the
    // caps BEFORE running any reduction. (A table's row count is the number of
    // times its opcode runs, unbounded by the bytecode size since a small loop
    // body runs many times, so it gets its own cap, not `bytecode_size`.)
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || bytecode_size > (1usize << MAX_LOG_BYTECODE)
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || taus.iter().any(|&t| t > MAX_LOG_ROWS)
        // flock sizes its argument to at least `n_blocks_log(1)` instances, and the
        // BLAKE2s table's value columns share that instance cube, so a height below the
        // floor describes a layout the arithmetization cannot express. The other two
        // verifiers reject it here too (`python-verifier`, `guests/lean_ethereum.py`).
        || taus[tables::BLAKE2S_TABLE] < crate::hash_flock::n_blocks_log(1)
        || ::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err()
    {
        return Err(CpuError::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, taus, *public_input);
    // The caps bound each announced log on its own; what the PCS is configured for
    // is the stacked size they imply, which they do not bound.
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&l.shape.mu) {
        return Err(CpuError::PublicInput);
    }
    Ok((l, log_inv_rate))
}

#[derive(Clone)]
pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    /// BLAKE2s over the stacked bytecode multilinear, computed once at assembly
    /// so proving and verifying the same program do not rehash it (that table is
    /// 16·2^kbc words, tens of megabytes at production sizes). Trusted to match
    /// `prog`: always set by [`Program::assemble`] from the bytecode, so a
    /// `Program` cannot carry a hash inconsistent with its own `prog`.
    pub(crate) bytecode_hash: [u8; 32],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame: the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (§ `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<hints::RHint>>,
    pub(crate) main_frame: u32,
    /// Named prover witness streams for the program's `hint_witness` calls
    /// ([`Program::set_witness`]): a stream is a sequence of *entries* (one
    /// slice of values per `hint_witness` call; the same symbol may be
    /// hinted many times); each call pops the next entry, whose length must
    /// match its destination. Prover-side only; verification ignores them.
    pub(crate) witness: HashMap<String, Vec<Vec<F192>>>,
    /// The fill blocks in the bytecode ([`filler`]): the cycles the interpreter
    /// traverses, after the program halts, to bring every table's row count to a power
    /// of two. Set by the compiler, prover-side only, and no program code reaches them,
    /// so a missing or wrong entry costs the prover a run that does not fill rather than
    /// anything a verifier would accept.
    pub filler: Vec<filler::Block>,
    /// Function pc-ranges `(name, entry, len)` from the compiler, for the
    /// `DBG_PROF=1` per-function cycle profile ([`Program::execute`]). Purely
    /// diagnostic; empty for hand-assembled programs.
    pub fn_ranges: Vec<(String, u32, u32)>,
    /// Source line of the statement that emitted each pc. Prover-side only, and
    /// outside `bytecode_hash`, so it costs nothing in the proof: a failed guest
    /// check reports a line rather than a pc to disassemble around. Empty for a
    /// hand-assembled program, and shorter than `prog`, which is padded.
    pub src_lines: Vec<u32>,
    /// The smallest stacked witness this program's proofs may commit to, as a
    /// log2. Zero (the default) asks for nothing.
    ///
    /// A consumer can need a proof to be no smaller than some size even when the
    /// run is: the recursion guest holds one WHIR opening arm per committed size
    /// it was compiled for, and has none below the first. A run that falls short
    /// buys the difference in fill rows ([`crate::cpu::filler`]) rather than in a
    /// padded commitment, which keeps the committed size a function of the
    /// announced table heights, so neither the verifier nor the guest needs a new
    /// parameter to certify. Prover-side only.
    pub min_log_committed: usize,
}

/// The bytecode digest reinterprets the stacked table as bytes, which is its
/// `to_le_bytes` image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// Assemble a [`Program`], computing its bytecode digest
    /// from `prog`. The single funnel for construction, so the digest is always
    /// consistent with the bytecode.
    pub fn assemble(prog: Vec<Op>, hints: HashMap<u32, Vec<hints::RHint>>, main_frame: u32) -> Self {
        let bytecode_hash = {
            let table = layout::bytecode_table(&prog);
            // SAFETY: F64 is #[repr(transparent)] over u64, so the slice's byte image is
            // exactly the concatenation of its `to_le_bytes` on little-endian targets.
            let bytes: &[u8] =
                unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };
            primitives::hash::Hasher::new().update(bytes).finalize()
        };
        Self {
            prog,
            bytecode_hash,
            hints,
            main_frame,
            witness: HashMap::new(),
            filler: Vec::new(),
            fn_ranges: Vec::new(),
            src_lines: Vec::new(),
            min_log_committed: 0,
        }
    }

    /// Where `pc` came from: `"verify_sub (line 2204)"` when the compiler left a
    /// line for it, the function name alone otherwise (a hand-assembled program,
    /// a fill block, or padding). This is what a run-time failure reports, so
    /// the reader gets a line instead of a pc to disassemble around.
    pub fn site_at(&self, pc: u32) -> String {
        match self.src_lines.get(pc as usize) {
            Some(&line) if line != 0 => format!("{} (line {line})", self.fn_at(pc)),
            _ => self.fn_at(pc).to_string(),
        }
    }

    /// The compiled function containing `pc`. [`Self::site_at`] wraps this with
    /// the source line when one is known.
    pub fn fn_at(&self, pc: u32) -> &str {
        self.fn_ranges
            .iter()
            .find(|(_, entry, len)| pc >= *entry && pc < *entry + *len)
            .map_or("<unknown fn>", |(name, _, _)| name.as_str())
    }

    /// Supply the entries of witness stream `name`: one slice of values per
    /// `hint_witness(dest, "name")` call, popped in order (the same symbol
    /// may be hinted many times). Prover-side data: entirely unconstrained,
    /// invisible to verification.
    pub fn set_witness(&mut self, name: impl Into<String>, entries: Vec<Vec<F192>>) {
        self.witness.insert(name.into(), entries);
    }

    /// Assemble a program directly from a fixed bytecode vector, starting at
    /// `(pc, fp) = (0, 0)` with no allocation hints. Suitable for straight-line
    /// programs that never change the frame pointer and touch only the first
    /// `main_frame` memory cells (so the prover needs no nondeterministic frame
    /// allocation). `prog.len()` must be a power of two with a never-executed
    /// sentinel in its last slot: the run halts on reaching `g^{len-1}` (§sec:state).
    #[cfg(test)]
    pub fn from_bytecode(prog: Vec<Op>, main_frame: u32) -> Self {
        Self::assemble(prog, HashMap::new(), main_frame)
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
    /// flock's BLAKE2s R1CS validity sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`CpuError::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Blake2s(flock::verifier::VerifyError),
}

/// Per side, which table (if any) owns each bus block, as `(table, column base)`.
type BlockOwners = [Vec<Option<(usize, usize)>>; 3];
/// Each table's `(column base, committed column count)` in the global schema.
type TableSpans = Vec<(usize, usize)>;

/// Blocks sourced from a table's height belong to it; the boundary, memory and
/// bytecode blocks belong to none and keep their own column claims at ζ.
fn block_owners(log_bytecode: usize, sides: [usize; 3]) -> BlockOwners {
    let sch = schema();
    let src = block_kappa_sources(log_bytecode);
    let mut it = src
        .into_iter()
        .map(|(source, _)| source.checked_sub(2).map(|t| (t, sch.base[t])));
    sides.map(|n| it.by_ref().take(n).collect())
}

/// The bus's public wiring: per side which table owns each block, and each table's
/// column span. Derived from the program and the announced layout alone, so prover
/// and verifier build it identically.
fn bus_wiring(program: &Program, l: &Layout) -> (BlockOwners, TableSpans) {
    let owners = block_owners(
        crate::log2_strict_usize(program.prog.len()),
        [l.push.len(), l.pull.len(), l.count.len()],
    );
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
fn airs(
    taus: &[usize; tables::N_TABLES],
    forms: &[Vec<leaf::BusForm>; 3],
    form_pows: [F192; 3],
) -> Vec<constraints::Air<'static>> {
    tables::tables()
        .iter()
        .zip(taus)
        .enumerate()
        .map(|(t, (&table, &tau))| {
            // One form, not three: the batch adds the three sides' evaluations
            // anyway, and summing them here is a setup cost against a dot product
            // and a product list per row per node.
            let bus = leaf::BusForm::sum((0..3).map(|s| forms[s][t].scaled(form_pows[s])));
            let bus_k = bus.clone();
            constraints::Air {
                tau,
                n_cols: table.n_committed_columns(),
                n_constraints: table.n_constraints(),
                eval: Box::new(move |p, vals| {
                    let air = <F192 as ColVal>::lift(table.eval_constraint(p, vals));
                    <F192 as ColVal>::reduce(air ^ bus.eval_unreduced(vals))
                }),
                // The same expression over K columns: the identity's K-only products
                // stay 64-bit and the bus form becomes a mixed dot product.
                eval_k: Box::new(move |p, vals| {
                    let air = <F64 as ColVal>::lift(table.eval_constraint_k(p, vals));
                    <F64 as ColVal>::reduce(air ^ bus_k.eval_unreduced(vals))
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

/// If `col` is a BLAKE2s **value** column (global index), its `q_flock` packed slot.
/// These columns are virtual (uncommitted): their memory-bus evaluation claims
/// are re-routed to `q_flock` slot evaluations, which is the whole binding: the
/// bus-tied value IS the proven `q_flock` word, no separate check needed.
fn blake2s_value_slot(col: usize) -> Option<usize> {
    let base = schema().base[tables::BLAKE2S_TABLE];
    tables::BLAKE2S_VALUE_COLS
        .iter()
        .position(|&c| base + c == col)
        .map(|i| crate::hash_flock::SLOTS[i])
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts
/// `[XOR, MUL, SET, DEREF, JUMP, BLAKE2s]`, and the
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
    /// Data memory is `2^log_mem` cells (the padded write-once image).
    pub log_mem: usize,
    /// Cells actually touched, before the pad to `2^log_mem`, i.e. the real memory
    /// footprint (`log2` is fractional).
    pub mem_used: usize,
}

impl Stats {
    /// Table names in `counts` order.
    pub const TABLES: [&'static str; tables::N_TABLES] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE2S"];

    /// One line of per-table instruction counts and shares, largest first, followed by memory and committed-witness sizes.
    ///
    /// The counts are `base_counts`, the work the program itself does, since the proven
    /// `counts` are all exact powers of two once the fill blocks have run (`filler`) and
    /// so say nothing about the workload.
    /// `log_mem` holds the padded memory size the commitment covers. Zero-count
    /// tables are omitted.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }
        let base_cycles: usize = self.base_counts.iter().sum();
        let mut shares: Vec<(&str, usize)> = Self::TABLES
            .iter()
            .zip(&self.base_counts)
            .filter(|&(_, &c)| c > 0)
            .map(|(&name, &c)| (name, c))
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
        parts.push(format!("MEMORY 2^{}", log2(self.mem_used)));
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`]. `log_inv_rate` selects the PCS rate and is announced in the
/// Fiat-Shamir transcript before the commitment.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(program: &Program, public_input: [F192; 2], log_inv_rate: usize) -> (Proof, Stats) {
    ::pcs::whir::validate_log_inv_rate(log_inv_rate).expect("valid log_inv_rate");
    // One proof is one arena phase: every transient buffer below is bump-allocated
    // and reclaimed wholesale here, rather than faulted in and unmapped again per
    // proof. Bound first so it outlives them; inert unless `init_prover` opted in.
    // The returned `Proof` is system-allocated (`ps.into_proof()` builds `Vec`s),
    // so it survives the next phase.
    let _phase = zk_alloc::enter_phase();
    let exec = crate::stage!("Execute program", || program.execute_to_floor(public_input));
    // A live value that came from outside the constraint system means the emitted
    // bytecode asserts less than its source asked for, so the proof would be about a
    // weaker statement than the program text. That is a compiler bug and never a
    // program one, so it is caught here, on the one path every proof takes, rather
    // than left to whichever test happens to look. A hard assert, not a
    // `debug_assert`: this is what makes the invariant hold in release, which is the
    // only profile the VM is ever run in.
    assert!(
        exec.unconstrained_reads.is_empty(),
        "the program read {} cell(s) nothing ever writes, first at {:?}: a constraint was \
         dropped in lowering (see `Execution::unconstrained_reads`)",
        exec.unconstrained_reads.len(),
        &exec.unconstrained_reads[..exec.unconstrained_reads.len().min(8)]
    );
    // Warm the shape-dependent BLAKE2s R1CS setup concurrently with the earlier proving stages. A no-BLAKE2s program still uses the padding shape.
    let n_blake2s_warm = exec.trace.blake2s.len().max(1);
    std::thread::spawn(move || crate::hash_flock::warm_setup(n_blake2s_warm));
    let cycles = exec.cycles;
    let w = crate::stage!("Build witness", || program.build(&exec));
    let counts = w.layout.taus.map(|t| 1usize << t);
    let committed_size = w.committed_size();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    debug_assert!(
        public_input.iter().all(|h| h.c2 == 0),
        "a public input is a 256-bit digest"
    );
    let mut ps = ProverState::new(digest_words(&fs_seed(program)), digest_words(&public_input));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.layout.taus, log_inv_rate);
    let committed = crate::stage!("Commit", || {
        pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate)
    });

    // BLAKE2s to flock (§hash_flock), single PCS: q_flock is ALWAYS a column in
    // `w.q` (≥1 instance, a program with no BLAKE2s carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE2s fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // WHIR over this commitment (below). Message, chaining-value, and output words
    // bind through the memory bus; counter and flags bind through bytecode. Their
    // virtual value columns route to q_flock, so no separate pin claims are needed.
    // Mirrored in `verify`.
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
            // One sumcheck for all six tables (§constraints).
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
                &airs(&l.taus, &bus.forms, form_pows),
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

    // The PI binding transmits the two LOW memory limbs' evaluations
    // (§sec:e2e-pi); the verifier checks them against the public-input line at
    // `r_pi`. The top limb of both public words is zero, so its evaluation is
    // zero at every `r_pi` and rides no scalar.
    let r_pi = ps.sample();
    let pi_limbs = [
        primitives::multilinear::interp_k(F64(l.pi[0].c0), F64(l.pi[1].c0), r_pi),
        primitives::multilinear::interp_k(F64(l.pi[0].c1), F64(l.pi[1].c1), r_pi),
        F192::ZERO,
    ];
    for v in &pi_limbs[..2] {
        ps.add_scalar(*v);
    }
    // Memory binds the message, chaining-value, and output words; bytecode binds
    // the counter and flags. All corresponding value columns are virtual and route
    // to q_flock through `slot_claims`.
    let slots = finish_claims(l, bus.claims, &table_claims, r_pi, pi_limbs);

    // Run flock's reduction (zerocheck + lincheck) over the prepared native
    // layouts retained from the fused q_flock build pass; it returns the
    // validity claim on the committed `q_flock`, discharged by the PCS below in
    // the SAME WHIR as every leanVM point claim (the point claims become the
    // opener's `point_claims`).
    let flock_reduction = w.flock_reduction;
    let reduced = crate::stage!("Flock reduction", || { flock_reduction.prove(&mut ps) });
    let n_blocks = flock_reduction.n_blocks();
    drop(flock_reduction);
    let offset = w.layout.placements[QFLOCK].offset;
    let ring = crate::hash_flock::ring_switch_open(n_blocks, offset, &reduced);
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &ring) });
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            base_counts: exec.base_counts,
            committed: committed_size,
            log_mem: w.log_mem,
            mem_used: exec.mem_used,
        },
    )
}

/// Everything the PCS has to open, in the ORDER that feeds the batch's weights:
/// the bus's framework claims, then the zerocheck's per-table column claims, then
/// the three public-input limb claims, each located in its committed slot. Both
/// sides assemble it here, so a claim can never shift by one element.
fn finish_claims(
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    table_claims: &[constraints::Claims],
    r_pi: F192,
    pi_limbs: [F192; 3],
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
    claims.extend(bind_pi_claim(r_pi, &l.placements, pi_limbs));
    slot_claims(l, claims)
}

/// The public-input binding (§sec:e2e-pi): the committed `MEM` at `(r, 0,…,0)` must
/// equal `interp(pi[0], pi[1], r)`, one transmitted evaluation per physical `K`
/// limb. The caller has already checked the three against the line; here they
/// simply become the three claims the opening discharges. `placements` comes from
/// the prover's or verifier's layout, so both sides build byte-identical claims.
fn bind_pi_claim(r: F192, placements: &[witness::Placement], limbs: [F192; 3]) -> [ColumnClaim; 3] {
    let mut point = vec![F192::ZERO; placements[MEM_LO].n_vars];
    point[0] = r;
    [MEM_LO, MEM_HI, MEM_TOP].map(|col| ColumnClaim {
        col,
        point: point.clone(),
        value: limbs[col - MEM_LO],
    })
}

/// Everything a recursion harness needs from an accepting verify run, named
/// and typed: the deferred bytecode claims, flock's
/// reduction claims, and the stacked-opening summary (ring-switch challenges +
/// WHIR fold/query data). The sub-proof scalars themselves live on
/// `proof.stream`, ending at `flock_stream_end`. Ordinary callers just
/// `?`-discard it.
pub struct VerifySummary {
    /// Transcript-bound inverse-rate logarithm used by this proof's PCS.
    pub log_inv_rate: usize,
    pub bytecode_claims: Vec<leaf::BytecodeClaim>,
    pub zc_claim: flock::zerocheck::ZerocheckClaim,
    pub lc_claim: flock::lincheck::LincheckClaim,
    /// Stream cursor just after flock's reduction, i.e. where the PCS opening's
    /// own scalars start. The recursion harness reads flock's lincheck tail
    /// from here rather than counting back from the end of the stream.
    pub flock_stream_end: usize,
    /// The proof this run just verified, in the unpruned form the recursion
    /// guest and the Python verifier consume.
    pub raw: fiat_shamir::transcript::RawProof,
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs, never the prover's witness.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(program: &Program, public_input: &[F192; 2], proof: &Proof) -> Result<VerifySummary, CpuError> {
    let mut vs = VerifierState::new(digest_words(&fs_seed(program)), proof, digest_words(public_input));
    let (l, log_inv_rate) = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(CpuError::Transcript)?;

    // BLAKE2s to flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE WHIR opening at the end. The padded
    // BLAKE2s table size is public and announced; its flock sub-proof rides the
    // shared stream and openings. Memory and bytecode bind every compression input
    // and output by routing their virtual value-column claims to q_flock.
    let n_blake2s = 1usize << l.taus[tables::BLAKE2S_TABLE];

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
    let table_claims = constraints::verify(
        &airs(&l.taus, &bus.forms, form_pows),
        zc_xi,
        &bus.point,
        target,
        &mut vs,
    )
    .map_err(CpuError::Constraint)?;

    let r_pi = vs.sample();
    let mut pi_limbs = [F192::ZERO; 3];
    for v in &mut pi_limbs[..2] {
        *v = vs.next_scalar().map_err(CpuError::Transcript)?;
    }
    // The two claimed evaluations must sit on the public-input line, the top
    // limb's being zero (§sec:e2e-pi).
    let want = primitives::multilinear::interp(l.pi[0], l.pi[1], r_pi);
    if pi_limbs[0] + F192::Y * pi_limbs[1] != want {
        return Err(CpuError::PublicInput);
    }
    let slots = finish_claims(&l, bus.claims, &table_claims, r_pi, pi_limbs);

    // Replay flock's reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its validity claim on q_flock, then
    // verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`). The padding convention always supplies at least one
    // instance, including programs that execute no BLAKE2s instruction.
    let n_blocks = n_blake2s.max(1);
    let offset = l.placements[QFLOCK].offset;
    let replay = crate::hash_flock::verify_reduction(n_blocks, &mut vs).map_err(CpuError::Blake2s)?;
    let flock_stream_end = vs.stream_offset();
    let ring = crate::hash_flock::ring_switch_verify(n_blocks, offset, &replay.claim);
    pcs::verify(&mut vs, &slots, &ring, l.shape, log_inv_rate, &root).map_err(CpuError::Open)?;
    vs.finish().map_err(CpuError::Transcript)?;
    Ok(VerifySummary {
        bytecode_claims: bus.bytecode_claims,
        zc_claim: replay.zc_claim,
        lc_claim: replay.lc_claim,
        log_inv_rate,
        flock_stream_end,
        raw: vs.into_raw_proof(),
    })
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE2s value columns are virtual: they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_flock` slot evaluation: an ordinary claim on the committed
/// `QFLOCK` column at the point freezing the low 8 coords to the slot's bits and
/// the high coords to `r`. No downstream special-casing: it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| {
            // A virtual BLAKE2s value column (always virtual): its bus claim at
            // instance point `c.point` is the q_flock slot value, a boolean-selector
            // (strided) claim on QFLOCK, folded sparsely (2^n_log, not the 2^(8+n_log)
            // dense QFLOCK block).
            if let Some(slot) = blake2s_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[QFLOCK].offset,
                    slot,
                    stride_log: crate::hash_flock::SLOT_STRIDE_LOG,
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

    /// A K-embedded immediate (both extension limbs zero).
    fn w(x: u64) -> F192 {
        F192::new(x, 0, 0)
    }

    /// Pack two 64-bit flock words into the canonical BLAKE2s subspace of F192.
    fn cell(lo: F64, hi: F64) -> F192 {
        F192::new(lo.0, hi.0, 0)
    }

    /// The default one-block-root metadata for a hand-built BLAKE2s op.
    fn md() -> F192 {
        crate::hash_flock::metadata(crate::hash_flock::PINNED_T, crate::hash_flock::FINAL_FLAG, 0)
    }

    /// The four chaining-value lanes of the two cv cells.
    fn cv_lanes(cv0: F192, cv1: F192) -> [F64; 4] {
        [F64(cv0.c0), F64(cv0.c1), F64(cv1.c0), F64(cv1.c1)]
    }

    /// A hand-built straight-line program with one BLAKE2s row: set up the two
    /// 256-bit inputs (`a` at cells 2,3, `b` at cells 4,5, one 128-bit word per
    /// cell) and the metadata (cell 8), hash them into the output `c` (cells 6,7),
    /// pad with filler SETs so the last executed instruction lands one before the
    /// sentinel, and halt there. The flock validity sub-proof plus the memory /
    /// state / bytecode bus interactions are verified end-to-end (the proof
    /// carries the WHIR opening they assert on).
    fn blake2s_program(a: [F64; 4], b: [F64; 4]) -> Program {
        // a → cells 2,3 and b → cells 4,5 (two flock lanes per BLAKE2s cell).
        let mut prog = vec![
            Op::Set {
                o: 2,
                k: cell(a[0], a[1]),
            },
            Op::Set {
                o: 3,
                k: cell(a[2], a[3]),
            },
            Op::Set {
                o: 4,
                k: cell(b[0], b[1]),
            },
            Op::Set {
                o: 5,
                k: cell(b[2], b[3]),
            },
            Op::Set { o: 8, k: md() },
            // The chaining value reads cells 0,1 (the public input); any
            // canonical cv is legal.
            Op::Blake2s {
                ins: [2, 3, 4, 5],
                cv: 0,
                out: 6,
                md: 8,
            },
        ]; // c → cells 6,7
        // 16 slots: 6 executed, then 9 filler SETs step the pc to 15, whose slot is
        // the never-executed sentinel.
        for k in 0..9u32 {
            prog.push(Op::Set {
                o: 16 + k,
                k: F192::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 16);
        Program::from_bytecode(prog, 32)
    }

    /// The opcode's execution semantics: the digest of the two message pairs under
    /// the public input's chaining value lands in the output pair. Proving a program
    /// is exercised from `lean_compiler`'s tests, which can compile one whose tables
    /// come out powers of two.
    #[test]
    fn blake2s_computes_the_compression() {
        let a: [F64; 4] = [
            F64(0x0123_4567_89ab_cdef),
            F64(0xfedc_ba98_7654_3210),
            F64(0x1111_2222_3333_4444),
            F64(0x5555_6666_7777_8888),
        ];
        let b: [F64; 4] = [
            F64(0xdead_beef_cafe_babe),
            F64(0x0badf00d_0badf00d),
            F64(0x9999_aaaa_bbbb_cccc),
            F64(0xdddd_eeee_ffff_0000),
        ];
        let program = blake2s_program(a, b);

        let pi = [w(7), w(11)];
        let exec = program.execute(pi);

        // The output cells hold the compression of the two inputs under the
        // pi-supplied chaining value (two 128-bit chunks).
        let d = blake2s_compress(a, b, cv_lanes(pi[0], pi[1]), md());
        assert_eq!(exec.mem[6], cell(d[0], d[1]));
        assert_eq!(exec.mem[7], cell(d[2], d[3]));
    }

    /// BLAKE consumes the `(c0,c1,0)` embedding. This is not an extra AIR
    /// constraint: the full three-limb memory bus makes a request carrying a
    /// literal zero in limb 2 match only such a stored word.
    #[test]
    #[should_panic(expected = "BLAKE2s m0 cell is not a canonical 128-bit embedding")]
    fn blake2s_requires_zero_third_limb() {
        let mut program = blake2s_program([F64::ZERO; 4], [F64::ZERO; 4]);
        program.prog[0] = Op::Set {
            o: 2,
            k: F192::new(0, 0, 1),
        };
        let _ = program.execute([w(7), w(11)]);
    }

    /// A self-hash `BLAKE2s(h, h)` (the hash-chain step) passes the *same* input
    /// chunks as both `a` and `b` (`ins[0..2] == ins[2..4]`), so one 256-bit quad
    /// feeds both inputs with no copy. The row reads those cells twice; the
    /// running access counts thread through and the bus still balances. This is
    /// the aliasing the DSL's hash-chain lowering relies on.
    #[test]
    fn blake2s_self_hash_aliased_operands() {
        let h: [F64; 4] = [
            F64(0xfeed_face_dead_beef),
            F64(0x0123_4567_89ab_cdef),
            F64(0xcafe_d00d_1337_c0de),
            F64(0x8877_6655_4433_2211),
        ];
        // a == b: hash h ‖ h into cells 4,5, both input operands aliasing one pair
        let mut prog = vec![
            Op::Set {
                o: 2,
                k: cell(h[0], h[1]),
            },
            Op::Set {
                o: 3,
                k: cell(h[2], h[3]),
            },
            Op::Set { o: 6, k: md() },
            Op::Blake2s {
                ins: [2, 3, 2, 3],
                cv: 0,
                out: 4,
                md: 6,
            },
        ];
        // 8 slots: 4 executed, 3 filler SETs stepping the pc, then the sentinel.
        for k in 0..3u32 {
            prog.push(Op::Set {
                o: 12 + k,
                k: F192::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 8);
        let program = Program::from_bytecode(prog, 16);
        let pi = [w(3), w(5)];

        let exec = program.execute(pi);
        let d = blake2s_compress(h, h, cv_lanes(pi[0], pi[1]), md());
        assert_eq!(exec.mem[4], cell(d[0], d[1]));
        assert_eq!(exec.mem[5], cell(d[2], d[3]));
    }

    /// A 192-bit-word MUL: the E-product of two full machine words. Full-limb
    /// constants are why this one is hand-written bytecode: a source literal fills
    /// only the low two limbs.
    #[test]
    fn mul_192bit_word() {
        let x = F192::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef, 0x1111_2222_3333_4444);
        let y = F192::new(0x9999_aaaa_bbbb_cccc, 0x1357_9bdf_2468_ace0, 0x5555_6666_7777_8888);
        let prog = vec![
            Op::Set { o: 2, k: x },
            Op::Set { o: 3, k: y },
            Op::Mul { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel (never executed)
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [w(1), w(2)];
        let exec = program.execute(pi);
        assert_eq!(exec.mem[4], x * y, "MUL computes the E product");
    }
}
