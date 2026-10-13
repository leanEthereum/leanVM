//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g. Machine-word arithmetic
//! is over `E = F192 = K[y]/(y³+y+1)` (XOR degree 1, MUL_NATIVE degree 2),
//! with each word carried by three committed `K = F64` limbs. `SHA3` adds the
//! memory/state/bytecode plumbing for one Keccak-f sponge step whose relation
//! is discharged by the Keccak reduction (see [`crate::keccak`]). All
//! challenges and transcript scalars live in the same tower E.

use std::collections::HashMap;

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_SHA3, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
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
pub use execute::{ExecError, Execution, Fault};
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Brow, Drow, Jrow, Srow, Trace, Xrow};

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
/// Two things go in. [`crate::keccak::relation_digest`] names the Keccak
/// relation and how its reduction is parameterized, independent of the instance
/// count, which is announced and absorbed with the other sizes, so one constant
/// covers every shape. And the bytecode enters through the hash
/// cached on `Program`, the hash of the stacked multilinear
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
    let relation = crate::keccak::relation_digest();
    h.update(&(relation.len() as u64).to_le_bytes());
    h.update(&relation);
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
        // The Keccak reduction is sized for at least `2^n_blocks_log(1)` steps, and the
        // SHA3 table's value columns share that instance cube, so a height below the
        // floor describes a layout the arithmetization cannot express. The other two
        // verifiers reject it here too (`python-verifier`, `guests/lean_ethereum.py`).
        || taus[tables::SHA3_TABLE] < crate::keccak::n_blocks_log(1)
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
    /// The hash of the stacked bytecode multilinear, computed once at assembly
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

    /// Instructions before the pad to a power of two: the compiled functions, or
    /// the whole bytecode of a hand-assembled program.
    pub fn code_len(&self) -> usize {
        match self.fn_ranges.as_slice() {
            [] => self.prog.len(),
            ranges => ranges.iter().map(|&(_, _, len)| len as usize).sum(),
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

/// Why [`prove`] produced no proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    /// `log_inv_rate` is outside the range the WHIR configuration accepts (1, 2, 3 or 4).
    InvalidRate { log_inv_rate: usize },
    /// The program has no execution on this input and advice: a failed `assert`,
    /// a wild pointer, advice that does not fit, ...
    Execution(ExecError),
    /// The run read these cells before anything wrote them, so their values would be
    /// the prover's ([`Execution::unconstrained_reads`]).
    UnconstrainedReads(Vec<u32>),
    /// The committed witness is `2^log_committed` words, outside the
    /// `2^MIN_MU..=2^MAX_MU` every verifier accepts
    WitnessOutOfRange { log_committed: usize },
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRate { log_inv_rate } => write!(f, "log_inv_rate {log_inv_rate} is not supported"),
            Self::Execution(e) => write!(f, "{e}"),
            Self::UnconstrainedReads(cells) => write!(
                f,
                "the program read {} cell(s) before anything wrote them, first at {:?}: a source read \
                 of a cell nothing stores, or a store the lowering dropped or misplaced",
                cells.len(),
                &cells[..cells.len().min(8)]
            ),
            Self::WitnessOutOfRange { log_committed } => write!(
                f,
                "the committed witness would be 2^{log_committed} words, outside the verifiable 2^{}..=2^{}",
                pcs::MIN_MU,
                pcs::MAX_MU
            ),
        }
    }
}

impl std::error::Error for ProveError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CpuError {
    Bus(leaf::Error),
    Constraint(constraints::Error),
    Open(pcs::Error),
    PublicInput,
    Transcript(crate::transcript::Error),
    /// The Keccak reduction's sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`CpuError::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Sha3(keccak_gkr::VerifyError),
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
                eval: Box::new(move |p, vals, quadratic| {
                    let air = <F192 as ColVal>::lift(table.eval_constraint(p, vals, quadratic));
                    <F192 as ColVal>::reduce(air ^ bus.eval_unreduced(vals, quadratic))
                }),
                // The same expression over K columns: the identity's K-only products
                // stay 64-bit and the bus form becomes a mixed dot product.
                eval_k: Box::new(move |p, vals, quadratic| {
                    let air = <F64 as ColVal>::lift(table.eval_constraint_k(p, vals, quadratic));
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

/// If `col` is a SHA3 **value** column (global index), its `q_keccak` slot and the
/// constant the committed lane differs by.
/// These columns are virtual (uncommitted): their memory-bus evaluation claims
/// are re-routed to `q_keccak` slot evaluations, which is the whole binding: the
/// bus-tied value IS the proven `q_keccak` word, no separate check needed.
fn sha3_value_slot(col: usize) -> Option<(usize, F192)> {
    let base = schema().base[tables::SHA3_TABLE];
    tables::SHA3_VALUE_COLS
        .iter()
        .position(|&c| base + c == col)
        .map(crate::keccak::value_slot)
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts
/// `[XOR, MUL, SET, DEREF, JUMP, SHA3]`, and the
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
    /// Bytecode instructions, before the pad to a power of two ([`Program::code_len`]).
    pub bytecode: usize,
}

impl Stats {
    /// Table names in `counts` order.
    pub const TABLES: [&'static str; tables::N_TABLES] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "SHA3"];

    /// One line of per-table instruction counts and shares, largest first, followed by memory, bytecode and committed-witness sizes.
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
        parts.push(format!("BYTECODE 2^{}", log2(self.bytecode)));
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`], or why no proof was made ([`ProveError`]). `log_inv_rate`
/// selects the PCS rate and is announced in the Fiat-Shamir transcript before
/// the commitment.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(program: &Program, public_input: [F192; 2], log_inv_rate: usize) -> Result<(Proof, Stats), ProveError> {
    if ::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err() {
        return Err(ProveError::InvalidRate { log_inv_rate });
    }
    let (exec, sha3_blocks) = crate::stage!("Execute program", || {
        crate::keccak::while_executing(|step| program.execute_with(public_input, step))
    });
    let exec = exec.map_err(ProveError::Execution)?;
    // A live value that came from outside the constraint system would make the proof
    // about a weaker statement than the program text, so it is refused here, on the one
    // path every proof takes, rather than left to whichever test happens to look.
    if !exec.unconstrained_reads.is_empty() {
        return Err(ProveError::UnconstrainedReads(exec.unconstrained_reads));
    }
    let cycles = exec.cycles;
    let w = crate::stage!("Build witness", || program.build(&exec, sha3_blocks));
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&w.layout.shape.mu) {
        return Err(ProveError::WitnessOutOfRange {
            log_committed: w.layout.shape.mu,
        });
    }
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

    // SHA3 (§keccak), single PCS: q_keccak is ALWAYS a column in `w.q` (the
    // SHA3 table is filled to the reduction's floor, so the proof shape is uniform
    // and there is no has/hasn't-SHA3 fork). The Keccak reduction's claims and
    // EVERY leanVM point claim are discharged together by ONE
    // WHIR over this commitment (below). Input and output lanes bind through the
    // memory bus: their virtual value columns route to q_keccak, so no separate pin
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

    // The PI binding (§sec:e2e-pi) transmits nothing: its claims are the public
    // input's limb lines at `r_pi`, which the verifier evaluates itself. `r_pi`
    // is still a challenge, squeezed after the commitment so the memory cannot
    // be chosen to fit it.
    let r_pi = ps.sample();
    // Memory binds the message, chaining-value, and output words; bytecode binds
    // the counter and flags. All corresponding value columns are virtual and route
    // to q_keccak through `slot_claims`.
    let mut slots = finish_claims(l, bus.claims, &table_claims, r_pi);

    // Run the Keccak reduction over the witness retained from the q_keccak build
    // pass; it returns two claims on the committed `q_keccak`, discharged by the
    // PCS below in the SAME WHIR as every leanVM point claim: one ring-switched,
    // one appended to the point claims.
    let keccak_reduction = w.keccak_reduction;
    let n_blocks = 1usize << w.layout.taus[tables::SHA3_TABLE];
    let offset = w.layout.placements[QKECCAK].offset;
    let q_keccak = &w.q[offset..offset + (1 << crate::keccak::qkeccak_kappa(n_blocks))];
    let openings = crate::stage!("Keccak reduction", || { keccak_reduction.prove(&mut ps, q_keccak) });
    drop(keccak_reduction);
    let (ring, outputs) = crate::keccak::ring_switch_open(n_blocks, offset, openings);
    slots.push(outputs);
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &ring) });
    Ok((
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            base_counts: exec.base_counts,
            committed: committed_size,
            log_mem: w.log_mem,
            mem_used: exec.mem_used,
            bytecode: program.code_len(),
        },
    ))
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
    claims.extend(bind_pi_claim(r_pi, l));
    slot_claims(l, claims)
}

/// The public-input binding (§sec:e2e-pi): each committed `MEM` limb at
/// `(r, 0,…,0)` must equal the line through that limb of `pi[0]` and `pi[1]`.
/// The public input is the statement, so both sides evaluate the lines
/// themselves and build byte-identical claims from their layouts; the prover
/// sends nothing. The verifier has rejected a nonzero top limb, so that claim is 0.
fn bind_pi_claim(r: F192, l: &Layout) -> [ColumnClaim; 3] {
    let [a, b] = l.pi;
    let limbs = [(a.c0, b.c0), (a.c1, b.c1), (a.c2, b.c2)];
    let mut point = vec![F192::ZERO; l.placements[MEM_LO].n_vars];
    point[0] = r;
    [MEM_LO, MEM_HI, MEM_TOP].map(|col| {
        let (x, y) = limbs[col - MEM_LO];
        ColumnClaim {
            col,
            point: point.clone(),
            value: primitives::multilinear::interp_k(F64(x), F64(y), r),
        }
    })
}

/// Everything a recursion harness needs from an accepting verify run, named
/// and typed: the deferred bytecode claim and the raw proof. The Keccak
/// reduction's scalars live on `proof.stream`, ending at `keccak_stream_end`.
/// Ordinary callers just `?`-discard it.
pub struct VerifySummary {
    /// Transcript-bound inverse-rate logarithm used by this proof's PCS.
    pub log_inv_rate: usize,
    pub bytecode_claim: leaf::BytecodeClaim,
    /// Stream cursor just after the Keccak reduction, i.e. where the PCS opening's
    /// own scalars start.
    pub keccak_stream_end: usize,
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

    // SHA3 (single PCS): the Keccak reduction's claims and every leanVM point
    // claim are verified together by ONE WHIR opening at the end. The SHA3 table
    // size is public and announced; the reduction rides the shared stream.
    // Memory binds every step's input and output lanes by routing
    // their virtual value-column claims to q_keccak.
    let n_sha3 = 1usize << l.taus[tables::SHA3_TABLE];

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

    // Squeezed after the commitment and every message before it, so the prover
    // cannot choose the memory to fit it; the claims it yields read no scalar.
    let r_pi = vs.sample();
    let mut slots = finish_claims(&l, bus.claims, &table_claims, r_pi);

    // Replay the Keccak reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its two claims on q_keccak, then
    // verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`).
    let n_blocks = n_sha3.max(1);
    let offset = l.placements[QKECCAK].offset;
    let openings = crate::keccak::verify_reduction(n_blocks, &mut vs).map_err(CpuError::Sha3)?;
    let keccak_stream_end = vs.stream_offset();
    let (ring, outputs) = crate::keccak::ring_switch_verify(n_blocks, offset, &openings);
    slots.push(outputs);
    pcs::verify(&mut vs, &slots, &ring, l.shape, log_inv_rate, &root).map_err(CpuError::Open)?;
    vs.finish().map_err(CpuError::Transcript)?;
    Ok(VerifySummary {
        bytecode_claim: bus.bytecode_claim,
        log_inv_rate,
        keccak_stream_end,
        raw: vs.into_raw_proof(),
    })
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// SHA3 value columns are virtual: they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_keccak` slot evaluation: an ordinary claim on the committed
/// `QKECCAK` column at the point whose low coords are `r` and whose next
/// `SLOT_LOG` are the slot's bits, shifted by the slot's constant. No downstream
/// special-casing: it folds into the one opening like every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| {
            // A SHA3 value column (always virtual): its bus claim at instance point
            // `c.point` is a claim on the slot's `2^n_log` words of QKECCAK.
            if let Some((slot, shift)) = sha3_value_slot(c.col) {
                return pcs::SlotClaim::Point {
                    offset: l.placements[QKECCAK].offset + (slot << c.point.len()),
                    low_point: c.point,
                    value: c.value + shift,
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

    /// A hand-built straight-line program with one SHA3 row: two message cells
    /// (2, 3) read twice as `m`, a four-cell `tail` (4..8), a zero five-cell `cap`
    /// (8..13), and the output run (13..26), padded with filler SETs so the last
    /// executed instruction lands one before the sentinel.
    fn sha3_program(a: F192, b: F192, tail: [F192; 4]) -> Program {
        let mut prog = vec![Op::Set { o: 2, k: a }, Op::Set { o: 3, k: b }];
        for (i, &t) in tail.iter().enumerate() {
            prog.push(Op::Set { o: 4 + i as u32, k: t });
        }
        for c in 0..5u32 {
            prog.push(Op::Set {
                o: 8 + c,
                k: F192::ZERO,
            });
        }
        prog.push(Op::Sha3 {
            m: [2, 3, 2, 3],
            tail: 4,
            cap: 8,
            out: 13,
        });
        // 16 slots: 12 executed, then 3 filler SETs step the pc to 15, whose slot is
        // the never-executed sentinel.
        for k in 0..3u32 {
            prog.push(Op::Set {
                o: 26 + k,
                k: F192::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 16);
        Program::from_bytecode(prog, 32)
    }

    /// The opcode's execution semantics: the thirteen output cells hold the step
    /// of the thirteen input cells, the two `m` pairs aliasing one another. With a
    /// zero `cap` and the padding in `tail`, the first two output cells are the
    /// hash of the 64 message bytes. Proving a program is exercised from
    /// `lean_compiler`'s tests, which can compile one whose tables come out powers
    /// of two.
    #[test]
    fn sha3_computes_the_step() {
        let a = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0);
        let b = F192::new(0xdead_beef_cafe_babe, 0x0bad_f00d_0bad_f00d, 0);
        let pad = F192::new(primitives::hash::PAD_FIRST as u64, 0, 0);
        let program = sha3_program(a, b, [pad, F192::ZERO, F192::ZERO, F192::ZERO]);
        let exec = program.execute([w(7), w(11)]).unwrap();

        let mut input = [F192::ZERO; crate::keccak::STATE_CELLS];
        input[..4].copy_from_slice(&[a, b, a, b]);
        input[4] = pad;
        let out = crate::keccak::step_cells(&input);
        assert_eq!(&exec.mem[13..26], &out[..]);

        let bytes: Vec<u8> = [a, b, a, b]
            .iter()
            .flat_map(|c| [c.c0, c.c1])
            .flat_map(u64::to_le_bytes)
            .collect();
        let digest: Vec<u8> = [out[0], out[1]]
            .iter()
            .flat_map(|c| [c.c0, c.c1])
            .flat_map(u64::to_le_bytes)
            .collect();
        assert_eq!(digest, primitives::hash::hash(&bytes));
    }

    /// A state cell carries `(lo, hi, 0)`. This is not an extra AIR constraint: the
    /// memory bus makes a read carrying a literal zero in limb 2 match only such a
    /// stored word.
    #[test]
    fn sha3_requires_zero_third_limb() {
        let err = sha3_program(F192::new(0, 0, 1), F192::ZERO, [F192::ZERO; 4])
            .execute([w(7), w(11)])
            .err()
            .expect("the run must fail");
        assert!(
            matches!(err.fault, Fault::NotCanonical { cell: 0, bits: 128, .. }),
            "{err}"
        );
    }

    /// The lone lane-16 cell carries `(lo, 0, 0)`, read with two literal zeros.
    #[test]
    fn sha3_requires_zero_lone_high_lane() {
        let mut program = sha3_program(F192::ZERO, F192::ZERO, [F192::ZERO; 4]);
        program.prog[6] = Op::Set {
            o: 8,
            k: F192::new(0, 1, 0),
        };
        let err = program.execute([w(7), w(11)]).err().expect("the run must fail");
        assert!(
            matches!(err.fault, Fault::NotCanonical { cell: 8, bits: 64, .. }),
            "{err}"
        );
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
        let exec = program.execute(pi).unwrap();
        assert_eq!(exec.mem[4], x * y, "MUL computes the E product");
    }

    /// The `XOR` reads `m[2]` before the `SET` writes it, so it reads ZERO, and its
    /// row, filled from the final image, would contradict any other value there.
    #[test]
    fn a_write_must_agree_with_an_earlier_read() {
        let prog = vec![
            Op::Xor { a: 2, b: 0, c: 3 },
            Op::Set { o: 2, k: F192::ONE },
            Op::Set { o: 4, k: F192::ZERO },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel (never executed)
        ];
        let err = Program::from_bytecode(prog, 8)
            .execute([F192::ZERO; 2])
            .err()
            .expect("the run must fail");
        assert!(matches!(err.fault, Fault::Conflict { cell: 2, .. }), "{err}");
    }
}
