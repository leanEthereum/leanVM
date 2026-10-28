//! Whole-program assembly over GF(2^64) (`doc/leanvm/main.tex`): the instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g. Machine-word arithmetic
//! is over `E = F192 = K[y]/(y³+y+1)` (XOR degree 1, MUL_NATIVE degree 2),
//! with each word carried by three committed `K = F64` limbs. `KECCAK` adds the
//! memory/state/bytecode plumbing for one Keccak-f sponge step whose relation
//! is discharged by the Keccak reduction (see [`crate::keccak`]). All
//! challenges and transcript scalars live in the same tower E.

use std::collections::HashMap;

use crate::colval::ColVal;
use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_DEREF, OP_JUMP, OP_KECCAK, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
};
use crate::transcript::ProverState;
use crate::witness;
use primitives::field::{F64, F192, g_pow};

mod execute;
pub mod hints;
mod isa;
pub mod layout;
mod trace;
pub(crate) use execute::Cell;
pub use execute::{ExecError, Execution, Fault, Memory};
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Drow, Jrow, Krow, Rows, Srow, Trace, Xrow};

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

/// The Fiat-Shamir IV: ONE 32-byte digest, as two field words, committing to
/// everything fixed about the proving environment.
///
/// It is [`verifier::TAG`] followed by the stacked bytecode multilinear
/// ([`layout::bytecode_table`]) rather than an assembler digest, so a verifier
/// holding only that polynomial reproduces the seed.
///
/// The IV fills lanes 0..4 of the transcript's first permutation input
/// ([`fiat_shamir::FiatShamirState::new`]), the public input the next four, so all challenges depend on the circuit version and the program before
/// anything else; a recursion guest carries the INNER program's IV in its public
/// input, pinning both with one word pair.
pub fn fs_seed(program: &Program) -> [F192; 2] {
    let d = &program.fiat_shamir_iv;
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)]
}

/// The two 128-bit halves a digest travels in, as the four words the
/// Fiat-Shamir sponge absorbs. Only defined for a real digest, whose halves have
/// no third limb; [`verify`] rejects a public input that has one, so a
/// third limb can never be silently dropped from what the transcript binds.
fn digest_words(halves: &[F192; 2]) -> [F64; 4] {
    [
        F64(halves[0].c0),
        F64(halves[0].c1),
        F64(halves[1].c0),
        F64(halves[1].c1),
    ]
}

/// Announce the prover's sizes (`log_mem`, every table's row count, the PCS rate) by
/// writing them onto the scalar stream, which binds them into the state and lets the
/// verifier reconstruct the layout, every table's height following from its rows
/// ([`layout::table_logs`]). The public statement (program + input) is not announced
/// here; it seeds the transcript at construction (see [`fs_seed`]). The boundary
/// states are derived from the program, so they need no binding.
fn announce_public(ps: &mut ProverState, log_mem: usize, rows: [usize; tables::N_TABLES], log_inv_rate: usize) {
    ps.add_scalar(F192::new(log_mem as u64, 0, 0));
    for n in rows {
        ps.add_scalar(F192::new(n as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
}

#[derive(Clone)]
pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    /// The Fiat-Shamir IV ([`fs_seed`]), computed once at assembly so proofs of
    /// the same program do not rehash the stacked bytecode multilinear (that
    /// table is 16·2^kbc words, tens of megabytes at production sizes). Trusted
    /// to match `prog`: always set by [`Program::assemble`] from the bytecode,
    /// so a `Program` cannot carry an IV inconsistent with its own `prog`.
    pub(crate) fiat_shamir_iv: [u8; 32],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame: the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification ([`verify`]) ignores them.
    pub(crate) hints: HashMap<u32, Vec<hints::RHint>>,
    pub(crate) main_frame: u32,
    /// Named prover witness streams for the program's `hint_witness` calls
    /// ([`Program::set_witness`]): a stream is a sequence of *entries* (one
    /// slice of values per `hint_witness` call; the same symbol may be
    /// hinted many times); each call pops the next entry, whose length must
    /// match its destination. Prover-side only; verification ignores them.
    pub(crate) witness: HashMap<String, Vec<Vec<F192>>>,
    /// Function pc-ranges `(name, entry, len)` from the compiler, for the
    /// `DBG_PROF=1` per-function cycle profile ([`Program::execute`]). Purely
    /// diagnostic; empty for hand-assembled programs.
    pub fn_ranges: Vec<(String, u32, u32)>,
    /// Source line of the statement that emitted each pc. Prover-side only, and
    /// outside `fiat_shamir_iv`, so it costs nothing in the proof: a failed guest
    /// check reports a line rather than a pc to disassemble around. Empty for a
    /// hand-assembled program, and shorter than `prog`, which is padded.
    pub src_lines: Vec<u32>,
    /// The smallest stacked witness this program's proofs may commit to, as a
    /// log2. Zero (the default) asks for nothing.
    ///
    /// A consumer can need a proof to be no smaller than some size even when the
    /// run is: the recursion guest holds one WHIR opening arm per committed size
    /// it was compiled for, and has none below the first. A run that falls short
    /// buys the difference in unused memory cells rather than in a padded commitment,
    /// which keeps the committed size a function of the announced sizes, so neither
    /// the verifier nor the guest needs a new parameter to certify. Prover-side only.
    pub min_log_committed: usize,
}

/// The IV reinterprets the stacked bytecode table as bytes, which is its
/// `to_le_bytes` image only on a little-endian target.
const _: () = assert!(cfg!(target_endian = "little"));

impl Program {
    /// Assemble a [`Program`], computing its Fiat-Shamir IV
    /// from `prog`. The single funnel for construction, so the digest is always
    /// consistent with the bytecode.
    pub fn assemble(prog: Vec<Op>, hints: HashMap<u32, Vec<hints::RHint>>, main_frame: u32) -> Self {
        let fiat_shamir_iv = {
            let table = layout::bytecode_table(&prog);
            // SAFETY: F64 is #[repr(transparent)] over u64, so the slice's byte image is
            // exactly the concatenation of its `to_le_bytes` on little-endian targets.
            let bytes: &[u8] =
                unsafe { core::slice::from_raw_parts(table.as_ptr().cast::<u8>(), core::mem::size_of_val(&table[..])) };
            primitives::hash::Hasher::new()
                .update(verifier::TAG)
                .update(bytes)
                .finalize()
        };
        Self {
            prog,
            fiat_shamir_iv,
            hints,
            main_frame,
            witness: HashMap::new(),
            fn_ranges: Vec::new(),
            src_lines: Vec::new(),
            min_log_committed: 0,
        }
    }

    /// Where `pc` came from: `"verify_sub (line 2204)"` when the compiler left a
    /// line for it, the function name alone otherwise (a hand-assembled program,
    /// or padding). This is what a run-time failure reports, so
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
    /// allocation). `prog.len()` must be a power of two: the run halts on reaching
    /// the final state `(g^{len-1}, g^0)`, the last slot in main's frame (§sec:state).
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

/// Why [`verify`] rejected a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CpuError {
    /// The statement is malformed: the public input is not two 128-bit halves, or the bytecode's length is not a power of two.
    PublicInput,
    /// The `verifier` crate rejected the proof.
    Verifier(verifier::VerifierError),
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
/// column span. Derived from the program and the announced layout alone, so a
/// verifier builds the same one.
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
            let bus = RowForm::new(&leaf::BusForm::sum((0..3).map(|s| forms[s][t].scaled(form_pows[s]))));
            let bus_k = bus.clone();
            constraints::Air {
                tau,
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

/// A table's bus form as the batch evaluates it on every row of every round: its
/// nonzero coefficients, and its products grouped by a column they share,
/// `Σ_a v_a·(Σ_b c_ab·v_b)`, so a column that several products share multiplies
/// once rather than once per product. The arithmetic is exact, so the value is the form's.
#[derive(Clone)]
struct RowForm {
    linear: Vec<(usize, F192)>,
    constant: F192,
    groups: Vec<(usize, Vec<(usize, F192)>)>,
}

impl RowForm {
    fn new(form: &leaf::BusForm) -> Self {
        let n = form.coeffs.len();
        let linear = (0..n)
            .filter(|&i| !form.coeffs[i].is_zero())
            .map(|i| (i, form.coeffs[i]))
            .collect();
        let mut prods = form.prods.clone();
        let mut groups: Vec<(usize, Vec<(usize, F192)>)> = Vec::new();
        // Greedily factor out the column the most remaining products share.
        while !prods.is_empty() {
            let mut shared = vec![0usize; n];
            for &(a, b, _) in &prods {
                shared[a] += 1;
                if b != a {
                    shared[b] += 1;
                }
            }
            let col = (0..n)
                .max_by_key(|&c| (shared[c], std::cmp::Reverse(c)))
                .expect("a column");
            let (with, rest): (Vec<_>, Vec<_>) = prods.into_iter().partition(|&(a, b, _)| a == col || b == col);
            groups.push((
                col,
                with.into_iter()
                    .map(|(a, b, c)| (if a == col { b } else { a }, c))
                    .collect(),
            ));
            prods = rest;
        }
        Self {
            linear,
            constant: form.constant,
            groups,
        }
    }

    /// The form at one row, unreduced, or only its degree-two terms when `quadratic`.
    #[inline(always)]
    fn eval_unreduced<T: ColVal>(&self, vals: &[T], quadratic: bool) -> T::Unreduced {
        let mut acc = if quadratic {
            T::lift(F192::ZERO)
        } else {
            self.linear
                .iter()
                .fold(T::lift(self.constant), |acc, &(i, c)| acc ^ vals[i].mul_e_unreduced(c))
        };
        for (a, terms) in &self.groups {
            if let [(b, c)] = terms[..] {
                acc ^= (vals[*a] * vals[b]).mul_e_unreduced(c);
                continue;
            }
            let inner = terms
                .iter()
                .fold(T::lift(F192::ZERO), |acc, &(b, c)| acc ^ vals[b].mul_e_unreduced(c));
            acc ^= vals[*a].mul_e_unreduced(T::reduce(inner));
        }
        acc
    }
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
/// (a mismatch fails its table sumcheck's terminal check). Were the
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

/// The KECCAK table's claims on its output lanes, which are the Keccak reduction's claim on
/// the permutation's output: the batch claims every column of the table at one point.
fn keccak_output_claim(table_claims: &[constraints::Claims]) -> keccak_gkr::OutputClaim {
    let claims = &table_claims[tables::KECCAK_TABLE];
    keccak_gkr::OutputClaim {
        instance: claims.chi.clone(),
        lanes: std::array::from_fn(|l| claims.evals[tables::keccakt::V_OUT + l]),
    }
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode row counts `[XOR, MUL, SET, DEREF, JUMP, KECCAK]`,
/// and the committed witness size, the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    /// Rows per table the program executed.
    pub rows: [usize; tables::N_TABLES],
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
    /// Table names in `rows` order.
    pub const TABLES: [&'static str; tables::N_TABLES] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "KECCAK"];

    /// One line of per-table instruction counts and shares, largest first, followed by memory, bytecode and committed-witness sizes.
    ///
    /// `log_mem` holds the padded memory size the commitment covers. Zero-count
    /// tables are omitted.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }
        let mut shares: Vec<(&str, usize)> = Self::TABLES
            .iter()
            .zip(&self.rows)
            .filter(|&(_, &c)| c > 0)
            .map(|(&name, &c)| (name, c))
            .collect();
        shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
        let mut parts: Vec<String> = shares
            .iter()
            .map(|&(name, c)| {
                let pct = 100.0 * c as f64 / self.cycles as f64;
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
    let (exec, keccak_blocks) = crate::stage!("Execute program", || {
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
    let mut w = crate::stage!("Build witness", || program.build(&exec, keccak_blocks));
    if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&w.layout.shape.mu) {
        return Err(ProveError::WitnessOutOfRange {
            log_committed: w.layout.shape.mu,
        });
    }
    let committed_size = w.committed_size();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    debug_assert!(
        public_input.iter().all(|h| h.c2 == 0),
        "a public input is a 256-bit digest"
    );
    let mut ps = ProverState::new(
        fiat_shamir::digest_words(&program.fiat_shamir_iv),
        digest_words(&public_input),
    );

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.layout.rows, log_inv_rate);
    let committed = crate::stage!("Commit", || {
        pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate)
    });

    // KECCAK (§keccak), single PCS: q_keccak is ALWAYS a column in `w.q` (the
    // KECCAK table is filled to the reduction's floor, so the proof shape is uniform
    // and there is no has/hasn't-KECCAK fork). The Keccak reduction's claims and
    // EVERY leanVM point claim are discharged together by ONE
    // WHIR over this commitment (below). Input and output lanes bind through the
    // memory bus: their virtual value columns route to q_keccak (inputs) and to the
    // reduction's output claim (outputs), so no separate pin claims are needed.
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
    // The bus and the constraints were the output lanes' last readers.
    drop(std::mem::take(&mut w.virt));
    let l = &w.layout;

    // The PI binding (§sec:e2e-pi) transmits nothing: its claims are the public
    // input's limb lines at `r_pi`, which the verifier evaluates itself. `r_pi`
    // is still a challenge, squeezed after the commitment so the memory cannot
    // be chosen to fit it.
    let r_pi = ps.sample();
    // Memory binds every step's input and output words. Their value columns are
    // virtual: the inputs route to q_keccak through `slot_claims`, the outputs are
    // the reduction's claim on the permutation's output.
    let mut slots = finish_claims(l, bus.claims, &table_claims, r_pi);
    let output = keccak_output_claim(&table_claims);

    // Run the Keccak reduction over the witness retained from the q_keccak build
    // pass; it returns two claims on the committed `q_keccak`, discharged by the
    // PCS below in the SAME WHIR as every leanVM point claim: one ring-switched,
    // one appended to the point claims.
    let keccak_reduction = w.keccak_reduction;
    let witness::Placement { offset, n_vars } = w.layout.placements[QKECCAK];
    let q_keccak = &w.q[offset..][..1 << n_vars];
    let openings = crate::stage!("Keccak reduction", || {
        keccak_reduction.prove(&mut ps, q_keccak, &output)
    });
    drop(keccak_reduction);
    let (ring, outputs) = openings.into_pcs_claims(offset);
    slots.extend(outputs);
    crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &ring) });
    Ok((
        ps.into_proof(),
        Stats {
            cycles,
            rows: w.layout.rows,
            committed: committed_size,
            log_mem: w.log_mem,
            mem_used: exec.mem_used,
            bytecode: program.code_len(),
        },
    ))
}

/// Everything the PCS has to open, in the ORDER that feeds the batch's weights:
/// the bus's framework claims, then the table sumcheck's per-table column claims (less the
/// `KECCAK` output lanes', which go to the reduction), then the three public-input limb
/// claims, each located in its committed slot. Every verifier assembles the same list in
/// the same order.
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
            let col = sch.base[t] + c;
            if let Some(KeccakLane::Output(_)) = keccak_value(col) {
                continue; // the Keccak reduction's claim on the output (`keccak_output_claim`)
            }
            claims.push(ColumnClaim {
                col,
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

/// A field element in the `verifier` crate's type, and back: the same limbs, no arithmetic.
pub fn to_scalar(value: &F192) -> verifier::E {
    verifier::E::new(value.c0, value.c1, value.c2)
}

pub fn from_scalar(value: verifier::E) -> F192 {
    F192::new(value.c0, value.c1, value.c2)
}

/// The wire proof in the `verifier` crate's types: the same limbs, digests and row words.
pub fn scalar_proof(proof: &Proof) -> verifier::Proof {
    let batches = proof.merkle.iter().map(|paths| verifier::PrunedMerklePaths {
        leaf_data: paths
            .leaf_data
            .iter()
            .map(|row| row.iter().map(|word| verifier::K(word.0)).collect())
            .collect(),
        sibling_hashes: paths.sibling_hashes.clone(),
    });
    verifier::Proof {
        stream: proof.stream.iter().map(to_scalar).collect(),
        merkle_openings: verifier::MerkleOpenings::Pruned(batches.collect()),
    }
}

/// The statement as the 32 bytes the `verifier` crate takes: the low two limbs of each half.
pub fn public_input_bytes(public_input: &[F192; 2]) -> [u8; 32] {
    let mut bytes = [0; 32];
    let limbs = public_input.iter().flat_map(|half| [half.c0, half.c1]);
    for (chunk, limb) in bytes.as_chunks_mut().0.iter_mut().zip(limbs) {
        *chunk = limb.to_le_bytes();
    }
    bytes
}

/// Verify a proof against the public statement (program + public input). The `verifier` crate does it: this only builds its inputs.
///
/// The stacked bytecode is rebuilt and rehashed on every call. A caller verifying many proofs of one program prepares a [`verifier::Bytecode`] once instead.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(program: &Program, public_input: &[F192; 2], proof: &Proof) -> Result<verifier::Summary, CpuError> {
    // The statement is two 128-bit halves, so a third limb would be dropped and two statements would share a proof.
    // `Program::prog` is public, and the stacked table below is only defined for a power-of-two bytecode.
    if public_input.iter().any(|half| half.c2 != 0) || !program.prog.len().is_power_of_two() {
        return Err(CpuError::PublicInput);
    }
    let table: Vec<u64> = layout::bytecode_table(&program.prog)
        .iter()
        .map(|word| word.0)
        .collect();
    let bytecode = verifier::Bytecode::new(&table);
    verifier::verify_execution(&bytecode, &public_input_bytes(public_input), &scalar_proof(proof))
        .map_err(CpuError::Verifier)
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// The columns `q_keccak` carries are virtual: they have no committed placement. A claim
/// `col(r) = v` on one (at the `n_log`-dim instance point `r`) is re-routed to the equal
/// `q_keccak` slot evaluation: an ordinary claim on the committed `QKECCAK` column at the
/// point whose low coords are `r` and whose next `SLOT_LOG` are the slot's bits. No
/// downstream special-casing: it folds into the one opening like every other point claim.
fn slot_claims(l: &Layout, claims: Vec<ColumnClaim>) -> Vec<pcs::SlotClaim> {
    claims
        .into_iter()
        .map(|c| {
            // A KECCAK value column (always virtual): its bus claim at instance point
            // `c.point` is a claim on the slot's `2^n_log` words of QKECCAK.
            if let Some(KeccakLane::Slot(slot)) = keccak_value(c.col) {
                return pcs::SlotClaim::Point {
                    offset: l.placements[QKECCAK].offset + (slot << c.point.len()),
                    low_point: c.point,
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

    /// A hand-built straight-line program with two KECCAK rows. The first reads, in the even
    /// layout, two message cells (2, 3) twice as `m`, a four-cell `tail` (4..8), `b8` (8) and a
    /// zero `cap` (9..13), and writes 13..26 in the odd layout; the second reads that output in
    /// the odd layout and writes 26..39 in the even one. Two filler SETs step the pc to 15, whose
    /// slot is the never-executed sentinel.
    fn keccak_program(a: F192, b: F192, tail: [F192; 4], b8: F192) -> Program {
        let mut prog = vec![Op::Set { o: 2, k: a }, Op::Set { o: 3, k: b }];
        for (i, &t) in tail.iter().enumerate() {
            prog.push(Op::Set { o: 4 + i as u32, k: t });
        }
        prog.push(Op::Set { o: 8, k: b8 });
        for c in 0..4u32 {
            prog.push(Op::Set {
                o: 9 + c,
                k: F192::ZERO,
            });
        }
        prog.push(Op::Keccak {
            m: [2, 3, 2, 3],
            tail: 4,
            b8: 8,
            cap: 9,
            out: 13,
            in_odd: false,
            out_odd: true,
        });
        prog.push(Op::Keccak {
            m: [13, 14, 15, 16],
            tail: 17,
            b8: 21,
            cap: 22,
            out: 26,
            in_odd: true,
            out_odd: false,
        });
        for k in 0..2u32 {
            prog.push(Op::Set {
                o: 39 + k,
                k: F192::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 16);
        Program::from_bytecode(prog, 64)
    }

    /// The opcode's execution semantics: the output cells hold the permutation of the lanes the
    /// input cells hold, each side in its layout, the two `m` pairs aliasing one another and
    /// `b8`'s free high limb ignored. With a zero `cap` and the padding in `tail` and `b8`, the
    /// first permutation's first four lanes are the hash of the 64 message bytes. Hand-assembled,
    /// the program is provable all the same: its tables are not powers of two.
    #[test]
    fn keccak_permutes_in_both_layouts() {
        use crate::keccak::{STATE_CELLS, permute_cells, state_of_cells};
        let a = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0);
        let b = F192::new(0xdead_beef_cafe_babe, 0x0bad_f00d_0bad_f00d, 0);
        let pad = F192::new(primitives::hash::PAD_FIRST as u64, 0, 0);
        let end = F192::new(primitives::hash::END_BIT, 0x5555, 0);
        let program = keccak_program(a, b, [pad, F192::ZERO, F192::ZERO, F192::ZERO], end);
        let pi = [w(7), w(11)];
        let exec = program.execute(pi).unwrap();

        let mut input = [F192::ZERO; STATE_CELLS];
        input[..9].copy_from_slice(&[a, b, a, b, pad, F192::ZERO, F192::ZERO, F192::ZERO, end]);
        let out = permute_cells(&input, false, true);
        let words = |at: usize| -> Vec<F192> { (at..at + STATE_CELLS).map(|i| exec.mem.word(i)).collect() };
        assert_eq!(words(13), out);
        assert_eq!(words(26), permute_cells(&out, true, false));

        let bytes: Vec<u8> = [a, b, a, b]
            .iter()
            .flat_map(|c| [c.c0, c.c1])
            .flat_map(u64::to_le_bytes)
            .collect();
        assert_eq!(
            primitives::hash::digest_of(&state_of_cells(&out, true)),
            primitives::hash::hash(&bytes)
        );

        let (proof, _) = prove(&program, pi, crate::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &pi, &proof).expect("a hand-assembled program verifies");
    }

    /// A state cell carries `(lo, hi, 0)`. This is not an extra AIR constraint: the
    /// memory bus makes a read carrying a literal zero in limb 2 match only such a
    /// stored word.
    #[test]
    fn keccak_requires_zero_third_limb() {
        let err = keccak_program(F192::new(0, 0, 1), F192::ZERO, [F192::ZERO; 4], F192::ZERO)
            .execute([w(7), w(11)])
            .err()
            .expect("the run must fail");
        assert!(matches!(err.fault, Fault::NotCanonical { cell: 0, .. }), "{err}");
    }

    /// The last slot in a frame other than main's is an ordinary slot: the machine halts in the
    /// final STATE, so this program reaches the last slot at `fp = g`, executes the JUMP there,
    /// and halts on landing back in main's frame. Its five rows are exactly the walk the state
    /// bus balances (§sec:state), so the verifier accepts the run the prover proves.
    #[test]
    fn halts_in_the_final_state() {
        let pi = [w(7), w(11)];
        let (last_pc, other_fp) = (F192::from(g_pow(7)), F192::from(g_pow(1)));
        let fill = Op::Xor { a: 0, b: 0, c: 0 };
        // The last slot is reached at `fp = g`, which is not main's, so it runs like any other.
        let program = |last| {
            let code = vec![
                Op::Set { o: 2, k: F192::ONE },   // the jump condition, and main's fp
                Op::Set { o: 3, k: last_pc },     // the last slot's pc
                Op::Set { o: 4, k: other_fp },    // a frame pointer other than main's
                Op::Jump { oc: 2, od: 3, of: 4 }, // -> (g^7, g)
                fill,
                fill,
                fill,
                last, // at fp = g it reads cells 2, 3, 2, so -> (g^7, g^0): the final state
            ];
            Program::from_bytecode(code, 8)
        };

        let jumping = program(Op::Jump { oc: 1, od: 2, of: 1 });
        let exec = jumping.execute(pi).expect("the run halts in the final state");
        assert_eq!(exec.cycles, 5, "three SETs and both JUMPs, the last slot's included");
        assert_eq!(exec.rows(), [0, 0, 3, 0, 2, 0], "XOR, MUL, SET, DEREF, JUMP, KECCAK");
        let (proof, _) = prove(&jumping, pi, crate::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&jumping, &pi, &proof).expect("the verifier accepts the run");

        // With the compiler's SET in the last slot the run has nowhere to go from there, its
        // successor g^8 being no bytecode address.
        let err = program(Op::Set { o: 5, k: F192::ONE })
            .execute(pi)
            .err()
            .expect("the run must fail");
        assert!(matches!(err.fault, Fault::HaltOutsideMain { fp: 1 }), "{err}");
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
        assert_eq!(exec.mem.word(4), x * y, "MUL computes the E product");
    }
}
