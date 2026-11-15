//! The whole program: its run ([`execute`]), its public layout ([`layout_of`]), and [`prove`], which binds the six
//! instruction tables to one commitment through the state, memory and bytecode buses (`doc/leanvm/main.tex`).
//! [`verify`] wraps the `verifier` crate.

use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{self, FillCtx, FlushBuilder, SEP_BYTECODE, SEP_MEM, SEP_STATE};
use crate::witness;
use primitives::field::{F64, F128, g_pow};
use primitives::transcript::ProverState;
use verifier::layout::{
    BYTECODE_FINAL_COUNTERS, GLOBAL_COLUMN_BASES, MEMORY_0, MEMORY_1, MEMORY_FINAL_COUNTERS, NUM_GLOBAL_COLUMNS,
    TABLE_WIDTHS,
};

mod execute;
mod hints;
pub mod layout;
mod trace;
pub use execute::{ExecError, Execution, Fault, Memory, execute};
use isa::Program;
pub use isa::{DerefMode, Op, OutCells, Stats};
pub use layout::*;
pub(crate) use trace::{Drow, Jrow, Krow, Srow, Trace, Xrow};

/// Announce the prover's sizes (`log_mem`, every table's row count, the PCS rate) on the stream, from which the
/// verifier rebuilds the layout ([`layout::table_logs`]). The statement, the program and the public input, is not
/// announced: it seeds the transcript.
fn announce_public(ps: &mut ProverState, log_mem: usize, rows: [usize; tables::N_TABLES], log_inv_rate: usize) {
    ps.add_scalar(F128::new(log_mem as u64, 0));
    for n in rows {
        ps.add_scalar(F128::new(n as u64, 0));
    }
    ps.add_scalar(F128::new(log_inv_rate as u64, 0));
}

pub use verifier::Proof;

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
    /// `2^MIN_STACKED_LOG..=2^MAX_STACKED_LOG` every verifier accepts
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
                pcs::MIN_STACKED_LOG,
                pcs::MAX_STACKED_LOG
            ),
        }
    }
}

impl std::error::Error for ProveError {}

/// The tables' entries in the table sumcheck, in table order: each table's committed columns, its summand (its
/// identities weighted by its own range of `ξ`-powers, each tree's bus form by the tree's power at
/// [`xi_form_base`]), and what the summand sums to, its bus forms' share, as its identities vanish.
fn airs<'a>(
    taus: &[usize; tables::N_TABLES],
    bus: &leaf::BusProof,
    cols: &'a [&'a [F64]],
    xi: F128,
) -> Vec<constraints::Air<'a>> {
    let base = xi_form_base();
    let pows = primitives::field::powers(xi, n_xi_powers());
    let offsets = constraints::xi_offsets(tables::tables().iter().map(|t| t.n_constraints()));
    tables::tables()
        .iter()
        .zip(taus)
        .enumerate()
        .map(|(t, (&table, &tau))| {
            let identities = table.constraint(&pows[offsets[t]..][..table.n_constraints()]);
            let bus_forms = (0..leaf::N_BUS_TREES).map(|s| bus.forms[s][t].scaled(pows[base + s]));
            constraints::Air {
                tau,
                cols: &cols[GLOBAL_COLUMN_BASES[t]..][..TABLE_WIDTHS[t]],
                form: constraints::Form::sum(bus_forms.chain([identities])),
                sigma: (0..leaf::N_BUS_TREES).map(|s| pows[base + s] * bus.sigmas[s][t]).sum(),
            }
        })
        .collect()
}

/// Where the bus forms' `ξ`-powers start: after every table's identities, one power per tree, shared by every table.
/// Shared, the batch's claim is `Σ_s ξ^{base + s}·rem_s`, which the verifier derives from the leaf claims; a power
/// per table would not factor through the trees' totals, and nothing would pin the tables' share of the bus.
pub fn xi_form_base() -> usize {
    tables::tables().iter().map(|t| t.n_constraints()).sum()
}

/// The batch's `ξ`-powers: one per identity, then one per bus tree. Its error is their count less one over `|E|`.
pub fn n_xi_powers() -> usize {
    xi_form_base() + leaf::N_BUS_TREES
}

/// The KECCAK table's claims on its output lanes, which are the Keccak reduction's claim on the permutation's
/// output: the table sumcheck claims every column of the table at one point.
fn keccak_output_claim(table_claims: &[constraints::Claims]) -> keccak_gkr::OutputClaim {
    let claims = &table_claims[tables::KECCAK_TABLE];
    keccak_gkr::OutputClaim {
        instance: claims.chi.clone(),
        lanes: std::array::from_fn(|l| claims.evals[tables::keccakt::V_OUT + l]),
    }
}

/// Prove the program on `public_input` and `witness` ([`execute`]) at the PCS rate `2^-log_inv_rate`: run it, commit
/// its witness, and prove, in transcript order, the bus, the table sumcheck, the public input's binding, the Keccak
/// reduction and the opening. Returns the proof and the run's [`Stats`], or why no proof was made.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(
    program: &Program,
    witness: &[(String, Vec<Vec<F128>>)],
    public_input: [F128; 2],
    log_inv_rate: usize,
) -> Result<(Proof, Stats), ProveError> {
    if !(pcs::MIN_LOG_INV_RATE..=pcs::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(ProveError::InvalidRate { log_inv_rate });
    }
    let exec =
        crate::stage!("Execute program", || execute(program, witness, public_input)).map_err(ProveError::Execution)?;
    // A value read before anything wrote it is the prover's to choose: the proof would be of a weaker statement than
    // the program's.
    if !exec.unconstrained_reads.is_empty() {
        return Err(ProveError::UnconstrainedReads(exec.unconstrained_reads));
    }
    // The layout follows from the run's sizes alone, so a run too large to commit is refused before its witness.
    let log_mem = crate::log2_strict_usize(exec.mem.len());
    let layout = layout_of(
        crate::log2_strict_usize(program.prog.len()),
        log_mem,
        exec.trace.row_counts(),
    );
    if layout.shape.mu > pcs::MAX_STACKED_LOG {
        return Err(ProveError::WitnessOutOfRange {
            log_committed: layout.shape.mu,
        });
    }
    let stats = Stats {
        cycles: exec.cycles,
        rows: layout.rows,
        committed: layout.committed_size(),
        log_mem,
        mem_used: exec.mem_used,
    };
    let mut w = crate::stage!("Build witness", || build(program, &exec, layout));
    drop(exec);

    // The statement, the program's IV and the public input, seeds the transcript; the sizes and the commitment come
    // before any challenge.
    let mut ps = ProverState::new(
        verifier::Digest(program.bytecode().fiat_shamir_iv()).words(),
        verifier::Digest(public_input_bytes(&public_input)).words(),
    );
    announce_public(&mut ps, log_mem, w.layout.rows, log_inv_rate);
    let committed = crate::stage!("Commit", || pcs::commit(&mut ps, &w.q, w.layout.shape, log_inv_rate));

    let (bus, table_claims) = {
        let l = &w.layout;
        let cols = w.columns();
        let bus = crate::stage!("Prove bus", || {
            leaf::prove_balance([&l.push, &l.pull, &l.count], &cols, program.stacked_bytecode(), &mut ps)
        });
        let table_claims = crate::stage!("Prove constraints", || {
            ps.grind(fiat_shamir::grinding_bits(n_xi_powers() as u128 - 1));
            let xi = ps.sample();
            constraints::prove(&airs(&l.taus, &bus, &cols, xi), &bus.point, &mut ps)
        });
        (bus, table_claims)
    };
    // The output lanes' last readers were the bus and the table sumcheck.
    drop(std::mem::take(&mut w.virt));

    // The public input's binding (§sec:e2e-pi) sends nothing: its claims are lines in `r_pi` the verifier evaluates
    // itself, numerator one, so no grind.
    let r_pi = ps.sample();
    let mut slots = finish_claims(&w.layout, bus.claims, &table_claims, r_pi);

    // The Keccak reduction ends on two claims on `q_keccak`, which join the one opening: one ring-switched, one a
    // point claim.
    let witness::Placement { offset, n_vars } = w.layout.placements[QKECCAK];
    let output = keccak_output_claim(&table_claims);
    let openings = crate::stage!("Keccak reduction", || {
        w.keccak_reduction
            .prove(&mut ps, &w.q[offset..][..1 << n_vars], &output)
    });
    let (ring, outputs) = openings.into_pcs_claims(offset);
    slots.extend(outputs);
    crate::stage!("PCS open", || pcs::open(&mut ps, committed, w.q, &slots, &ring));
    Ok((ps.into_proof(), stats))
}

/// Everything the PCS has to open, in the order that feeds the batch's weights:
/// the bus's framework claims, then the table sumcheck's per-table column claims (less the
/// `KECCAK` output lanes', which go to the reduction), then the two public-input limb
/// claims, each located in its committed slot. Every verifier assembles the same list in
/// the same order. The opening needs only each claim's column and point: the values were
/// sent with the claims, or are the verifier's own.
fn finish_claims(
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    table_claims: &[constraints::Claims],
    r_pi: F128,
) -> Vec<pcs::SlotClaim> {
    let bus = bus_claims.into_iter().map(|c| (c.col, c.point));
    let tables = (0..tables::N_TABLES).flat_map(|t| {
        (GLOBAL_COLUMN_BASES[t]..GLOBAL_COLUMN_BASES[t] + TABLE_WIDTHS[t])
            // the Keccak reduction's claim on the output (`keccak_output_claim`)
            .filter(|&col| !matches!(keccak_value(col), Some(KeccakLane::Output(_))))
            .map(move |col| (col, table_claims[t].chi.clone()))
    });
    let pi = pi_point(r_pi, l);
    let pi = [MEMORY_0, MEMORY_1].map(|col| (col, pi.clone()));
    (bus.chain(tables).chain(pi))
        .map(|(col, point)| slot_claim(l, col, point))
        .collect()
}

/// The point of the public-input binding (§sec:e2e-pi): each committed `MEM` limb at
/// `(r, 0,…,0)` must equal the line through that limb of `pi[0]` and `pi[1]`.
/// The public input is the statement, so the verifier evaluates the lines itself;
/// the prover sends nothing.
fn pi_point(r: F128, l: &Layout) -> Vec<F128> {
    let mut point = vec![F128::ZERO; l.placements[MEMORY_0].n_vars];
    point[0] = r;
    point
}

/// A field element in the `verifier` crate's type, and back: the same limbs, no arithmetic.
pub fn to_scalar(value: &F128) -> verifier::E {
    verifier::E::new(value.c0, value.c1)
}

pub fn from_scalar(value: verifier::E) -> F128 {
    F128::new(value.c0, value.c1)
}

/// The statement as the 32 bytes the `verifier` crate takes: the two limbs of each half.
pub fn public_input_bytes(public_input: &[F128; 2]) -> [u8; 32] {
    verifier::Digest::from_halves(to_scalar(&public_input[0]), to_scalar(&public_input[1])).0
}

/// Verify a proof against the public statement (program + public input). The `verifier` crate does it: this only
/// builds its inputs.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(
    program: &Program,
    public_input: &[F128; 2],
    proof: &Proof,
) -> Result<verifier::Summary, verifier::VerifierError> {
    verifier::verify_execution(program.bytecode(), &public_input_bytes(public_input), proof)
}

/// Locate a claim on column `col` at `point`: it lives in the slot at `placements[col].offset`,
/// with the claim's point as the low point.
///
/// The columns `q_keccak` carries are virtual: they have no committed placement. A claim
/// `col(r) = v` on one, at the instance point `r`, is the claim on its slot's `2^|r|` words of
/// `q_keccak`, which folds into the one opening like every other point claim.
fn slot_claim(l: &Layout, col: usize, point: Vec<F128>) -> pcs::SlotClaim {
    let offset = match keccak_value(col) {
        Some(KeccakLane::Slot(slot)) => l.placements[QKECCAK].offset + (slot << point.len()),
        _ => l.placements[col].offset,
    };
    pcs::SlotClaim {
        offset,
        low_point: point,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `SET` of a prover word.
    fn set(o: u32, k: F128) -> Op {
        Op::Set { o, k: to_scalar(&k) }
    }

    /// A K-embedded immediate (extension limb zero).
    fn w(x: u64) -> F128 {
        F128::new(x, 0)
    }

    /// A hand-assembled program: no hints, no debug information, started at `(pc, fp) = (0, 0)`. Straight-line
    /// programs that never change the frame pointer and touch only the first `main_frame` cells need no
    /// allocation. It halts on reaching the final state `(g^{len-1}, g^0)`, the last slot in main's frame
    /// (§sec:state).
    fn from_bytecode(prog: Vec<Op>, main_frame: u32) -> Program {
        Program::from(isa::CompiledProgram {
            prog,
            hints: Default::default(),
            main_frame,
            fn_ranges: Vec::new(),
            src_lines: Vec::new(),
        })
    }

    /// A hand-built straight-line program with two KECCAK rows. The first reads, in the even
    /// layout, two message cells (2, 3) twice as `m`, a four-cell `tail` (4..8), `b8` (8) and a
    /// zero `cap` (9..13), and writes 13..26 in the odd layout; the second reads that output in
    /// the odd layout and writes 26..39 in the even one. Two filler SETs step the pc to 15, whose
    /// slot is the never-executed sentinel.
    fn keccak_program(a: F128, b: F128, tail: [F128; 4], b8: F128) -> Program {
        let mut prog = vec![set(2, a), set(3, b)];
        for (i, &t) in tail.iter().enumerate() {
            prog.push(set(4 + i as u32, t));
        }
        prog.push(set(8, b8));
        for c in 0..4u32 {
            prog.push(set(9 + c, F128::ZERO));
        }
        prog.push(Op::Keccak {
            m: [2, 3, 2, 3],
            tail: 4,
            b8: 8,
            cap: 9,
            out: 13,
            in_odd: false,
            out_odd: true,
            out_cells: OutCells::All,
        });
        prog.push(Op::Keccak {
            m: [13, 14, 15, 16],
            tail: 17,
            b8: 21,
            cap: 22,
            out: 26,
            in_odd: true,
            out_odd: false,
            out_cells: OutCells::All,
        });
        for k in 0..2u32 {
            prog.push(set(39 + k, F128::ONE));
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 16);
        from_bytecode(prog, 64)
    }

    /// Two KECCAK rows over one input that write only part of their output: the first its cell 0 at 13, the
    /// second its cells 0 and 1 at 26. An XOR reads cells 13 and 27 into 40.
    fn partial_keccak_program() -> Program {
        let mut prog = vec![set(2, w(3)), set(3, w(4))];
        for c in 4..13u32 {
            prog.push(set(c, w(u64::from(c))));
        }
        for (out, out_cells) in [(13, OutCells::One), (26, OutCells::Two)] {
            prog.push(Op::Keccak {
                m: [2, 3, 2, 3],
                tail: 4,
                b8: 8,
                cap: 9,
                out,
                in_odd: false,
                out_odd: false,
                out_cells,
            });
        }
        prog.push(Op::Xor { a: 13, b: 27, c: 40 });
        prog.push(set(41, F128::ONE));
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 16);
        from_bytecode(prog, 64)
    }

    /// A KECCAK writes the output cells its bytecode requests and no other, and the proof verifies.
    #[test]
    fn keccak_writes_only_requested_cells() {
        use crate::keccak::permute_cells;
        let program = partial_keccak_program();
        let pi = [w(7), w(11)];
        let exec = execute(&program, &[], pi).unwrap();
        let input = std::array::from_fn(|c| exec.mem.word(if c < 4 { 2 + c % 2 } else { c }));
        let out = permute_cells(&input, false, false);
        assert_eq!(exec.mem.word(13), out[0]);
        assert_eq!([exec.mem.word(26), exec.mem.word(27)], [out[0], out[1]]);
        assert!(
            (14..26).chain(28..39).all(|c| exec.mem.word(c) == F128::ZERO),
            "a cell not requested is not written"
        );
        let (proof, _) = prove(&program, &[], pi, crate::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &pi, &proof).expect("partial outputs verify");
    }

    /// The opcode's execution semantics: the output cells hold the permutation of the lanes the
    /// input cells hold, each side in its layout, the two `m` pairs aliasing one another and
    /// `b8`'s free high limb ignored. With a zero `cap` and the padding in `tail` and `b8`, the
    /// first permutation's first four lanes are the hash of the 64 message bytes. Hand-assembled,
    /// the program is provable all the same: its tables are not powers of two.
    #[test]
    fn keccak_permutes_in_both_layouts() {
        use crate::keccak::{STATE_CELLS, permute_cells, state_of_cells};
        let a = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
        let b = F128::new(0xdead_beef_cafe_babe, 0x0bad_f00d_0bad_f00d);
        let pad = F128::new(primitives::hash::PAD_FIRST as u64, 0);
        let end = F128::new(primitives::hash::END_BIT, 0x5555);
        let program = keccak_program(a, b, [pad, F128::ZERO, F128::ZERO, F128::ZERO], end);
        let pi = [w(7), w(11)];
        let exec = execute(&program, &[], pi).unwrap();

        let mut input = [F128::ZERO; STATE_CELLS];
        input[..9].copy_from_slice(&[a, b, a, b, pad, F128::ZERO, F128::ZERO, F128::ZERO, end]);
        let out = permute_cells(&input, false, true);
        let words = |at: usize| -> Vec<F128> { (at..at + STATE_CELLS).map(|i| exec.mem.word(i)).collect() };
        assert_eq!(words(13), out);
        assert_eq!(words(26), permute_cells(&out, true, false));

        let bytes: Vec<u8> = [a, b, a, b]
            .iter()
            .flat_map(|c| [c.c0, c.c1])
            .flat_map(u64::to_le_bytes)
            .collect();
        assert_eq!(
            primitives::hash::digest_of(&state_of_cells(true, |c| out[c])),
            primitives::hash::hash(&bytes)
        );

        let (proof, _) = prove(&program, &[], pi, crate::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &pi, &proof).expect("a hand-assembled program verifies");
    }

    /// The last slot in a frame other than main's is an ordinary slot: the machine halts in the
    /// final STATE, so this program reaches the last slot at `fp = g`, executes the JUMP there,
    /// and halts on landing back in main's frame. Its five rows are exactly the walk the state
    /// bus balances (§sec:state), so the verifier accepts the run the prover proves.
    #[test]
    fn halts_in_the_final_state() {
        let pi = [w(7), w(11)];
        let (last_pc, other_fp) = (F128::from(g_pow(7)), F128::from(g_pow(1)));
        let fill = Op::Xor { a: 0, b: 0, c: 0 };
        // The last slot is reached at `fp = g`, which is not main's, so it runs like any other.
        let program = |last| {
            let code = vec![
                set(2, F128::ONE),                // the jump condition, and main's fp
                set(3, last_pc),                  // the last slot's pc
                set(4, other_fp),                 // a frame pointer other than main's
                Op::Jump { oc: 2, od: 3, of: 4 }, // -> (g^7, g)
                fill,
                fill,
                fill,
                last, // at fp = g it reads cells 2, 3, 2, so -> (g^7, g^0): the final state
            ];
            from_bytecode(code, 8)
        };

        let jumping = program(Op::Jump { oc: 1, od: 2, of: 1 });
        let exec = execute(&jumping, &[], pi).expect("the run halts in the final state");
        assert_eq!(exec.cycles, 5, "three SETs and both JUMPs, the last slot's included");
        assert_eq!(exec.rows(), [0, 0, 3, 0, 2, 0], "XOR, MUL, SET, DEREF, JUMP, KECCAK");
        let (proof, _) = prove(&jumping, &[], pi, crate::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&jumping, &pi, &proof).expect("the verifier accepts the run");

        // With the compiler's SET in the last slot the run has nowhere to go from there, its
        // successor g^8 being no bytecode address.
        let err = execute(&program(set(5, F128::ONE)), &[], pi)
            .err()
            .expect("the run must fail");
        assert!(matches!(err.fault, Fault::HaltOutsideMain { fp: 1 }), "{err}");
    }

    /// A 128-bit-word MUL: the E-product of two full machine words.
    #[test]
    fn mul_128bit_word() {
        let x = F128::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef);
        let y = F128::new(0x9999_aaaa_bbbb_cccc, 0x1357_9bdf_2468_ace0);
        let prog = vec![
            set(2, x),
            set(3, y),
            Op::Mul { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel (never executed)
        ];
        let program = from_bytecode(prog, 5);
        let pi = [w(1), w(2)];
        let exec = execute(&program, &[], pi).unwrap();
        assert_eq!(exec.mem.word(4), x * y, "MUL computes the E product");
    }
}
