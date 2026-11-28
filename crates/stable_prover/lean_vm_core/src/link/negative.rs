//! Negative tests: the real prover on a tampered witness, which the verifier must reject, and the two tampers it must
//! accept. Each tamper runs after the witness is built and before it is committed ([`crate::cpu::prove_tampered`]).

use super::pointer::Chunks;
use super::prove::{Plan, cheat};
use crate::cpu::fixture::{LOOP_PC, PROGRAM_LEN, assemble, gw, looping_program, set, w};
use crate::cpu::layout::Witness;
use crate::cpu::{ALLOW_CROSSING, Fault, Op, OutCells, cheat as execute_cheat, execute, prove_tampered, verify};
use crate::tables::{self, GLOBAL_COLUMN_BASES};
use isa::Program;
use primitives::field::{F64, F128, g_pow};
use verifier::VerifierError;
use verifier::layout::{
    MEMORY_0, OP_DEREF as DEREF, OP_JUMP as JUMP, OP_KECCAK as KECCAK_TABLE, OP_MUL as MUL, OP_SET as SET,
    OP_XOR as XOR,
};

/// `XOR` asserts per iteration of the loop.
const ASSERTS: usize = 13;

fn program() -> Program {
    looping_program(ASSERTS)
}

const PI: [F128; 2] = [F128::new(7, 0), F128::new(11, 0)];

/// A pointer column's words, or any column's values, in the witness.
fn column(w: &mut Witness, t: usize, c: usize) -> &mut [F64] {
    w.column_mut(GLOBAL_COLUMN_BASES[t] + c)
}

/// The memory's log size.
fn log_mem(w: &Witness) -> usize {
    w.layout.placements[MEMORY_0].n_vars
}

fn plan(t: usize) -> Plan {
    Plan::of(tables::tables()[t])
}

fn chunks(w: &Witness) -> Chunks {
    Chunks::new(w.layout.pointer_width)
}

/// Prove with `tamper` applied, and verify.
fn outcome(tamper: impl FnOnce(&mut Witness)) -> Result<(), VerifierError> {
    let program = program();
    let tamper = |w: &mut Witness| {
        tamper(w);
        w.write_edits();
    };
    let (proof, _) = prove_tampered(&program, &[], PI, crate::pcs::TEST_LOG_INV_RATE, tamper).expect("the prover runs");
    cheat::INDEX_WORD.set(None);
    cheat::MEMORY_TERM.set(F128::ZERO);
    verify(&program, &PI, &proof).map(|_| ())
}

fn rejected(tamper: impl FnOnce(&mut Witness)) {
    assert_eq!(outcome(tamper), Err(VerifierError::LinkTerminal));
}

/// The bit of another value of chunk `i` than the one `word` holds there.
fn other_bit(chunks: &Chunks, word: u64, i: usize) -> u64 {
    let shift: usize = (0..i).map(|i| 1 << chunks.widths[i]).sum();
    let current = chunks.bits(word, i).trailing_zeros() as usize;
    1 << (shift + (current + 1) % (1 << chunks.widths[i]))
}

/// The honest run's shape: the pointer width exceeds the memory's and the program's, and every table has a row.
#[test]
fn honest_proof_verifies() {
    let exec = execute(&program(), &[], PI).expect("the program runs");
    assert!(exec.rows().iter().all(|&n| n > 0), "{:?}", exec.rows());
    assert_eq!(
        outcome(|w| {
            let width = w.layout.pointer_width;
            assert!(
                width > log_mem(w) && 1 << width > PROGRAM_LEN,
                "width {width}, memory 2^{}",
                log_mem(w)
            );
            assert!(chunks(w).d() > 1);
        }),
        Ok(())
    );
}

#[test]
fn a_chunk_with_two_ones_is_rejected() {
    rejected(|w| {
        let (chunks, cycle) = (chunks(w), plan(SET).links.state.cycle);
        let word = &mut column(w, SET, cycle)[0];
        *word = F64(word.0 | other_bit(&chunks, word.0, 0));
    });
}

#[test]
fn a_chunk_with_no_ones_is_rejected() {
    rejected(|w| {
        let (chunks, pointer) = (chunks(w), plan(SET).links.memory[0].pointer);
        let word = &mut column(w, SET, pointer)[0];
        *word = F64(word.0 & !(chunks.bits(word.0, 1) << (1 << chunks.widths[0])));
    });
}

#[test]
fn swapped_cycle_pointers_are_rejected() {
    rejected(|w| column(w, SET, plan(SET).links.state.cycle).swap(0, 1));
}

#[test]
fn a_duplicate_cycle_pointer_is_rejected() {
    rejected(|w| {
        let cycle = column(w, SET, plan(SET).links.state.cycle);
        cycle[1] = cycle[0];
    });
}

/// A `DEREF` row's value column changed, with the memory as it was.
#[test]
fn a_changed_value_is_rejected() {
    rejected(|w| {
        let value = plan(DEREF)
            .links
            .memory
            .iter()
            .find_map(|a| a.value.coeffs.iter().position(|c| !c.is_zero()))
            .expect("a DEREF access reads a value column");
        let cell = &mut column(w, DEREF, value)[0];
        *cell += F64::ONE;
    });
}

/// The `SET` that writes cap cell 10 pointed at cell 11, which holds the same zero.
#[test]
fn a_read_of_another_cell_with_the_same_value_is_rejected() {
    rejected(|w| {
        let (chunks, pointer) = (chunks(w), plan(SET).links.memory[0].pointer);
        let words = column(w, SET, pointer);
        let row = words
            .iter()
            .position(|v| chunks.decode(v.0) == Some(10))
            .expect("a SET writes cell 10");
        words[row] = F64(chunks.encode(11));
    });
}

/// The mirror test binds executed rows only: two ones in an executed row's chunk are rejected, in a padding row's
/// accepted, since a padding row takes part in no link.
#[test]
fn a_non_one_hot_pointer_counts_on_executed_rows_only() {
    let tamper = |row: fn(&Witness) -> usize| {
        move |w: &mut Witness| {
            let (chunks, row, pointer) = (chunks(w), row(w), plan(SET).links.memory[0].pointer);
            let word = &mut column(w, SET, pointer)[row];
            *word = F64(word.0 | other_bit(&chunks, word.0, 0));
        }
    };
    let executed = |w: &Witness| w.layout.rows[SET] - 1;
    let padding = |w: &Witness| {
        assert!(w.layout.rows[SET] < 1 << w.layout.taus[SET], "SET has padding rows");
        w.layout.rows[SET]
    };
    assert_eq!(outcome(tamper(executed)), Err(VerifierError::LinkTerminal));
    assert_eq!(outcome(tamper(padding)), Ok(()));
}

/// A padding row keeps pointer 0 and carries any payload.
#[test]
fn a_padding_row_with_any_payload_is_accepted() {
    assert_eq!(
        outcome(|w| {
            let row = w.layout.rows[SET];
            let plan = plan(SET);
            for &c in &plan.values {
                column(w, SET, c)[row] += F64(5);
            }
        }),
        Ok(())
    );
}

/// Rows 0 of `XOR` and `MUL` both combine two zeros, so swapped whole they still agree with memory; only the opcode
/// each table's program read carries differs, and with one weight shared by both tables those two errors would cancel.
#[test]
fn an_xor_and_mul_row_swapped_are_rejected() {
    rejected(|w| {
        for c in 0..tables::tables()[XOR].n_committed_columns() {
            let (x, m) = (column(w, XOR, c)[0], column(w, MUL, c)[0]);
            column(w, XOR, c)[0] = m;
            column(w, MUL, c)[0] = x;
        }
    });
}

/// Row 0 of `XOR` reads cell 25 twice: both pointers take the same extra one.
#[test]
fn two_pointers_of_a_row_with_the_same_non_one_hot_chunk_are_rejected() {
    rejected(|w| {
        let chunks = chunks(w);
        let accesses = plan(XOR).links.memory;
        let extra = other_bit(&chunks, column(w, XOR, accesses[0].pointer)[0].0, 0);
        for access in &accesses[..2] {
            let word = &mut column(w, XOR, access.pointer)[0];
            assert_eq!(chunks.decode(word.0), Some(25));
            *word = F64(word.0 | extra);
        }
    });
}

/// An executed pointer with an extra one, while the index side scatters the honest word, as a prover would that
/// kept the index side's arrays honest and hoped the row side would not notice.
#[test]
fn a_non_one_hot_pointer_with_honest_index_arrays_is_rejected() {
    rejected(|w| {
        let (chunks, pointer) = (chunks(w), plan(SET).links.memory[0].pointer);
        let word = &mut column(w, SET, pointer)[0];
        cheat::INDEX_WORD.set(Some((SET, pointer, 0, word.0)));
        *word = F64(word.0 | other_bit(&chunks, word.0, 0));
    });
}

/// A row's bytecode pointer moved past the program, into the zero padding below `2^W`.
#[test]
fn a_bytecode_pointer_past_the_program_is_rejected() {
    rejected(|w| {
        let (chunks, pointer) = (chunks(w), plan(SET).links.bytecode.pointer);
        let word = &mut column(w, SET, pointer)[0];
        let pc = chunks.decode(word.0).expect("one-hot");
        *word = F64(chunks.encode(pc + PROGRAM_LEN));
    });
}

/// The `KECCAK` row's write of output cell 13 moved past memory, into the zero padding below `2^W`.
#[test]
fn a_keccak_pointer_past_memory_is_rejected() {
    rejected(|w| {
        let (chunks, log_mem) = (chunks(w), log_mem(w));
        let pointer = (plan(KECCAK_TABLE).links.pointers().iter().copied())
            .find(|&c| chunks.decode(column(w, KECCAK_TABLE, c)[0].0) == Some(13))
            .expect("KECCAK writes cell 13");
        let word = &mut column(w, KECCAK_TABLE, pointer)[0];
        *word = F64(chunks.encode(13 + (1 << log_mem)));
    });
}

/// The loop's asserts: `XOR` of frame cell 1 with itself into cell 7, the same instruction at each of these pcs.
const ASSERT_PCS: std::ops::Range<usize> = LOOP_PC + 7..LOOP_PC + 8 + ASSERTS;

/// The first `XOR` row that runs the assert at `pc`.
fn assert_row(w: &mut Witness, pc: usize) -> usize {
    let (chunks, pointer) = (chunks(w), plan(XOR).links.bytecode.pointer);
    let words = column(w, XOR, pointer);
    words
        .iter()
        .position(|v| chunks.decode(v.0) == Some(pc))
        .expect("an XOR row runs the assert")
}

/// An assert's pointer for operand `a` names frame cell 9 rather than 1. Cell 9 is the next frame's cell 1, written
/// earlier in the iteration with the same `g^8`, so the row agrees with memory; only the address the program gives
/// for operand `a`, `fp·g^1`, is wrong.
#[test]
fn a_wrong_instruction_is_rejected() {
    rejected(|w| {
        let (chunks, links) = (chunks(w), plan(XOR).links);
        let row = assert_row(w, ASSERT_PCS.start);
        let word = &mut column(w, XOR, links.memory[0].pointer)[row];
        let cell = chunks.decode(word.0).expect("one-hot");
        let memory = execute(&program(), &[], PI).expect("the program runs").mem;
        assert_eq!(memory.word(cell + 8), memory.word(cell));
        *word = F64(chunks.encode(cell + 8));
    });
}

/// An assert row claims the pc of the next assert, the same instruction: its program read and its memory accesses
/// agree, but the state it starts from is not the successor its predecessor produced, and the successor it produces
/// is not the state the next row starts from.
#[test]
fn a_wrong_successor_state_is_rejected() {
    rejected(|w| {
        let (chunks, links) = (chunks(w), plan(XOR).links);
        let pc = ASSERT_PCS.start + 1;
        let row = assert_row(w, pc);
        assert_eq!(links.bytecode.pc, links.state.pc);
        column(w, XOR, links.state.pc)[row] = g_pow(pc + 1);
        column(w, XOR, links.bytecode.pointer)[row] = F64(chunks.encode(pc + 1));
    });
}

/// The last `SET` row claims the cycle just past the run, so its own cycle is missing from the cycle pointers and the
/// cycle past the run, which only the final state may claim, is claimed twice.
#[test]
fn a_missing_cycle_is_rejected() {
    rejected(|w| {
        let (chunks, cycle) = (chunks(w), plan(SET).links.state.cycle);
        let cycles: usize = w.layout.rows.iter().sum();
        assert!(cycles < 1 << chunks.width, "the cycle past the run has a pointer");
        let row = w.layout.rows[SET] - 1;
        column(w, SET, cycle)[row] = F64(chunks.encode(cycles));
    });
}

/// The last `SET` row claims the top cycle `2^W - 1`, whose successor the state identity drops (`eq(ζ, j + 1)` is
/// zero there): its own cycle is missing and the top cycle has a row, which the cycle count forbids.
#[test]
fn a_cycle_pointer_at_the_top_of_the_index_is_rejected() {
    rejected(|w| {
        let (chunks, cycle) = (chunks(w), plan(SET).links.state.cycle);
        let cycles: usize = w.layout.rows.iter().sum();
        let top = (1 << chunks.width) - 1;
        assert!(cycles < top, "the top cycle lies past the run's final one");
        let row = w.layout.rows[SET] - 1;
        column(w, SET, cycle)[row] = F64(chunks.encode(top));
    });
}

#[test]
fn a_wrong_memory_term_is_rejected() {
    rejected(|_| cheat::MEMORY_TERM.set(F128::ONE));
}

/// A `KECCAK` whose capacity is cells `cap` to `cap + 3` of main's frame, run honestly: in one window it verifies.
/// Across the boundary at 16 the run faults; let through, the reads past it leave their pointer's window, so they drop
/// out of the scattered accesses while their rows still weigh the presence coefficient, and the memory link fails.
#[test]
fn a_keccak_block_across_its_window_is_rejected() {
    let run = |cap: u32| {
        let mut prog = vec![set(2, w(3)), set(3, w(4))];
        prog.extend((4..9u32).map(|c| set(c, w(u64::from(c)))));
        prog.extend((cap..cap + 4).map(|c| set(c, F128::ZERO)));
        prog.push(Op::Keccak {
            m: [2, 3, 2, 3],
            tail: 4,
            b8: 8,
            cap,
            out: 20,
            in_odd: false,
            out_odd: false,
            out_cells: OutCells::One,
        });
        // Sixteen instructions, a power of two.
        prog.extend((24..28u32).map(|c| set(c, F128::ZERO)));
        let program = assemble(prog, 32);
        let fault = execute(&program, &[], PI).err().map(|e| e.fault);
        let across = matches!(fault, Some(Fault::KeccakAcrossWindow { cell, cells: 4 }) if cell == cap);
        assert_eq!((across, fault.is_none()), (cap % 16 > 12, cap % 16 <= 12));
        ALLOW_CROSSING.set(true);
        let proof = prove_tampered(&program, &[], PI, crate::pcs::TEST_LOG_INV_RATE, |w| w.write_edits());
        ALLOW_CROSSING.set(false);
        verify(&program, &PI, &proof.expect("the prover runs").0).map(|_| ())
    };
    assert_eq!(run(12), Ok(()));
    assert_eq!(run(14), Err(VerifierError::LinkTerminal));
}

/// A straight-line program whose `XOR` and `MUL` tables have the same height, all in main's frame.
fn equal_heights() -> Program {
    let mut prog = vec![set(25, F128::ZERO)];
    prog.extend((0..3).map(|_| Op::Mul { a: 25, b: 25, c: 26 }));
    prog.extend((0..4).map(|_| Op::Xor { a: 25, b: 25, c: 27 }));
    assemble(prog, 32)
}

/// Row 0 of `XOR` and row 0 of `MUL`, tables of the same height in the same frame, swap their cycles: each claims
/// the other's cycle and pc. The state and bytecode payloads are linear, so the swapped pair's sum equals the honest
/// pair's, and only a row weight that differs between the two tables tells the rows apart.
#[test]
fn rows_of_two_tables_at_the_same_index_with_swapped_cycles_are_rejected() {
    let program = equal_heights();
    let tamper = |w: &mut Witness| {
        assert_eq!(w.layout.taus[XOR], w.layout.taus[MUL], "{:?}", w.layout.taus);
        let (x, m) = (plan(XOR).links, plan(MUL).links);
        let fp = column(w, XOR, x.state.fp)[0];
        assert_eq!(fp, column(w, MUL, m.state.fp)[0]);
        for (cx, cm) in [
            (x.state.cycle, m.state.cycle),
            (x.state.pc, m.state.pc),
            (x.bytecode.pointer, m.bytecode.pointer),
        ] {
            let (a, b) = (column(w, XOR, cx)[0], column(w, MUL, cm)[0]);
            column(w, XOR, cx)[0] = b;
            column(w, MUL, cm)[0] = a;
        }
    };
    let tamper = |w: &mut Witness| {
        tamper(w);
        w.write_edits();
    };
    let (proof, _) = prove_tampered(&program, &[], PI, crate::pcs::TEST_LOG_INV_RATE, tamper).expect("the prover runs");
    assert_eq!(
        verify(&program, &PI, &proof).map(|_| ()),
        Err(VerifierError::LinkTerminal)
    );
}

/// Prove `program` with the executor's `cheat`, if any, on and `tamper` applied, and verify.
fn cheated_outcome(
    program: &Program,
    pi: [F128; 2],
    cheat: Option<&'static std::thread::LocalKey<std::cell::Cell<bool>>>,
    tamper: impl FnOnce(&mut Witness),
) -> Result<(), VerifierError> {
    let tamper = |w: &mut Witness| {
        tamper(w);
        w.write_edits();
    };
    cheat.inspect(|c| c.set(true));
    let proved = prove_tampered(program, &[], pi, crate::pcs::TEST_LOG_INV_RATE, tamper);
    cheat.inspect(|c| c.set(false));
    let (proof, _) = proved.expect("the prover runs");
    verify(program, &pi, &proof).map(|_| ())
}

/// `assert_in_k(m[0], m[1])`, an untaken `JUMP` on a zero cell to cell 0 with frame cell 1, of a public input whose
/// cell 0 is outside `K`: the executor faults, and a prover that steps past the fault is rejected.
#[test]
fn assert_in_k_of_a_non_k_word_is_rejected() {
    let program = assemble(
        vec![
            set(2, F128::ZERO),
            Op::Jump { oc: 2, od: 0, of: 1 },
            set(3, F128::ZERO),
            set(4, F128::ZERO),
        ],
        32,
    );
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let pi = [F128::new(7, 5), PI[1]];
    assert!(execute(&program, &[], pi).is_err());
    let cheat = Some(&execute_cheat::UNTAKEN_JUMP_WORDS_UNCHECKED);
    assert_eq!(
        cheated_outcome(&program, pi, cheat, |_| {}),
        Err(VerifierError::LinkTerminal)
    );
}

/// One `JUMP` on a zero condition, to pc `dest` with frame `g^0`.
fn one_jump(dest: usize) -> Program {
    assemble(
        vec![
            set(2, F128::ZERO),
            set(3, gw(dest)),
            set(4, gw(0)),
            Op::Jump { oc: 2, od: 3, of: 4 },
            set(5, F128::ZERO),
            set(6, F128::ZERO),
            set(7, F128::ZERO),
            set(8, F128::ZERO),
        ],
        32,
    )
}

/// An untaken jump (`b = 0`) that goes to its destination anyway and commits it as its successor: memory and the
/// state link agree, and only the successor's identity catches it.
#[test]
fn an_untaken_jump_that_jumps_is_rejected() {
    let program = one_jump(5);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let tamper = |w: &mut Witness| {
        let column_of = |name| tables::column(JUMP, name);
        for (next, word) in [("pc_next", "v_pc"), ("fp_next", "v_fp")].map(|(a, b)| (column_of(a), column_of(b))) {
            let word = column(w, JUMP, word)[0];
            column(w, JUMP, next)[0] = word;
        }
    };
    let cheat = Some(&execute_cheat::EVERY_JUMP_TAKEN);
    assert_eq!(
        cheated_outcome(&program, PI, cheat, tamper),
        Err(VerifierError::LinkTerminal)
    );
}

/// An untaken jump to `g·pc` with frame `fp`, its taken flag `b` set: memory, the state link and the successor's
/// identities agree, and only `b + cond·w` catches it.
#[test]
fn a_taken_flag_on_a_zero_condition_is_rejected() {
    let program = one_jump(4);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let tamper = |w: &mut Witness| column(w, JUMP, tables::column(JUMP, "b"))[0] = F64::ONE;
    assert_eq!(
        cheated_outcome(&program, PI, None, tamper),
        Err(VerifierError::LinkTerminal)
    );
}
