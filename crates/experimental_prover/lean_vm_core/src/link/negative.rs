//! Negative tests: the real prover on a tampered witness, which the verifier must reject, and the changes it must
//! accept. Each tamper runs after the witness is built and before it is committed ([`crate::cpu::prove_tampered`]).

use super::pointer::Chunks;
use super::prove::{Plan, cheat};
use crate::cpu::layout::Witness;
use crate::cpu::{DerefMode, Fault, Op, OutCells, cheat as execute_cheat, execute, prove_tampered, to_scalar, verify};
use crate::tables;
use isa::Program;
use primitives::field::{F64, F128, g_pow};
use verifier::VerifierError;
use verifier::layout::{
    OP_DEREF as DEREF, OP_JUMP as JUMP, OP_KECCAK as KECCAK_TABLE, OP_MUL as MUL, OP_SET as SET, OP_XOR as XOR,
};

/// Loop iterations, and `XOR` asserts per iteration: enough cycles that the pointer width (the cycle count's bits)
/// exceeds both the memory's and the program's, so pointers past memory and past the program exist.
const ITERATIONS: usize = 14;
const ASSERTS: usize = 12;
/// Where the loop's code starts, and its first frame.
const LOOP_PC: usize = 30;
const FIRST_FRAME: usize = 48;
const PROGRAM_LEN: usize = 64;

fn w(x: u64) -> F128 {
    F128::new(x, 0)
}

fn gw(k: usize) -> F128 {
    F128::from(g_pow(k))
}

/// `SET` of a prover word.
fn set(o: u32, k: F128) -> Op {
    Op::Set { o, k: to_scalar(&k) }
}

/// A hand-assembled program with a main frame of 32 cells.
fn assemble(prog: Vec<Op>) -> Program {
    Program::from(isa::CompiledProgram {
        prog,
        hints: Default::default(),
        main_frame: 32,
        fn_ranges: Vec::new(),
        src_lines: Vec::new(),
    })
}

/// A program with a row in every table. Main sets up a Keccak permutation, a `DEREF`, a `MUL` and an `XOR` of zeros
/// (rows 0 of their tables), then runs a loop of `ITERATIONS + 1` iterations, one frame of eight cells each: frame
/// cells 0 to 5 hold `g^fp`, `g^8`, the condition `c_k = g^k + g^n`, the loop's pc, `K = g^n + g^{n+1}` and `g`,
/// and each iteration writes the next frame's from its own, then asserts `ASSERTS` times. The condition reaches zero
/// at `k = n`, where the loop falls through to a `JUMP` to the final state.
fn program() -> Program {
    let n = ITERATIONS;
    let k_const = gw(n) + gw(n + 1);
    let mut prog = vec![set(2, w(3)), set(3, w(4))];
    for c in 4..13u32 {
        let k = if c < 9 { w(u64::from(c)) } else { F128::ZERO };
        prog.push(set(c, k));
    }
    prog.push(Op::Keccak {
        m: [2, 3, 2, 3],
        tail: 4,
        b8: 8,
        cap: 9,
        out: 13,
        in_odd: false,
        out_odd: false,
        out_cells: OutCells::One,
    });
    prog.extend([
        set(25, F128::ZERO),
        Op::Mul { a: 25, b: 25, c: 26 },
        Op::Xor { a: 25, b: 25, c: 27 },
        set(14, gw(20)),
        set(21, w(9)),
        Op::Deref {
            o1: 14,
            o2: 1,
            o3: 15,
            mode: DerefMode::Cell,
        },
        Op::Mul { a: 2, b: 3, c: 16 },
        Op::Xor { a: 13, b: 16, c: 17 },
    ]);
    let frame = FIRST_FRAME as u32;
    for (k, o) in [gw(FIRST_FRAME), gw(8), gw(0) + gw(n), gw(LOOP_PC), k_const, gw(1)]
        .into_iter()
        .zip(0..)
    {
        prog.push(set(frame + o, k));
    }
    prog.extend([
        set(22, F128::ONE),
        set(23, gw(LOOP_PC)),
        set(24, gw(FIRST_FRAME)),
        Op::Jump { oc: 22, od: 23, of: 24 },
    ]);
    assert_eq!(prog.len(), LOOP_PC);
    prog.extend([
        Op::Mul { a: 0, b: 1, c: 8 },
        set(9, gw(8)),
        set(11, gw(LOOP_PC)),
        set(12, k_const),
        set(13, gw(1)),
        Op::Mul { a: 2, b: 5, c: 6 },
        Op::Xor { a: 6, b: 4, c: 10 },
        Op::Xor { a: 1, b: 1, c: 7 },
    ]);
    prog.extend((0..ASSERTS).map(|_| Op::Xor { a: 1, b: 1, c: 7 }));
    prog.push(Op::Jump { oc: 2, od: 3, of: 8 });
    prog.extend([
        set(16, F128::ONE),
        set(17, gw(PROGRAM_LEN - 1)),
        Op::Jump { oc: 16, od: 17, of: 16 },
    ]);
    prog.resize(PROGRAM_LEN, Op::Xor { a: 0, b: 0, c: 0 });
    assemble(prog)
}

const PI: [F128; 2] = [F128::new(7, 0), F128::new(11, 0)];

/// A pointer column's words, or any column's values, in the witness.
fn column(w: &mut Witness, t: usize, c: usize) -> &mut [F64] {
    w.column_mut(tables::GLOBAL_COLUMN_BASES[t] + c)
}

fn plan(t: usize) -> Plan {
    Plan::of(tables::tables()[t])
}

fn chunks(w: &Witness) -> Chunks {
    Chunks::new(w.layout.pointer_width)
}

/// Prove with `tamper` applied, and verify.
/// The loop program's verdict with `tamper`, which may set the link's cheats, cleared after.
fn outcome(tamper: impl FnOnce(&mut Witness)) -> Result<(), VerifierError> {
    let verdict = cheated_outcome(&program(), PI, None, tamper);
    cheat::INDEX_WORD.set(None);
    cheat::MEMORY_TERM.set(F128::ZERO);
    verdict
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
                width > w.log_mem && 1 << width > PROGRAM_LEN,
                "width {width}, memory 2^{}",
                w.log_mem
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
        let (chunks, log_mem) = (chunks(w), w.log_mem);
        let pointer = plan(KECCAK_TABLE)
            .pointers
            .into_iter()
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

#[test]
fn a_wrong_memory_term_is_rejected() {
    rejected(|_| cheat::MEMORY_TERM.set(F128::ONE));
}

/// A `KECCAK` in main's frame with its `tail` at `tail`, its capacity at `cap` and its output at `out`: whether the run
/// faults on a block across its window, and the verdict on a proof of it run anyway.
fn keccak_at(tail: u32, cap: u32, out: u32, out_cells: OutCells) -> (Option<Fault>, Result<(), VerifierError>) {
    let mut prog = vec![set(2, w(3)), set(3, w(4))];
    prog.extend((tail..tail + 4).map(|c| set(c, w(u64::from(c)))));
    prog.push(set(8, w(8)));
    prog.extend((cap..cap + 4).map(|c| set(c, F128::ZERO)));
    prog.push(Op::Keccak {
        m: [2, 3, 2, 3],
        tail,
        b8: 8,
        cap,
        out,
        in_odd: false,
        out_odd: false,
        out_cells,
    });
    // Sixteen instructions, a power of two.
    prog.push(set(31, F128::ZERO));
    prog.resize(16, Op::Xor { a: 31, b: 31, c: 31 });
    let program = assemble(prog);
    let fault = execute(&program, &[], PI).err().map(|e| e.fault);
    let verdict = cheated_outcome(&program, PI, Some(&execute_cheat::KECCAK_ACROSS_WINDOW), |_| {});
    (fault, verdict)
}

/// Each `KECCAK` block, its `tail`, its capacity and its thirteen output cells, in one window verifies. Across the
/// boundary at 16 the run faults; let through, the cells past it leave their pointer's window, so they drop out of the
/// scattered accesses while their rows still weigh the presence coefficient, and the memory link fails.
#[test]
fn a_keccak_block_across_its_window_is_rejected() {
    for (tail, cap, out, out_cells, across) in [
        (4, 12, 20, OutCells::One, None),
        (4, 14, 20, OutCells::One, Some((14, 4))),
        (4, 9, 20, OutCells::One, None),
        (14, 9, 20, OutCells::One, Some((14, 4))),
        (4, 9, 16, OutCells::All, None),
        (4, 9, 13, OutCells::All, Some((13, 13))),
    ] {
        let (fault, verdict) = keccak_at(tail, cap, out, out_cells);
        let case = format!("tail {tail}, cap {cap}, out {out}");
        match across {
            None => assert_eq!((fault, verdict), (None, Ok(())), "{case}"),
            Some((cell, cells)) => {
                assert_eq!(fault, Some(Fault::KeccakAcrossWindow { cell, cells }), "{case}");
                assert_eq!(verdict, Err(VerifierError::LinkTerminal), "{case}");
            }
        }
    }
}

/// A straight-line program whose `XOR` and `MUL` tables have the same height, all in main's frame.
fn equal_heights() -> Program {
    let mut prog = vec![set(25, F128::ZERO)];
    prog.extend((0..3).map(|_| Op::Mul { a: 25, b: 25, c: 26 }));
    prog.extend((0..4).map(|_| Op::Xor { a: 25, b: 25, c: 27 }));
    assemble(prog)
}

/// Row 0 of `XOR` and row 0 of `MUL`, tables of the same height in the same frame, swap their cycles: each claims
/// the other's cycle, pc and instruction. A row's state and successor follow from its pc, so the state link's arrays
/// `A` and `B` are exactly the honest ones, and only the opcode term, under each table's weight `θ_F`, tells the rows
/// apart.
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
    let program = assemble(vec![
        set(2, F128::ZERO),
        Op::Jump { oc: 2, od: 0, of: 1 },
        set(3, F128::ZERO),
        set(4, F128::ZERO),
    ]);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let pi = [F128::new(7, 5), PI[1]];
    assert!(execute(&program, &[], pi).is_err());
    let cheat = Some(&execute_cheat::UNTAKEN_JUMP_WORDS_UNCHECKED);
    assert_eq!(
        cheated_outcome(&program, pi, cheat, |_| {}),
        Err(VerifierError::LinkTerminal)
    );
}

/// The first `JUMP` row's successor set to its destination and frame, as a taken jump's.
fn commit_jump_as_taken(w: &mut Witness) {
    use tables::jump::{FP_NEXT, PC_NEXT, V_FP, V_PC};
    for (next, word) in [(PC_NEXT, V_PC), (FP_NEXT, V_FP)] {
        let word = column(w, JUMP, word)[0];
        column(w, JUMP, next)[0] = word;
    }
}

/// One `JUMP` on the condition `cond`, to pc `dest` with frame `g^0`.
fn one_jump(cond: F128, dest: usize) -> Program {
    assemble(vec![
        set(2, cond),
        set(3, gw(dest)),
        set(4, gw(0)),
        Op::Jump { oc: 2, od: 3, of: 4 },
        set(5, F128::ZERO),
        set(6, F128::ZERO),
        set(7, F128::ZERO),
        set(8, F128::ZERO),
    ])
}

/// An untaken jump (`b = 0`) that goes to its destination anyway and commits it as its successor: memory and the
/// state link agree, and only the successor's identity catches it.
#[test]
fn an_untaken_jump_that_jumps_is_rejected() {
    let program = one_jump(F128::ZERO, 5);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let cheat = Some(&execute_cheat::EVERY_JUMP_TAKEN);
    assert_eq!(
        cheated_outcome(&program, PI, cheat, commit_jump_as_taken),
        Err(VerifierError::LinkTerminal)
    );
}

/// An untaken jump to `g·pc` with frame `fp`, its taken flag `b` set: memory, the state link and the successor's
/// identities agree, and only `b + cond·w` catches it.
#[test]
fn a_taken_flag_on_a_zero_condition_is_rejected() {
    let program = one_jump(F128::ZERO, 4);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let tamper = |w: &mut Witness| column(w, JUMP, tables::jump::B)[0] = F64::ONE;
    assert_eq!(
        cheated_outcome(&program, PI, None, tamper),
        Err(VerifierError::LinkTerminal)
    );
}

/// A taken jump to `g·pc` with frame `fp`, its flag `b` and inverse `w` zeroed: `b + cond·w`, the state link and the
/// successor's identities agree, and only `cond·(b + 1)` catches it.
#[test]
fn a_zero_flag_on_a_nonzero_condition_is_rejected() {
    let program = one_jump(F128::ONE, 4);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let tamper = |w: &mut Witness| {
        column(w, JUMP, tables::jump::B)[0] = F64::ZERO;
        column(w, JUMP, tables::jump::W)[0] = F64::ZERO;
    };
    assert_eq!(
        cheated_outcome(&program, PI, None, tamper),
        Err(VerifierError::LinkTerminal)
    );
}

/// An untaken jump to `g·pc` that moves to the frame `g^8` anyway and commits it as its successor's frame, then, in
/// that frame, a taken jump to the final state: memory, the state link and the pc's identity agree, and only the
/// frame's identity `fp' + b·v_fp + (b + 1)·fp` catches it.
#[test]
fn an_untaken_jump_that_changes_frame_is_rejected() {
    let program = assemble(vec![
        set(2, F128::ZERO),
        set(3, gw(4)),
        set(4, gw(8)),
        Op::Jump { oc: 2, od: 3, of: 4 },
        set(5, F128::ONE),
        set(6, gw(7)),
        set(7, gw(0)),
        Op::Jump { oc: 5, od: 6, of: 7 },
    ]);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let cheat = Some(&execute_cheat::EVERY_JUMP_TAKEN);
    assert_eq!(
        cheated_outcome(&program, PI, cheat, commit_jump_as_taken),
        Err(VerifierError::LinkTerminal)
    );
}

/// A run copied sixteen instructions on, whose rows all claim the copy's pcs: every row's instruction, memory
/// accesses, successor and the final state agree, and only the start, `ŝ_init` at cycle 0, catches it.
#[test]
fn a_run_that_starts_elsewhere_is_rejected() {
    let run = [
        set(2, F128::ONE),
        set(3, gw(31)),
        set(4, gw(0)),
        Op::Jump { oc: 2, od: 3, of: 4 },
    ];
    let mut prog = run.to_vec();
    prog.resize(16, Op::Xor { a: 0, b: 0, c: 0 });
    prog.extend(run);
    prog.resize(32, Op::Xor { a: 0, b: 0, c: 0 });
    let program = assemble(prog);
    assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()));
    let tamper = |w: &mut Witness| {
        let chunks = chunks(w);
        for t in [SET, JUMP] {
            let links = plan(t).links;
            for row in 0..w.layout.rows[t] {
                let pc = chunks
                    .decode(column(w, t, links.bytecode.pointer)[row].0)
                    .expect("one-hot")
                    + 16;
                column(w, t, links.state.pc)[row] = g_pow(pc);
                column(w, t, links.bytecode.pointer)[row] = F64(chunks.encode(pc));
            }
        }
    };
    assert_eq!(
        cheated_outcome(&program, PI, None, tamper),
        Err(VerifierError::LinkTerminal)
    );
}

/// A main frame's prologue: a `KECCAK` inside its window, an untaken `JUMP`, and cell 25 zero for the filler.
fn prologue() -> Vec<Op> {
    let mut prog = vec![set(2, w(3)), set(3, w(4))];
    prog.extend((4..9u32).map(|c| set(c, w(u64::from(c)))));
    prog.extend((12..16u32).map(|c| set(c, F128::ZERO)));
    prog.push(Op::Keccak {
        m: [2, 3, 2, 3],
        tail: 4,
        b8: 8,
        cap: 12,
        out: 16,
        in_odd: false,
        out_odd: false,
        out_cells: OutCells::One,
    });
    prog.extend([
        set(22, F128::ZERO),
        set(23, w(5)),
        set(24, w(6)),
        Op::Jump { oc: 22, od: 23, of: 24 },
        set(25, F128::ZERO),
    ]);
    prog
}

/// Straight-line programs of `2^m` instructions, some skipping one by a taken `JUMP`, whose `XOR`, `MUL` and `SET`
/// heights and cycle count sit at and around powers of two, prove and verify.
#[test]
fn heights_around_powers_of_two_verify() {
    for log_len in [5usize, 6, 7, 8, 10, 12] {
        let len = 1usize << log_len;
        for (mix, skip) in [(0usize, false), (1, false), (2, true), (3, true), (4, false)] {
            let mut prog = prologue();
            if skip {
                let to = prog.len() + 5;
                prog.extend([
                    set(28, F128::ONE),
                    set(29, gw(to)),
                    set(30, gw(0)),
                    Op::Jump { oc: 28, od: 29, of: 30 },
                    Op::Xor { a: 25, b: 25, c: 26 },
                ]);
            }
            let rest = len - prog.len();
            prog.extend((0..rest).map(|i| match mix {
                1 => Op::Mul { a: 25, b: 25, c: 27 },
                3 if i <= rest / 2 => Op::Mul { a: 25, b: 25, c: 27 },
                4 if i % 3 == 0 => set(31, F128::ZERO),
                2 if i % 2 == 1 => set(31, F128::ZERO),
                _ => Op::Xor { a: 25, b: 25, c: 26 },
            }));
            let program = assemble(prog);
            let exec = execute(&program, &[], PI).expect("the program runs");
            let rows = exec.rows();
            assert_eq!(
                cheated_outcome(&program, PI, None, |_| {}),
                Ok(()),
                "len {len}, mix {mix}, rows {rows:?}"
            );
        }
    }
}

/// Table heights of exactly `2^m - 1`, `2^m` and `2^m + 1`, the run ending by a jump to the last pc, prove and verify.
#[test]
fn exact_heights_around_powers_of_two_verify() {
    for m in [1usize, 2, 3, 4, 5, 8, 11] {
        for h in [(1 << m) - 1, 1 << m, (1 << m) + 1] {
            for (xors, muls, sets) in [
                (h, 0, 0),
                (0, h, 1),
                (h, h, 2),
                (h, 3, (1usize << m).saturating_sub(16)),
            ] {
                let mut prog = prologue();
                prog.extend((0..xors).map(|_| Op::Xor { a: 25, b: 25, c: 26 }));
                prog.extend((0..muls).map(|_| Op::Mul { a: 25, b: 25, c: 27 }));
                prog.extend((0..sets).map(|_| set(31, F128::ZERO)));
                let len = (prog.len() + 4).next_power_of_two();
                prog.extend([
                    set(28, F128::ONE),
                    set(29, gw(len - 1)),
                    set(30, gw(0)),
                    Op::Jump { oc: 28, od: 29, of: 30 },
                ]);
                prog.resize(len, Op::Xor { a: 0, b: 0, c: 0 });
                let program = assemble(prog);
                let rows = execute(&program, &[], PI).expect("the program runs").rows();
                assert_eq!(cheated_outcome(&program, PI, None, |_| {}), Ok(()), "rows {rows:?}");
            }
        }
    }
}
