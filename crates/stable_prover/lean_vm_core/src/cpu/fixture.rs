//! Hand-assembled programs for the tests.

use super::{DerefMode, Op, OutCells, to_scalar};
use isa::Program;
use primitives::field::{F128, g_pow};

/// Loop iterations of [`looping_program`]: enough cycles that the pointer width (the cycle count's bits) exceeds
/// both the memory's and the program's, so pointers past memory and past the program exist.
pub const ITERATIONS: usize = 14;
/// Where [`looping_program`]'s loop code starts, its first frame, and its length.
pub const LOOP_PC: usize = 30;
pub const FIRST_FRAME: usize = 48;
pub const PROGRAM_LEN: usize = 64;

/// A K-embedded immediate (extension limb zero).
pub fn w(x: u64) -> F128 {
    F128::new(x, 0)
}

pub fn gw(k: usize) -> F128 {
    F128::from(g_pow(k))
}

/// `SET` of a prover word.
pub fn set(o: u32, k: F128) -> Op {
    Op::Set { o, k: to_scalar(&k) }
}

/// A hand-assembled program: no hints, no debug information, started at `(pc, fp) = (0, 0)`. It halts on reaching
/// the final state `(g^{len-1}, g^0)`, the last slot in main's frame (§sec:state).
pub fn assemble(prog: Vec<Op>, main_frame: u32) -> Program {
    Program::from(isa::CompiledProgram {
        prog,
        hints: Default::default(),
        main_frame,
        fn_ranges: Vec::new(),
        src_lines: Vec::new(),
    })
}

/// A program with a row in every table. Main sets up a Keccak permutation writing one output cell, a `DEREF`, a
/// `MUL` and an `XOR` of zeros (rows 0 of their tables), then runs a loop of `ITERATIONS + 1` iterations, one frame
/// of eight cells each: frame cells 0 to 5 hold `g^fp`, `g^8`, the condition `c_k = g^k + g^n`, the loop's pc,
/// `K = g^n + g^{n+1}` and `g`, and each iteration writes the next frame's from its own, then asserts `asserts`
/// times. The condition reaches zero at `k = n`, where the loop falls through to a `JUMP` to the final state.
pub fn looping_program(asserts: usize) -> Program {
    let n = ITERATIONS;
    let k_const = gw(n) + gw(n + 1);
    let mut prog = vec![set(2, w(3)), set(3, w(4))];
    for c in 4..13u32 {
        prog.push(set(c, if c < 9 { w(u64::from(c)) } else { F128::ZERO }));
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
    let cells = [gw(FIRST_FRAME), gw(8), gw(0) + gw(n), gw(LOOP_PC), k_const, gw(1)];
    prog.extend(cells.into_iter().zip(0..).map(|(k, o)| set(frame + o, k)));
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
    ]);
    prog.extend((0..asserts).map(|_| Op::Xor { a: 1, b: 1, c: 7 }));
    prog.push(Op::Jump { oc: 2, od: 3, of: 8 });
    prog.extend([
        set(16, F128::ONE),
        set(17, gw(PROGRAM_LEN - 1)),
        Op::Jump { oc: 16, od: 17, of: 16 },
    ]);
    prog.resize(PROGRAM_LEN, Op::Xor { a: 0, b: 0, c: 0 });
    assemble(prog, 32)
}
