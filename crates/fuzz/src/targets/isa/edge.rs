//! `isa-edge`: programs whose shape sits on a boundary.

use super::program::{Builder, Exit, garbage};
use super::random::public_input;
use crate::{Ctx, Finding, Outcome, Source, catch};
use leanvm_core::cpu::{DerefMode, Op, OutCells, Program};
use primitives::field::{F128, g_pow};
use std::collections::HashMap;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(16) {
        0..=2 => exact(src, ctx),
        3..=6 => table_rows(src, ctx),
        7 => halt_elsewhere(src, ctx),
        8 if src.chance(1, 8) => self_loop(src, ctx),
        9 | 10 => big_operands(src, ctx),
        11 => tiny_frames(src, ctx),
        12 => odd_lengths(src, ctx),
        _ => exact(src, ctx),
    }
}

/// Bytecode of exactly `2^k` slots whose code runs into the last one before the halt slot, `k` from 0 (the halt slot
/// alone: a run of no instruction) up.
fn exact(src: &mut Source, ctx: &Ctx) -> Outcome {
    let k = src.below(10);
    let len = 1usize << k;
    ctx.note(format!("exact 2^{k}"));
    let pi = public_input(src);
    let mut b = Builder::new(pi);
    while b.main.code.len() + 30 < len {
        b.main.step(src);
    }
    let halt = if src.bool() {
        Op::Xor { a: 0, b: 0, c: 0 }
    } else {
        garbage(src)
    };
    let built = b.finish(src, len, halt);
    if built.prog.len() != len {
        return Ok(());
    }
    super::check(&built.program(64), pi, Some(&built), src, ctx, "isa-edge exact")
}

/// Exactly `n` rows of one table, `n` at and around a power of two, the other tables nearly empty.
fn table_rows(src: &mut Source, ctx: &Ctx) -> Outcome {
    let k = src.below(11);
    let n = ((1usize << k) + src.below(3))
        .saturating_sub(1)
        .max(if src.bool() { 0 } else { 1 });
    let table = src.below(6);
    ctx.note(format!("rows table {table} 2^{}", k.min(10)));
    let pi = public_input(src);
    let w = |x: u64| F128::new(x, 0);
    let mut prog = vec![Op::Set { o: 2, k: w(3) }, Op::Set { o: 3, k: w(5) }];
    let mut next = 4u32;
    let mut fresh = |n: u32| {
        let c = next;
        next += n;
        c
    };
    match table {
        0 | 1 => {
            for _ in 0..n {
                let c = fresh(1);
                let (a, bb) = (2 + src.below(2) as u32, 2 + src.below(2) as u32);
                prog.push(if table == 0 {
                    Op::Xor { a, b: bb, c }
                } else {
                    Op::Mul { a, b: bb, c }
                });
            }
        }
        2 => {
            for _ in 0..n {
                prog.push(Op::Set {
                    o: fresh(1),
                    k: src.f128(),
                });
            }
        }
        3 => {
            // DEREF copies through one pointer to cell 0: a2 = 2 + j reads cells 2 and 3, a3 fresh.
            prog.push(Op::Set {
                o: 1000,
                k: F128::from(g_pow(0)),
            });
            for _ in 0..n {
                let mode = *src.pick(&[DerefMode::Cell, DerefMode::Cell, DerefMode::Fp]);
                let o3 = fresh(1);
                let o2 = if mode == DerefMode::Cell {
                    2 + src.below(2) as u32
                } else {
                    fresh(1)
                };
                prog.push(Op::Deref { o1: 1000, o2, o3, mode });
                if mode == DerefMode::Fp {
                    // `o3` is only counted, never written: give it a value so nothing reads it unwritten later.
                    prog.push(Op::Set { o: o3, k: F128::ZERO });
                }
            }
        }
        4 => {
            // Untaken jumps over the same three cells.
            prog.push(Op::Set { o: 1000, k: F128::ZERO });
            for _ in 0..n {
                prog.push(Op::Jump { oc: 1000, od: 2, of: 3 });
            }
        }
        _ => {
            // KECCAK rows over one input block, each to its own output.
            let n = n.min(300);
            let block = fresh(13);
            for c in 0..13 {
                prog.push(Op::Set {
                    o: block + c,
                    k: F128::new(src.u64(), src.u64()),
                });
            }
            for _ in 0..n {
                let out = fresh(13);
                prog.push(Op::Keccak {
                    m: [block, block + 1, block + 2, block + 3],
                    tail: block + 4,
                    b8: block + 8,
                    cap: block + 9,
                    out,
                    in_odd: src.bool(),
                    out_odd: src.bool(),
                    out_cells: *src.pick(&[OutCells::One, OutCells::Two, OutCells::All]),
                });
            }
        }
    }
    let len = (prog.len() + 1).next_power_of_two();
    while prog.len() < len - 1 {
        prog.push(Op::Set {
            o: fresh(1),
            k: F128::ONE,
        });
    }
    prog.push(Op::Xor { a: 0, b: 0, c: 0 });
    let program = Program::assemble(prog, HashMap::new(), 64);
    super::check(&program, pi, None, src, ctx, "isa-edge rows")
}

/// A callee that jumps to the halt slot: in its own frame (refused, `HaltOutsideMain`, unless the halt slot jumps
/// away) or in main's (the machine halts).
fn halt_elsewhere(src: &mut Source, ctx: &Ctx) -> Outcome {
    let pi = public_input(src);
    let mut b = Builder::new(pi);
    for _ in 0..src.below(4) {
        b.main.step(src);
    }
    let exit = if src.bool() { Exit::HaltHere } else { Exit::HaltMain };
    ctx.note(format!("halt from callee {exit:?}"));
    let body = src.below(4);
    b.call(src, 1 << 12, body, exit);
    let halt = if src.chance(3, 4) {
        Op::Xor { a: 0, b: 0, c: 0 }
    } else {
        garbage(src)
    };
    let built = b.finish(src, 1, halt);
    super::check(&built.program(64), pi, Some(&built), src, ctx, "isa-edge halt")
}

/// A jump to itself: the run stops at the step limit with an error, after a bounded time.
fn self_loop(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("self loop");
    let w = |x: u64| F128::new(x, 0);
    let prog = vec![
        Op::Set { o: 2, k: w(1) },
        Op::Set {
            o: 3,
            k: F128::from(g_pow(3)),
        },
        Op::Set { o: 4, k: w(1) },
        Op::Jump { oc: 2, od: 3, of: 4 },
    ];
    let mut prog = prog;
    prog.push(Op::Xor { a: 0, b: 0, c: 0 });
    while !prog.len().is_power_of_two() {
        prog.insert(prog.len() - 1, garbage(src));
    }
    let program = Program::assemble(prog, HashMap::new(), 8);
    let run = catch(|| program.execute([F128::ZERO; 2]))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("isa-edge loop"))?;
    match run {
        Err(e) if matches!(e.fault, leanvm_core::cpu::Fault::StepLimit) => Ok(()),
        other => Err(Finding::high(
            "isa-edge loop: a self-loop did not stop at the step limit",
            format!("{:?}", other.map(|e| e.cycles).map_err(|e| e.to_string())),
        )),
    }
}

/// Operands near `u32::MAX`, in main's frame and in a callee's, where a frame offset added to the frame pointer or a
/// pointer's base can overflow: the interpreter must refuse with an error, not wrap or panic.
fn big_operands(src: &mut Source, ctx: &Ctx) -> Outcome {
    let near = |src: &mut Source| u32::MAX - src.below(20) as u32;
    let pi = public_input(src);
    let mut b = Builder::new(pi);
    b.main.step(src);
    let w = |x: u64| F128::new(x, 0);
    let what = src.below(5);
    let op = match what {
        // A KECCAK whose consecutive input cells run past u32::MAX, in main's frame.
        0 => Op::Keccak {
            m: [0, 0, 0, 0],
            tail: u32::MAX - src.below(3) as u32,
            b8: 0,
            cap: 0,
            out: 2,
            in_odd: false,
            out_odd: false,
            out_cells: OutCells::One,
        },
        // A DEREF whose pointer base plus offset runs past u32::MAX.
        1 => {
            let p = b.main.fresh(1);
            // A base of at least 20, so base + offset always passes u32::MAX.
            b.main.code.push(Op::Set {
                o: p,
                k: F128::from(g_pow(src.range(20, 100))),
            });
            Op::Deref {
                o1: p,
                o2: near(src),
                o3: 0,
                mode: *src.pick(&[DerefMode::Cell, DerefMode::Fp, DerefMode::Pc]),
            }
        }
        // In a callee's frame, fp + offset past u32::MAX.
        _ => {
            let base = 1 << 12;
            let (cond, target, ptr) = (b.main.fresh(1), b.main.fresh(1), b.main.fresh(1));
            let at = b.main.code.len() + 4;
            b.main.code.push(Op::Set { o: cond, k: w(1) });
            b.main.code.push(Op::Set {
                o: target,
                k: F128::from(g_pow(at)),
            });
            b.main.code.push(Op::Set {
                o: ptr,
                k: F128::from(g_pow(base)),
            });
            b.main.code.push(Op::Jump {
                oc: cond,
                od: target,
                of: ptr,
            });
            // Now at `at`, in frame `base`.
            match what {
                2 => Op::Set { o: near(src), k: w(7) },
                3 => Op::Xor {
                    a: near(src),
                    b: 0,
                    c: 1,
                },
                _ => Op::Jump {
                    oc: near(src),
                    od: 0,
                    of: 0,
                },
            }
        }
    };
    ctx.note(format!("big operand {what}"));
    b.main.code.push(op);
    b.main.broken = true;
    let built = b.finish(src, 1, Op::Xor { a: 0, b: 0, c: 0 });
    let program = built.program(64);
    let run = catch(|| program.execute(pi)).map_err(|(m, l)| Finding::panic(&m, &l).in_context("isa-edge operands"))?;
    if let Ok(exec) = run {
        return Err(Finding::medium(
            "isa-edge operands: an address past u32::MAX did not fail the run",
            format!(
                "operand case {what}: ran {} cycles over {} cells",
                exec.cycles,
                exec.mem.len()
            ),
        ));
    }
    Ok(())
}

/// `main_frame` of 0, 1 and 2: the public input cells exist whatever the frame says.
fn tiny_frames(src: &mut Source, ctx: &Ctx) -> Outcome {
    let main_frame = src.below(3) as u32;
    ctx.note(format!("main frame {main_frame}"));
    let pi = public_input(src);
    let mut b = Builder::new(pi);
    for _ in 0..src.below(6) {
        b.main.step(src);
    }
    let built = b.finish(src, 1, Op::Xor { a: 0, b: 0, c: 0 });
    super::check(&built.program(main_frame), pi, Some(&built), src, ctx, "isa-edge frame")
}

/// Bytecode whose length is no power of two, or empty: `Program::assemble` refuses it with its documented panic, and
/// no program of such a length exists to run, prove or verify.
fn odd_lengths(src: &mut Source, ctx: &Ctx) -> Outcome {
    let len = *src.pick(&[0usize, 3, 5, 6, 7, 9, 12]);
    ctx.note(format!("length {len}"));
    let mut prog: Vec<Op> = (1..len)
        .map(|i| Op::Set {
            o: 2 + i as u32,
            k: F128::ONE,
        })
        .collect();
    if len > 0 {
        prog.push(Op::Xor { a: 0, b: 0, c: 0 });
    }
    match catch(|| Program::assemble(prog, HashMap::new(), 8)) {
        Err((message, _)) if message.contains("must be a power of two long") => Ok(()),
        Err((message, location)) => {
            Err(Finding::panic(&message, &location).in_context("Program::assemble of a non-power-of-two bytecode"))
        }
        Ok(_) => Err(Finding::high(
            "Program::assemble accepted a bytecode whose length is no power of two",
            format!("length {len}"),
        )),
    }
}
