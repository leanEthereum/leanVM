//! The `isa` group: hand-assembled bytecode straight into the VM, bypassing the compiler.
//!
//! The oracle for a program: `execute` returns an `ExecError` or a run, never panics; a run whose every read was of a
//! written cell proves, and its proof verifies (completeness, High); the proof verifies for no other public input and
//! for no program with one instruction changed (Critical); and when the generator built the program, the run's memory
//! holds the values the generator computed by itself.

use crate::programs::{self, fault_kind, prove_honest};
use crate::{Cost, Ctx, Finding, Outcome, Source, Target, catch};
use leanvm_core::cpu::{DerefMode, Op, OutCells, Program, ProveError};
use primitives::field::F192;

mod edge;
pub mod program;
mod random;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "isa-random",
        about: "generated straight-line, jumping, calling and KECCAK programs: no panic, memory as the generator computed, honest runs prove, proofs bind the input and every instruction",
        cost: Cost::Medium,
        run: random::run,
    },
    &Target {
        name: "isa-edge",
        about: "bytecode at the edges: exact power-of-two lengths, table rows at powers of two, halting from another frame, self-loops, operands at u32::MAX, tiny main frames, non-power-of-two lengths",
        cost: Cost::Medium,
        run: edge::run,
    },
];

/// Runs with more memory or more steps than this are executed but not proven: a case stays seconds.
const PROVE_MAX_LOG_MEM: usize = 20;
const PROVE_MAX_CYCLES: usize = 1 << 16;

/// The whole oracle on one program. `built`, when the generator made it, also checks the run's memory.
pub fn check(
    program: &Program,
    public_input: [F192; 2],
    built: Option<&program::Built>,
    src: &mut Source,
    ctx: &Ctx,
    context: &str,
) -> Outcome {
    let run = catch(|| program.execute(public_input)).map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))?;
    let exec = match run {
        Err(e) => {
            ctx.note(format!("fault {}", fault_kind(&e.fault)));
            if built.is_some_and(|b| !b.broken) {
                return Err(Finding::high(
                    format!("{context}: a program the generator ran fails: {}", fault_kind(&e.fault)),
                    format!("{e}"),
                ));
            }
            return Ok(());
        }
        Ok(exec) => exec,
    };
    ctx.note("ran");
    if let Some(b) = built {
        if b.broken {
            // The mistake sat on a path the run never took (after a callee halted the machine, say).
            ctx.note("mistake not reached");
        } else if exec.unconstrained_reads.is_empty() {
            b.check_memory(&exec.mem, context)?;
        }
    }
    if exec.mem.len() > 1 << PROVE_MAX_LOG_MEM || exec.cycles > PROVE_MAX_CYCLES {
        ctx.note("too large to prove");
        return Ok(());
    }
    let rate = programs::log_inv_rate(src);
    if !exec.unconstrained_reads.is_empty() {
        drop(exec);
        let refused = catch(|| leanvm_core::cpu::prove(program, public_input, rate))
            .map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))?;
        return match refused {
            Err(ProveError::UnconstrainedReads(_)) => {
                ctx.note("refused unconstrained reads");
                Ok(())
            }
            other => Err(Finding::high(
                format!("{context}: a run that read unwritten cells was not refused"),
                format!("{:?}", other.err()),
            )),
        };
    }
    drop(exec);
    let proof = catch(|| prove_honest(program, public_input, rate, context))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))??;
    let Some(proof) = proof else {
        ctx.note("witness out of range");
        return Ok(());
    };
    ctx.note("proved");

    // Another public input.
    let mut other = public_input;
    let i = src.below(2);
    other[i] = crate::mutate_proof::perturb(other[i], src);
    other[i].c2 = 0;
    if other != public_input && leanvm_core::cpu::verify(program, &other, &proof).is_ok() {
        return Err(Finding::critical(
            format!("{context}: a proof verifies for another public input"),
            format!("proven {public_input:?}, accepted {other:?}"),
        ));
    }

    // Another program: one instruction changed, the halt slot included.
    let mut prog = program.prog().to_vec();
    let at = if src.chance(1, 4) {
        prog.len() - 1
    } else {
        src.below(prog.len())
    };
    prog[at] = change(prog[at], src);
    let before = leanvm_core::cpu::layout::bytecode_table(program.prog());
    if leanvm_core::cpu::layout::bytecode_table(&prog) != before {
        let changed = Program::assemble(prog, Default::default(), 0);
        let verdict = catch(|| leanvm_core::cpu::verify(&changed, &public_input, &proof))
            .map_err(|(m, l)| Finding::panic(&m, &l).in_context(context))?;
        if verdict.is_ok() {
            return Err(Finding::critical(
                format!("{context}: a proof verifies for a program with one instruction changed"),
                format!(
                    "slot {at} of {}: {:?} became {:?}",
                    program.prog().len(),
                    program.prog()[at],
                    changed.prog()[at]
                ),
            ));
        }
        ctx.note("bound to its program");
    }
    Ok(())
}

/// One instruction changed a little: an operand, a flag, an immediate, the opcode.
pub fn change(op: Op, src: &mut Source) -> Op {
    let bump = |x: u32, src: &mut Source| match src.below(3) {
        0 => x.wrapping_add(1),
        1 => x ^ 1 << src.below(32),
        _ => src.below(64) as u32,
    };
    match op {
        Op::Xor { a, b, c } if src.bool() => Op::Mul { a, b, c },
        Op::Mul { a, b, c } if src.bool() => Op::Xor { a, b, c },
        Op::Xor { a, b, c } => Op::Xor { a, b: bump(b, src), c },
        Op::Mul { a, b, c } => Op::Mul { a: bump(a, src), b, c },
        Op::Set { o, k } => {
            if src.bool() {
                Op::Set {
                    o,
                    k: crate::mutate_proof::perturb(k, src),
                }
            } else {
                Op::Set { o: bump(o, src), k }
            }
        }
        Op::Deref { o1, o2, o3, mode } => match src.below(3) {
            0 => Op::Deref {
                o1,
                o2,
                o3,
                mode: match mode {
                    DerefMode::Cell => DerefMode::Pc,
                    DerefMode::Pc => DerefMode::Fp,
                    DerefMode::Fp => DerefMode::Cell,
                },
            },
            1 => Op::Deref {
                o1,
                o2: bump(o2, src),
                o3,
                mode,
            },
            _ => Op::Deref {
                o1,
                o2,
                o3: bump(o3, src),
                mode,
            },
        },
        Op::Jump { oc, od, of } => Op::Jump {
            oc,
            od: bump(od, src),
            of,
        },
        Op::Keccak {
            m,
            tail,
            b8,
            cap,
            out,
            in_odd,
            out_odd,
            out_cells,
        } => {
            let mut k = (m, tail, b8, cap, out, in_odd, out_odd, out_cells);
            match src.below(6) {
                0 => k.5 = !in_odd,
                1 => k.6 = !out_odd,
                2 => {
                    k.7 = match out_cells {
                        OutCells::One => OutCells::Two,
                        OutCells::Two => OutCells::All,
                        OutCells::All => OutCells::One,
                    }
                }
                3 => k.0[src.below(4)] = bump(m[0], src),
                4 => k.1 = bump(tail, src),
                _ => k.4 = bump(out, src),
            }
            Op::Keccak {
                m: k.0,
                tail: k.1,
                b8: k.2,
                cap: k.3,
                out: k.4,
                in_odd: k.5,
                out_odd: k.6,
                out_cells: k.7,
            }
        }
    }
}
