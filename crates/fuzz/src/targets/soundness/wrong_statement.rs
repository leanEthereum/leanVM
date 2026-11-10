//! `soundness-wrong-statement`: a proof is of one statement, the bytecode and the public input. An honest proof is
//! checked against another public input and against a bytecode one instruction away; and a prover is handed a
//! `Program` whose `prog` was edited after assembly, so it executes one bytecode while its transcript is seeded with
//! (and its bus reads) the other's IV and public columns: its proof must verify against neither program. The rate
//! is announced inside the proof, not passed to `verify`: lies about it are `soundness-transcript-tamper`'s.

use super::fixtures::{self, Fixture};
use crate::mutate_proof::perturb;
use crate::{Ctx, Finding, Outcome, Source, catch};
use leanvm_core::cpu::{DerefMode, Op, OutCells, Program};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let Some((fixture, rate, honest)) = fixtures::draw(src)? else {
        return Ok(());
    };
    let context = format!("soundness-wrong-statement {}", fixture.name);
    let detail = |what: &str| format!("program {}, rate {rate}, {what}", fixture.name);
    match src.below(3) {
        0 => {
            let mut other = fixture.public_input;
            let i = src.below(2);
            other[i] = perturb(other[i], src);
            if src.chance(1, 4) {
                other.swap(0, 1);
            }
            if other == fixture.public_input {
                return Ok(());
            }
            let has_top = other.iter().any(|h| h.c2 != 0);
            ctx.note(if has_top {
                "public input with a top limb"
            } else {
                "other public input"
            });
            let verdict = catch(|| leanvm_core::cpu::verify(&fixture.program, &other, &honest.proof))
                .map_err(|(m, l)| Finding::panic(&m, &l).in_context(&context))?;
            super::must_reject(
                ctx,
                verdict,
                format!("{context}: a proof verifies for another public input"),
                || detail(&format!("proven {:?}, accepted {other:?}", fixture.public_input)),
            )
        }
        1 => {
            let Some((program, what)) = edited(fixture, src, false) else {
                return Ok(());
            };
            ctx.note(format!("other bytecode {what}"));
            let verdict = catch(|| leanvm_core::cpu::verify(&program, &fixture.public_input, &honest.proof))
                .map_err(|(m, l)| Finding::panic(&m, &l).in_context(&context))?;
            super::must_reject(
                ctx,
                verdict,
                format!("soundness-wrong-statement: a proof verifies for another bytecode ({what})"),
                || detail(&what),
            )
        }
        _ => {
            // The executed instruction is what the stale IV hides: one never run leaves the run, and so the proof, the
            // original program's.
            let Some((stale, what)) = edited(fixture, src, true) else {
                return Ok(());
            };
            let proved = catch(|| leanvm_core::cpu::prove(&stale, fixture.public_input, rate));
            let proof = match proved {
                Ok(Ok((proof, _))) => proof,
                Ok(Err(e)) => {
                    ctx.note(format!(
                        "stale IV {what}: prover refused {}",
                        crate::programs::prove_error_kind(&e)
                    ));
                    return Ok(());
                }
                Err(_) => {
                    ctx.note(format!("stale IV {what}: prover panicked"));
                    return Ok(());
                }
            };
            ctx.note(format!("stale IV {what} proved"));
            for (program, against) in [
                (&fixture.program, "the assembled bytecode"),
                (&stale, "the executed bytecode"),
            ] {
                let verdict = catch(|| leanvm_core::cpu::verify(program, &fixture.public_input, &proof))
                    .map_err(|(m, l)| Finding::panic(&m, &l).in_context(&context))?;
                super::must_reject(
                    ctx,
                    verdict,
                    format!("soundness-wrong-statement: a stale-IV proof verifies against {against} ({what})"),
                    || detail(&what),
                )?;
            }
            Ok(())
        }
    }
}

/// `fixture`'s program with one instruction changed (an executed one when `executed`), or two swapped, and the kind
/// of change. The IV and the public columns stay the assembled program's ([`tamper::replace_bytecode`]), as a
/// malicious prover's would.
fn edited(fixture: &Fixture, src: &mut Source, executed: bool) -> Option<(Program, String)> {
    let mut prog = fixture.program.prog().to_vec();
    let prog = &mut prog;
    let pcs: Vec<usize> = if executed {
        fixture.executed().to_vec()
    } else {
        (0..prog.len()).collect()
    };
    if pcs.is_empty() {
        return None;
    }
    let pc = pcs[src.below(pcs.len())];
    let what = if src.chance(1, 8) && pcs.len() > 1 {
        let other = pcs[src.below(pcs.len())];
        prog.swap(pc, other);
        "swap".to_string()
    } else {
        let what = edit_op(&mut prog[pc], src);
        format!("{}/{what}", op_name(&prog[pc]))
    };
    let changed = format!("{:?}", prog) != format!("{:?}", fixture.program.prog());
    let mut program = fixture.program.clone();
    leanvm_core::cpu::tamper::replace_bytecode(&mut program, std::mem::take(prog));
    changed.then_some((program, what))
}

fn op_name(op: &Op) -> &'static str {
    match op {
        Op::Xor { .. } => "XOR",
        Op::Mul { .. } => "MUL",
        Op::Set { .. } => "SET",
        Op::Deref { .. } => "DEREF",
        Op::Jump { .. } => "JUMP",
        Op::Keccak { .. } => "KECCAK",
    }
}

/// An offset a step away, or on an edge.
fn offset(o: u32, src: &mut Source) -> u32 {
    match src.below(4) {
        0 => o.wrapping_add(1),
        1 => o.wrapping_sub(1),
        2 => o ^ (1 << src.below(8)),
        _ => src.below(64) as u32,
    }
}

/// Change one field of `op`, naming it.
fn edit_op(op: &mut Op, src: &mut Source) -> &'static str {
    match op {
        Op::Xor { a, b, c } | Op::Mul { a, b, c } => match src.below(5) {
            0 => {
                *a = offset(*a, src);
                "a"
            }
            1 => {
                *b = offset(*b, src);
                "b"
            }
            2 => {
                *c = offset(*c, src);
                "c"
            }
            3 => {
                std::mem::swap(a, c);
                "swap-a-c"
            }
            _ => {
                let (a, b, c) = (*a, *b, *c);
                *op = if matches!(op, Op::Xor { .. }) {
                    Op::Mul { a, b, c }
                } else {
                    Op::Xor { a, b, c }
                };
                "opcode"
            }
        },
        Op::Set { o, k } => {
            if src.bool() {
                *o = offset(*o, src);
                "o"
            } else {
                *k = perturb(*k, src);
                "k"
            }
        }
        Op::Deref { o1, o2, o3, mode } => match src.below(4) {
            0 => {
                *o1 = offset(*o1, src);
                "o1"
            }
            1 => {
                *o2 = offset(*o2, src);
                "o2"
            }
            2 => {
                *o3 = offset(*o3, src);
                "o3"
            }
            _ => {
                *mode = match (*mode, src.bool()) {
                    (DerefMode::Cell, true) | (DerefMode::Fp, false) => DerefMode::Pc,
                    (DerefMode::Cell, false) | (DerefMode::Pc, true) => DerefMode::Fp,
                    _ => DerefMode::Cell,
                };
                "mode"
            }
        },
        Op::Jump { oc, od, of } => match src.below(3) {
            0 => {
                *oc = offset(*oc, src);
                "oc"
            }
            1 => {
                *od = offset(*od, src);
                "od"
            }
            _ => {
                *of = offset(*of, src);
                "of"
            }
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
        } => match src.below(7) {
            0 => {
                let i = src.below(4);
                m[i] = offset(m[i], src);
                "m"
            }
            1 => {
                *tail = offset(*tail, src);
                "tail"
            }
            2 => {
                *b8 = offset(*b8, src);
                "b8"
            }
            3 => {
                *cap = offset(*cap, src);
                "cap"
            }
            4 => {
                *out = offset(*out, src);
                "out"
            }
            5 => {
                if src.bool() {
                    *in_odd = !*in_odd;
                } else {
                    *out_odd = !*out_odd;
                }
                "layout"
            }
            _ => {
                *out_cells = match (*out_cells, src.bool()) {
                    (OutCells::One, true) | (OutCells::All, false) => OutCells::Two,
                    (OutCells::One, false) | (OutCells::Two, true) => OutCells::All,
                    _ => OutCells::One,
                };
                "out-cells"
            }
        },
    }
}
