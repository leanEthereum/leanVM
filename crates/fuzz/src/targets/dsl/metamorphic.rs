//! `dsl-metamorphic`: one generated program in two spellings (`print::Style`: inlined or called, unrolled or
//! looped, a value moved through a `StackBuf`, a `HeapBuf`, a list or a function return, constants folded or
//! computed, `x * 1`, `x + 0`, other names and indentation) must publish the same public input, and compiling a
//! source twice must give the same bytecode.

use super::generate::{bucket, compile};
use super::print::{self, Style};
use super::synth::{self, Limits};
use crate::{Ctx, Finding, Outcome, Source};
use leanvm_core::cpu::Program;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let mut lim = Limits::for_depth(src, ctx.depth.min(1));
    lim.budget = lim.budget.min(60);
    let g = synth::generate(src, lim);
    let a_style = if src.bool() {
        Style::plain()
    } else {
        Style::random(&mut src.rng())
    };
    let b_style = Style::random(&mut src.rng());
    let a = print::print(&g.prog, &a_style, src.u64());
    let b = print::print(&g.prog, &b_style, src.u64());
    ctx.note(format!("spelling {}", b_style.knobs()));
    let context = "dsl-metamorphic";
    let pa = compile(&a, &g, context)?;
    let pb = compile(&b, &g, context)?;
    // The bytecode digest leads the transcript: a source must compile to one program.
    for (source, program) in [(&a, &pa), (&b, &pb)] {
        let again = compile(source, &g, context)?;
        if fingerprint(program) != fingerprint(&again) {
            return Err(Finding::high(
                format!("{context}: one source compiles to two programs"),
                source.to_string(),
            ));
        }
    }
    let ra = pa.execute(g.public_input);
    let rb = pb.execute(g.public_input);
    match (ra, rb) {
        (Ok(ea), Ok(eb)) => {
            ctx.note(format!(
                "both ran, {} and {} cycles",
                bucket(ea.cycles),
                bucket(eb.cycles)
            ));
            Ok(())
        }
        (Ok(_), Err(e)) | (Err(e), Ok(_)) => {
            let (good, bad) = if pa.execute(g.public_input).is_ok() {
                (&a, &b)
            } else {
                (&b, &a)
            };
            Err(Finding::high(
                format!(
                    "{context}: two spellings of one program disagree ({})",
                    crate::programs::fault_kind(&e.fault)
                ),
                format!("{e}\n\nthis spelling fails:\n{bad}\n\nthis one runs:\n{good}"),
            ))
        }
        (Err(e), Err(_)) => Err(Finding::high(
            format!(
                "{context}: neither spelling computes the generated value ({})",
                crate::programs::fault_kind(&e.fault)
            ),
            format!("{e}\nexpected {:?}\n\n{a}\n\n{b}", g.public_input),
        )),
    }
}

/// What a compilation produced that a proof depends on: the bytecode, its layout and its source map.
fn fingerprint(p: &Program) -> String {
    format!("{:?}|{:?}|{:?}", p.prog(), p.fn_ranges, p.src_lines)
}
