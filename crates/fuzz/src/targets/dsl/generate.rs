//! `dsl-gen`: a generated self-checking program (`gen`) in a random spelling (`print`) must compile, run to exactly
//! the public input the generator computed, and prove; its proof must not verify for another public input.

use super::print::{self, Style};
use super::synth::{self, Generated, Limits};
use crate::findings::normalize;
use crate::programs::{self, CompileFailure};
use crate::{Ctx, Finding, Outcome, Source};
use leanvm_core::cpu::{Execution, Fault, Program};
use primitives::field::F192;

/// Runs longer than this are not proven: a generated program is small, and a long one is the generator's doing.
const PROVE_CYCLES: usize = 1 << 18;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let lim = Limits::for_depth(src, ctx.depth);
    let g = synth::generate(src, lim);
    let style = if src.chance(1, 4) {
        Style::plain()
    } else {
        Style::random(&mut src.rng())
    };
    let source = print::print(&g.prog, &style, src.u64());
    for f in &g.features {
        ctx.note(*f);
    }
    let (program, exec) = compile_and_run(&source, &g, "dsl-gen")?;
    ctx.note(format!("ran, {} cycles", bucket(exec.cycles)));
    let prove = match ctx.depth {
        0 => false,
        1 => src.chance(1, 8),
        _ => true,
    };
    if prove && exec.cycles <= PROVE_CYCLES {
        drop(exec);
        prove_and_perturb(&program, g.public_input, src, ctx, "dsl-gen", &annotated(&source, &g))?;
    }
    Ok(())
}

/// A coarse size, for notes.
pub fn bucket(n: usize) -> String {
    format!("<2^{}", usize::BITS - n.leading_zeros())
}

/// The program with the generator's witness streams installed.
pub fn compile(source: &str, g: &Generated, context: &str) -> Result<Program, Finding> {
    let mut program = programs::compile_source(source).map_err(|f| compile_finding(&f, source, context))?;
    for (name, entries) in &g.witness {
        program.set_witness(name.clone(), entries.clone());
    }
    Ok(program)
}

/// A well-formed program the compiler refused: every refusal of a generated program is a finding.
pub fn compile_finding(f: &CompileFailure, source: &str, context: &str) -> Finding {
    let (what, key) = match f {
        CompileFailure::Parse(m) => ("parse error", short(m)),
        CompileFailure::ParsePanic { message, location } => ("parse panic", format!("{location}: {}", short(message))),
        CompileFailure::CompilePanic { message, location } => {
            ("compile panic", format!("{location}: {}", short(message)))
        }
    };
    Finding::high(
        format!("{context}: a well-formed program is refused ({what}): {key}"),
        format!("{}\n\n{source}", f.message()),
    )
}

/// A message without its numbers and names, cut where it starts to name the program's own text.
fn short(m: &str) -> String {
    let m = normalize(m);
    let m = m.split('`').next().unwrap_or(&m).to_string();
    m.chars().take(90).collect()
}

pub fn compile_and_run(source: &str, g: &Generated, context: &str) -> Result<(Program, Execution), Finding> {
    let program = compile(source, g, context)?;
    let exec = run_expect(&program, g.public_input, source, g, context)?;
    Ok((program, exec))
}

/// Run on the public input the generator computed: any fault is the program computing something else.
pub fn run_expect(
    program: &Program,
    pi: [F192; 2],
    source: &str,
    g: &Generated,
    context: &str,
) -> Result<Execution, Finding> {
    match program.execute(pi) {
        Ok(exec) => Ok(exec),
        Err(e) => {
            let kind = match &e.fault {
                Fault::Conflict { cell, .. } if *cell < 2 => "publishes another public input".to_string(),
                Fault::Conflict { hint: Some(h), .. } => format!("conflict in hint {h}"),
                Fault::Conflict { .. } => "a write-once conflict (an assertion fails)".to_string(),
                other => format!("faults: {}", programs::fault_kind(other)),
            };
            Err(Finding::high(
                format!("{context}: a generated program {kind}"),
                format!("{e}\n\n{}", annotated(source, g)),
            ))
        }
    }
}

/// Prove and verify, then check the proof does not verify for a neighbouring statement.
pub fn prove_and_perturb(
    program: &Program,
    pi: [F192; 2],
    src: &mut Source,
    ctx: &Ctx,
    context: &str,
    source: &str,
) -> Outcome {
    let rate = programs::log_inv_rate(src);
    let proof = programs::prove_honest(program, pi, rate, context).map_err(|mut f| {
        f.detail = format!("{}\n\n{source}", f.detail);
        f
    })?;
    let Some(proof) = proof else { return Ok(()) };
    ctx.note("proved");
    let mut other = pi;
    let i = src.below(2);
    other[i] = crate::mutate_proof::perturb(other[i], src);
    other[i].c2 = 0;
    if other != pi && leanvm_core::cpu::verify(program, &other, &proof).is_ok() {
        return Err(Finding::critical(
            format!("{context}: a proof verifies for another public input"),
            format!("proven {pi:?}, accepted {other:?}\n\n{source}"),
        ));
    }
    Ok(())
}

/// The program as a corpus file: its public input and witness as annotations, so it replays with
/// `leanvm-fuzz programs` once saved under `crates/fuzz/programs/`.
pub fn annotated(source: &str, g: &Generated) -> String {
    // `parse_const` reads integers, `+` and `*`: the third limb is a multiple of `y² = (2^64)²`.
    let elt = |x: &F192| {
        let low = x.c0 as u128 | (x.c1 as u128) << 64;
        if x.c2 == 0 {
            low.to_string()
        } else {
            format!("{low} + {} * 18446744073709551616 * 18446744073709551616", x.c2)
        }
    };
    let mut out = format!(
        "# public_input: {}, {}\n",
        elt(&g.public_input[0]),
        elt(&g.public_input[1])
    );
    for (name, entries) in &g.witness {
        for entry in entries {
            let items: Vec<String> = entry.iter().map(elt).collect();
            out.push_str(&format!("# witness {name}: {}\n", items.join(", ")));
        }
    }
    out + source
}
