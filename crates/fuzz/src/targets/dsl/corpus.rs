//! `dsl-corpus`: every hand-written program, held to what its annotations promise, then proven, then its statement
//! changed under the proof.

use crate::programs::{self, CompileFailure, Expect};
use crate::{Ctx, Finding, Outcome, Source};
use leanvm_core::cpu::ProveError;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let corpus = programs::corpus_at(ctx.depth);
    let spec = &corpus[src.below(corpus.len())];
    check(spec, src, ctx)
}

/// One program against its annotations: what `cargo leanvm-fuzz programs` runs on each.
pub fn check(spec: &programs::Spec, src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note(format!("program {}", spec.name));
    let context = format!("dsl-corpus {}", spec.name);
    let program = match spec.compile() {
        Ok(program) => program,
        Err(failure) => {
            if let Some(finding) = failure.as_finding(&context)
                && finding.severity < crate::Severity::Low
            {
                return Err(finding);
            }
            return match (&spec.expect, &failure) {
                (Expect::CompileError(want), f) if f.message().contains(want.as_str()) => Ok(()),
                (Expect::Any, _) => Ok(()),
                (_, CompileFailure::CompilePanic { message, location }) => Err(Finding::high(
                    format!("{context}: compile failed, expected {:?}", spec.expect),
                    format!("panicked at {location}: {message}"),
                )),
                (_, f) => Err(Finding::high(
                    format!("{context}: compile failed, expected {:?}", spec.expect),
                    f.message().to_string(),
                )),
            };
        }
    };
    if let Expect::CompileError(_) = spec.expect {
        return Err(Finding::high(
            format!("{context}: compiled, expected a compile error"),
            String::new(),
        ));
    }
    let (run, pi) = programs::execute(&program, spec.public_input);
    let exec = match (run, &spec.expect) {
        (Err(e), Expect::ExecFail(want)) if e.to_string().contains(want.as_str()) => {
            ctx.note(format!("exec-fail {}", programs::fault_kind(&e.fault)));
            return Ok(());
        }
        (Err(_), Expect::Any) => return Ok(()),
        (Err(e), expect) => {
            return Err(Finding::high(
                format!(
                    "{context}: run failed ({}), expected {expect:?}",
                    programs::fault_kind(&e.fault)
                ),
                e.to_string(),
            ));
        }
        (Ok(exec), Expect::ExecFail(want)) => {
            return Err(Finding::high(
                format!("{context}: ran, expected a run failure `{want}`"),
                format!("{} cycles", exec.cycles),
            ));
        }
        (Ok(exec), _) => exec,
    };
    ctx.note(format!("ran {}", spec.name));
    let unconstrained = !exec.unconstrained_reads.is_empty();
    drop(exec);
    if spec.slow && ctx.depth < 2 {
        return Ok(());
    }
    let rate = programs::log_inv_rate(src);
    match &spec.expect {
        Expect::ProveFail(want) => match leanvm_core::cpu::prove(&program, pi, rate) {
            Err(e) if e.to_string().contains(want.as_str()) => Ok(()),
            Err(e) => Err(Finding::high(
                format!("{context}: prove refused, but not with `{want}`"),
                e.to_string(),
            )),
            Ok(_) => Err(Finding::high(
                format!("{context}: proved, expected a prove failure `{want}`"),
                String::new(),
            )),
        },
        Expect::Ok | Expect::Any => {
            if unconstrained {
                return match leanvm_core::cpu::prove(&program, pi, rate) {
                    Err(ProveError::UnconstrainedReads(_)) if spec.expect == Expect::Any => Ok(()),
                    Err(ProveError::UnconstrainedReads(cells)) => Err(Finding::high(
                        format!("{context}: reads unwritten cells, expected ok"),
                        format!("{cells:?}"),
                    )),
                    other => Err(Finding::high(
                        format!("{context}: a run with unconstrained reads was not refused"),
                        format!("{:?}", other.err()),
                    )),
                };
            }
            let Some(proof) = programs::prove_honest(&program, pi, rate, &context)? else {
                return Ok(());
            };
            ctx.note(format!("proved {}", spec.name));
            // The proof is of this statement only.
            let mut other = pi;
            let i = src.below(2);
            other[i] = crate::mutate_proof::perturb(other[i], src);
                    if other != pi && leanvm_core::cpu::verify(&program, &other, &proof).is_ok() {
                return Err(Finding::critical(
                    format!("{context}: a proof verifies for another public input"),
                    format!("proven {pi:?}, accepted {other:?}"),
                ));
            }
            Ok(())
        }
        _ => unreachable!(),
    }
}
