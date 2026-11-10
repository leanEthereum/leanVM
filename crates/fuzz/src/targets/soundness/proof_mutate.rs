//! `soundness-proof-mutate`: one or several structured edits of an honest proof (`mutate_proof`). A changed proof
//! that verifies is Critical; a verifier or replay that panics on it is Medium. Edits made after the fact break
//! Fiat-Shamir, so this mostly drives every check's failure path and the verifier's reading of malformed proofs.

use super::fixtures::{self, Honest};
use super::{must_reject, replay_caught, verify_caught};
use crate::mutate_proof;
use crate::{Ctx, Outcome, Source};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let Some((fixture, rate, honest)) = fixtures::draw(src)? else {
        return Ok(());
    };
    // Another honest proof to splice from: the same program at another rate, or another program.
    let other = if src.bool() {
        let other_rate = crate::programs::log_inv_rate(src);
        fixtures::honest(fixture, other_rate)?
    } else {
        fixtures::draw(src)?.map(|(_, _, h)| h)
    };
    let mut proof = honest.proof.clone();
    let n = if src.chance(1, 4) { src.range(2, 6) } else { 1 };
    let mut edits = Vec::new();
    for _ in 0..n {
        edits.push(mutate_proof::mutate(
            &mut proof,
            src,
            other.as_deref().map(|h: &Honest| &h.proof),
        ));
    }
    let what = edits.join("+");
    if edits.len() == 1 {
        ctx.note(format!("mutation {what}"));
    } else {
        ctx.note("mutation several");
    }
    if proof == honest.proof {
        ctx.note("mutation unchanged");
        return Ok(());
    }
    let context = format!("soundness-proof-mutate {}", fixture.name);
    let replayed = replay_caught(fixture, &proof, &context)?;
    let verdict = verify_caught(fixture, &proof, &context)?;
    if let Err(e) = &verdict {
        ctx.note(format!("{} rejected {}", edits[0], fixtures::error_name(e)));
    }
    if let Err(e) = replayed {
        ctx.note(format!("replay refused {}", fixtures::verifier_error_name(&e)));
    }
    must_reject(
        ctx,
        verdict,
        format!("soundness-proof-mutate: a mutated proof verifies ({})", edits[0]),
        || format!("program {}, rate {rate}, edits {what}", fixture.name),
    )
}
