//! `soundness-replay-consistency`: `replay_unchecked` walks the transcript `verify_execution` walks, checking
//! nothing. On an honest proof both return one `Summary`. On a mutated one the replay never panics, never refuses a
//! proof verify accepts, and refuses one exactly where verify fails structurally: a structural error is raised in
//! both modes at the same point of one walk, so verify meeting one first means no check failed before it.

use super::fixtures;
use super::{replay_caught, verify_caught};
use crate::mutate_proof;
use crate::{Ctx, Finding, Outcome, Source};
use verifier::VerifierError;

/// Errors the walk raises in both modes, outside any check: reading a proof of the wrong length or shape.
fn structural(e: &VerifierError) -> bool {
    use VerifierError::*;
    matches!(
        e,
        StreamExhausted
            | StreamNotConsumed
            | MerkleNotConsumed
            | MerkleOpeningMissing
            | MerkleOpeningShape
            | MerkleOpeningPosition
            | AnnouncedHighLimb
            | PcsInverseRate
            | CommittedSize
            | AnnouncedTableSizes
            | WhirShape
            | QueryCountLadder
            | WhirNoTerminalLevel
    )
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let Some((fixture, rate, honest)) = fixtures::draw(src)? else {
        return Ok(());
    };
    let context = format!("soundness-replay-consistency {}", fixture.name);
    let mut proof = honest.proof.clone();
    let mutated = src.chance(3, 4);
    let mut edit = "honest";
    if mutated {
        edit = mutate_proof::mutate(&mut proof, src, None);
        ctx.note(format!("mutation {edit}"));
    }
    let replayed = replay_caught(fixture, &proof, &context)?;
    let verdict = verify_caught(fixture, &proof, &context)?;
    let detail = || format!("program {}, rate {rate}, edit {edit}", fixture.name);
    match (&verdict, &replayed) {
        (Ok(checked), Ok(replay)) => {
            ctx.note("both accept");
            if checked != replay {
                return Err(Finding::high(
                    format!("{context}: replay's summary differs from verify's"),
                    format!("{}\nverify {checked:?}\nreplay {replay:?}", detail()),
                ));
            }
            if proof == honest.proof && *checked != honest.summary {
                return Err(Finding::high(
                    format!("{context}: verify's summary changed between calls"),
                    detail(),
                ));
            }
        }
        (Ok(_), Err(e)) => {
            return Err(Finding::high(
                format!(
                    "{context}: replay refuses a proof verify accepts ({})",
                    fixtures::verifier_error_name(e)
                ),
                detail(),
            ));
        }
        (Err(v), replay) if structural(v) => {
            ctx.note(format!("structural {}", fixtures::verifier_error_name(v)));
            if replay.as_ref().err() != Some(v) {
                return Err(Finding::high(
                    format!(
                        "{context}: verify fails structurally ({}) where replay does not",
                        fixtures::verifier_error_name(v)
                    ),
                    format!("{}\nreplay {replay:?}", detail()),
                ));
            }
        }
        (Err(e), replay) => {
            ctx.note(format!(
                "check {} replay {}",
                fixtures::error_name(e),
                replay.as_ref().err().map_or("ok".into(), fixtures::verifier_error_name)
            ));
        }
    }
    if verdict.is_ok() && proof != honest.proof {
        return Err(Finding::critical(
            format!("{context}: a mutated proof verifies ({edit})"),
            detail(),
        ));
    }
    Ok(())
}
