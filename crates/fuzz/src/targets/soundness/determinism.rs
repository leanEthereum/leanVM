//! `soundness-determinism`: grinding takes the smallest valid nonce and the fixtures take no randomness, so a proof
//! is a function of its program, statement and rate. Two proofs in one process must be byte-identical, and a digest
//! of the proof is kept under the campaign directory, which the supervisor's workers, each with its own
//! `LEANVM_NUM_THREADS`, compare against: a difference is a proof depending on the thread count or on state left
//! over from an earlier run (High).

use super::fixtures;
use crate::{Ctx, Finding, Outcome, Source};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// This binary's identity (its path, size and modification time): digests are compared only between workers of
/// one build, since a rebuilt prover may legitimately prove differently.
fn build() -> &'static str {
    static BUILD: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    BUILD.get_or_init(|| {
        let exe = std::env::current_exe().unwrap_or_default();
        let meta = std::fs::metadata(&exe).ok();
        let stamp = meta
            .as_ref()
            .and_then(|m| m.modified().ok())
            .map(|t| format!("{t:?}"))
            .unwrap_or_default();
        let id = format!("{} {} {stamp}", exe.display(), meta.map_or(0, |m| m.len()));
        hex(&primitives::hash::hash(id.as_bytes())[..8])
    })
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let fixture = fixtures::pick(src);
    let rate = crate::programs::log_inv_rate(src);
    let context = format!("soundness-determinism {}", fixture.name);
    let Some(cached) = fixtures::honest(fixture, rate)? else {
        return Ok(());
    };
    let Ok((fresh, _)) = leanvm_core::cpu::prove(&fixture.program, fixture.public_input, rate) else {
        return Err(Finding::high(
            format!("{context}: a proof that succeeded once is refused"),
            format!("rate {rate}"),
        ));
    };
    let threads = parallel::num_threads();
    if fresh != cached.proof {
        return Err(Finding::high(
            "soundness-determinism: two proofs of one statement differ in one process",
            format!("program {}, rate {rate}, {threads} threads", fixture.name),
        ));
    }
    let digest = hex(&primitives::hash::hash(&fresh.to_bytes()));
    let name = format!(
        "determinism/{}/{}-{rate}.digest",
        build(),
        fixture.name.replace('/', "_")
    );
    let path = ctx.path(&name);
    match std::fs::read_to_string(&path) {
        Ok(kept) => {
            let mut fields = kept.split_whitespace();
            let (Some(theirs), their_threads) = (fields.next(), fields.next().unwrap_or("?")) else {
                return Ok(());
            };
            ctx.note(if their_threads == threads.to_string() {
                "digest same threads"
            } else {
                "digest other threads"
            });
            if theirs.len() == digest.len() && theirs != digest {
                return Err(Finding::high(
                    "soundness-determinism: a proof differs across processes",
                    format!(
                        "program {}, rate {rate}: {digest} with {threads} threads, {theirs} with {their_threads} in {}",
                        fixture.name,
                        path.display()
                    ),
                ));
            }
        }
        Err(_) => {
            let tmp = path.with_extension(format!("tmp{}", std::process::id()));
            if std::fs::write(&tmp, format!("{digest} {threads}\n")).is_ok() {
                let _ = std::fs::rename(&tmp, &path);
            }
            ctx.note("digest recorded");
        }
    }
    Ok(())
}
