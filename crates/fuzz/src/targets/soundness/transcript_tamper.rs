//! `soundness-transcript-tamper`: the prover forges one or several of the scalars it sends (`fiat_shamir::tamper`)
//! and then carries on honestly from the challenges its forgery induces, so the proof is Fiat-Shamir consistent with
//! the lie and only the checks the forged message feeds can catch it. Forgeries are aimed at every stage of the
//! stream (located from the honest proof's shape), and at the announced sizes, where the prover then commits its
//! real witness under a layout it lied about. Anything forged that verifies is Critical; a prover that panics on its
//! own forgery is noted, not reported.

use super::fixtures::{self, Fixture, Honest};
use crate::mutate_proof::{ANNOUNCED, perturb};
use crate::{Ctx, Outcome, Source, catch};
use leanvm_core::cpu::tamper::transcript;
use leanvm_core::tables::{N_TABLES, TABLE_LOG_FLOORS, tables};
use primitives::field::F192;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

/// The parts of an execution proof's stream, located from an honest proof of the same program and rate.
pub struct Stages {
    pub named: Vec<(&'static str, Range<usize>)>,
    /// Stream positions after the Keccak reduction that hold small integers: the grinding nonces.
    pub nonces: Vec<usize>,
}

impl Stages {
    pub fn of(honest: &Honest) -> Self {
        let len = honest.proof.stream.len();
        let keccak = honest.summary.keccak_scalars.clone();
        let taus: Vec<usize> = (0..N_TABLES)
            .map(|t| {
                let rows = honest.summary.table_rows[t] as usize;
                rows.next_power_of_two()
                    .trailing_zeros()
                    .max(TABLE_LOG_FLOORS[t] as u32) as usize
            })
            .collect();
        // The table sumcheck: three scalars a round over the tallest table, then every table's column evaluations.
        let widths: usize = tables().iter().map(|t| t.n_committed_columns()).sum();
        let table_len = 3 * taus.iter().max().copied().unwrap_or(0) + widths;
        let table_start = keccak.start.saturating_sub(table_len).max(ANNOUNCED + 2);
        let tail = len.saturating_sub(32).max(keccak.end);
        let named = vec![
            ("announced", 0..ANNOUNCED),
            ("root", ANNOUNCED..ANNOUNCED + 2),
            ("bus-gkr", ANNOUNCED + 2..table_start),
            ("table-sumcheck", table_start..keccak.start),
            ("keccak", keccak.clone()),
            ("ring-switch-whir", keccak.end..tail),
            ("whir-final", tail..len),
        ];
        let nonces = (keccak.end..len)
            .filter(|&i| {
                let x = honest.proof.stream[i];
                x.c1 == 0 && x.c2 == 0 && x.c0 < 1 << 32
            })
            .collect();
        Self { named, nonces }
    }

    fn stage_of(&self, i: usize) -> &'static str {
        if self.nonces.contains(&i) {
            return "nonce";
        }
        self.named
            .iter()
            .find(|(_, r)| r.contains(&i))
            .map_or("past-end", |(name, _)| name)
    }

    /// A position, biased to an even share per stage.
    fn position(&self, src: &mut Source) -> usize {
        if !self.nonces.is_empty() && src.chance(1, 8) {
            return self.nonces[src.below(self.nonces.len())];
        }
        let live: Vec<&Range<usize>> = self.named.iter().map(|(_, r)| r).filter(|r| !r.is_empty()).collect();
        let r = live[src.below(live.len())];
        match src.below(4) {
            0 => r.start,
            1 => r.end - 1,
            _ => src.range(r.start, r.end - 1),
        }
    }
}

/// What the forger does to the scalar at one position: add a difference, or send a value outright.
#[derive(Clone, Copy, Debug)]
enum Forge {
    Add(F192),
    Set(F192),
}

impl Forge {
    fn apply(self, x: F192) -> F192 {
        match self {
            Forge::Add(d) => x + d,
            Forge::Set(v) => v,
        }
    }
}

/// A lie about announced size `j` (`log_mem`, a table's rows, the rate), the prover committing its real witness.
fn announced_lie(j: usize, honest: &F192, src: &mut Source) -> F192 {
    let v = honest.c0;
    let lie = match src.below(6) {
        0 => v.wrapping_add(1),
        1 => v.wrapping_sub(1),
        2 => v.next_power_of_two(),
        3 if j == ANNOUNCED - 1 => src.range(0, 5) as u64,
        3 => 0,
        4 => v.wrapping_add(src.range(2, 1 << 12) as u64),
        _ => v ^ (1 << src.below(40)),
    };
    F192::new(lie, 0, 0)
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let Some((fixture, rate, honest)) = fixtures::draw(src)? else {
        return Ok(());
    };
    let stages = Stages::of(&honest);
    let stream = &honest.proof.stream;
    let mut plan: BTreeMap<usize, Forge> = BTreeMap::new();
    let shape = match src.below(8) {
        0 => {
            let j = src.below(ANNOUNCED);
            plan.insert(j, Forge::Set(announced_lie(j, &stream[j], src)));
            "announced-lie"
        }
        1 => {
            // A run of consecutive messages: a round polynomial, and the next round's.
            let start = stages.position(src);
            for i in start..(start + src.range(2, 8)).min(stream.len()) {
                plan.insert(i, Forge::Add(perturb(stream[i], src) + stream[i]));
            }
            "run"
        }
        2 => {
            // Two forgeries in different places, the second answering a transcript the first already changed.
            for _ in 0..2 {
                let i = stages.position(src);
                plan.insert(i, Forge::Add(perturb(stream[i], src) + stream[i]));
            }
            "pair"
        }
        3 => {
            // The same difference added to several positions of one stage.
            let i = stages.position(src);
            let d = perturb(stream[i], src) + stream[i];
            for k in 0..src.range(2, 5) {
                plan.insert((i + k * src.range(1, 3)).min(stream.len() - 1), Forge::Add(d));
            }
            "shared-difference"
        }
        _ => {
            let i = stages.position(src);
            let forge = if src.chance(1, 3) {
                Forge::Set(perturb(stream[i], src))
            } else {
                Forge::Add(perturb(stream[i], src) + stream[i])
            };
            plan.insert(i, forge);
            "single"
        }
    };
    let first = *plan.keys().next().expect("a forgery");
    let stage = stages.stage_of(first);
    ctx.note(format!("{shape} {stage}"));
    forge_and_verify(fixture, rate, plan, ctx, &format!("{shape} at {stage}"))
}

/// Prove `fixture` with `plan`'s forgeries armed, then verify: Critical if a forged proof verifies.
fn forge_and_verify(
    fixture: &'static Fixture,
    rate: usize,
    plan: BTreeMap<usize, Forge>,
    ctx: &Ctx,
    what: &str,
) -> Outcome {
    let changed = Rc::new(Cell::new(false));
    let seen = changed.clone();
    let described = format!("{plan:?}");
    transcript::arm(Box::new(move |i, x| match plan.get(&i) {
        Some(forge) => {
            let y = forge.apply(x);
            if y != x {
                seen.set(true);
            }
            y
        }
        None => x,
    }));
    let proved = catch(|| leanvm_core::cpu::prove(&fixture.program, fixture.public_input, rate));
    transcript::disarm();
    let proof = match proved {
        Err(_) => {
            ctx.note(format!("{what}: prover panicked"));
            return Ok(());
        }
        Ok(Err(e)) => {
            ctx.note(format!(
                "{what}: prover refused {}",
                crate::programs::prove_error_kind(&e)
            ));
            return Ok(());
        }
        Ok(Ok((proof, _))) => proof,
    };
    if !changed.get() {
        ctx.note("forgery a no-op");
        return Ok(());
    }
    let context = format!("soundness-transcript-tamper {}", fixture.name);
    let verdict = super::verify_caught(fixture, &proof, &context)?;
    if let Err(e) = &verdict {
        ctx.note(format!("{what}: rejected {}", fixtures::error_name(e)));
    }
    super::must_reject(
        ctx,
        verdict,
        format!("soundness-transcript-tamper: a forged transcript verifies ({what})"),
        || format!("program {}, rate {rate}, forgeries {described}", fixture.name),
    )
}
