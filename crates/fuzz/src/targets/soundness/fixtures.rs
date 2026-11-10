//! The honest proofs the soundness targets attack: a few programs written here to reach every table (and one
//! KECCAK-heavy and one memory-heavy shape), plus every small provable corpus program. Each program is compiled and
//! run once per process, and each `(program, rate)` proven once.

use crate::programs;
use crate::{Finding, Source};
use leanvm_core::cpu::{self, CpuError, Program, Proof};
use primitives::field::{F64, F192};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// Programs written for these targets, each deterministic (no hint streams beyond what it states).
const INLINE: &[(&str, &str)] = &[
    (
        "inline/all_tables",
        r#"
from snark_lib import *

def step(a, b):
    c = a + b
    return c * GEN

def main():
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 7
    for i in mul_range(1, GEN ** 3):
        b = i * i
        keccak(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    acc = HeapBuf(8)
    acc[1] = GEN
    for i in mul_range(1, GEN ** 5):
        acc[i * GEN] = step(acc[i], GEN ** 3)
    r = HeapBuf(1)
    if acc[GEN ** 2] == acc[GEN ** 3]:
        r[1] = 1
    else:
        r[1] = 2
    assert r[1] == 2
    p = GEN ** 0
    p[1] = buf[GEN ** 6]
    p[GEN] = acc[GEN ** 5]
    return
"#,
    ),
    (
        "inline/keccak_heavy",
        r#"
from snark_lib import *

def main():
    buf = HeapBuf(1210)
    buf[1] = 5
    buf[GEN] = 7
    for i in mul_range(1, GEN ** 600):
        b = i * i
        keccak(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    p = GEN ** 0
    p[1] = buf[GEN ** 1200]
    p[GEN] = buf[GEN ** 1201]
    return
"#,
    ),
    (
        "inline/memory_heavy",
        r#"
from snark_lib import *

def main():
    buf = HeapBuf(4096)
    buf[1] = GEN
    for i in mul_range(1, GEN ** 4095):
        buf[i * GEN] = buf[i] * GEN + i
    p = GEN ** 0
    p[1] = buf[GEN ** 4095]
    p[GEN] = buf[GEN ** 17]
    return
"#,
    ),
    (
        "inline/hinted",
        r#"
# witness r: GEN ** 5, 12
# witness h: 3, 5, 6
from snark_lib import *

def main():
    sb = StackBuf(2)
    hint_witness(sb, "r")
    assert log(sb[0]) < 8
    assert sb[1] == 12
    hb = HeapBuf(4)
    hint_witness(hb[0:3], "h")
    assert hb[1] + hb[GEN] == hb[GEN ** 2]
    p = GEN ** 0
    p[1] = sb[0]
    p[GEN] = hb[GEN ** 2]
    return
"#,
    ),
];

/// A program with the statement it was run on.
pub struct Fixture {
    pub name: String,
    pub program: Program,
    pub public_input: [F192; 2],
    /// The pcs the honest run executed, recorded the first time it is proven.
    executed: OnceLock<Vec<usize>>,
}

impl Fixture {
    /// The executed pcs, once [`honest`] has proven this program at least once.
    pub fn executed(&self) -> &[usize] {
        self.executed.get().map_or(&[], |v| v)
    }

    pub fn verify(&self, proof: &Proof) -> Result<verifier::Summary, CpuError> {
        cpu::verify(&self.program, &self.public_input, proof)
    }
}

/// The most cycles a corpus program may run to be a fixture (the inline ones are sized by hand): proofs here have to take about a second.
const MAX_CYCLES: usize = 1 << 16;
/// The most `KECCAK` steps, and memory cells, likewise.
const MAX_KECCAK: usize = 1 << 11;
const MAX_CELLS: usize = 1 << 20;
const KECCAK_TABLE: usize = 5;

pub fn fixtures() -> &'static [Fixture] {
    static FIXTURES: OnceLock<Vec<Fixture>> = OnceLock::new();
    FIXTURES.get_or_init(|| {
        let mut out = Vec::new();
        let inline = INLINE.iter().map(|&(name, source)| (name.to_string(), source, None));
        let corpus = programs::provable()
            .into_iter()
            .filter(|s| !s.slow)
            .map(|s| (s.name.to_string(), s.source, Some(s)));
        for (name, source, spec) in inline.chain(corpus) {
            let parsed = match spec {
                Some(spec) => spec.clone(),
                None => match programs::Spec::parse("inline", source) {
                    Ok(spec) => spec,
                    Err(_) => continue,
                },
            };
            let Ok(program) = parsed.compile() else { continue };
            if !program.prog().len().is_power_of_two() {
                continue;
            }
            let (run, public_input) = programs::execute(&program, parsed.public_input);
            let Ok(exec) = run else { continue };
            if std::env::var_os("LEANVM_FUZZ_VERBOSE").is_some() {
                eprintln!(
                    "fixture {name}: {} cycles, rows {:?}, {} cells",
                    exec.cycles,
                    exec.rows(),
                    exec.mem.len()
                );
            }
            if !exec.unconstrained_reads.is_empty()
                || (spec.is_some()
                    && (exec.cycles > MAX_CYCLES
                        || exec.rows()[KECCAK_TABLE] > MAX_KECCAK
                        || exec.mem.len() > MAX_CELLS))
                || public_input.iter().any(|h| h.c2 != 0)
            {
                continue;
            }
            out.push(Fixture {
                name,
                program,
                public_input,
                executed: OnceLock::new(),
            });
        }
        for (name, _) in INLINE {
            assert!(
                out.iter().any(|f| f.name == *name),
                "the soundness fixture {name} no longer compiles or runs"
            );
        }
        out
    })
}

/// A fixture drawn from the input: the inline programs (every table) half the time.
pub fn pick(src: &mut Source) -> &'static Fixture {
    let all = fixtures();
    let n_inline = all.iter().take_while(|f| f.name.starts_with("inline/")).count();
    if src.bool() {
        &all[src.below(n_inline)]
    } else {
        &all[src.below(all.len())]
    }
}

/// One of the fixtures `names`, or any fixture when none of them is one.
pub fn pick_named(src: &mut Source, names: &[&str]) -> &'static Fixture {
    let named: Vec<&'static Fixture> = fixtures().iter().filter(|f| names.contains(&f.name.as_str())).collect();
    if named.is_empty() {
        pick(src)
    } else {
        named[src.below(named.len())]
    }
}

/// An honest proof of `fixture` at `rate`, verified once.
pub struct Honest {
    pub proof: Proof,
    pub summary: verifier::Summary,
}

/// The honest proof, cached per process. `Ok(None)` when the prover documentedly refuses the run (a witness out of
/// the PCS window); a refused or rejected honest run is a completeness finding.
pub fn honest(fixture: &'static Fixture, rate: usize) -> Result<Option<Arc<Honest>>, Finding> {
    type Cache = Mutex<HashMap<(usize, usize), Option<Arc<Honest>>>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let key = (fixture as *const Fixture as usize, rate);
    if let Some(hit) = CACHE.get_or_init(Default::default).lock().unwrap().get(&key) {
        return Ok(hit.clone());
    }
    let executed = Arc::new(Mutex::new(Vec::new()));
    if fixture.executed.get().is_none() {
        let sink = executed.clone();
        cpu::tamper::arm(Box::new(move |view| {
            let counts = view.column(cpu::tamper::BFCNT);
            *sink.lock().unwrap() = (0..counts.len()).filter(|&pc| counts[pc] != F64::ONE).collect();
        }));
    }
    let context = format!("soundness {}", fixture.name);
    // A corpus program that does not prove honestly (a known completeness bug) is `dsl-corpus`'s finding, not a
    // fixture: it is skipped, but an inline program here has to prove.
    let proof = match programs::prove_honest(&fixture.program, fixture.public_input, rate, &context) {
        Ok(proof) => proof,
        Err(finding) if fixture.name.starts_with("inline/") => return Err(finding),
        Err(_) => None,
    };
    cpu::tamper::disarm();
    let entry = proof.map(|proof| {
        let summary = fixture.verify(&proof).expect("prove_honest verified it");
        Arc::new(Honest { proof, summary })
    });
    if entry.is_some() {
        let _ = fixture.executed.set(std::mem::take(&mut executed.lock().unwrap()));
    }
    CACHE
        .get_or_init(Default::default)
        .lock()
        .unwrap()
        .insert(key, entry.clone());
    Ok(entry)
}

/// A fixture, the rate it was proven at, and its honest proof.
pub type Drawn = (&'static Fixture, usize, Arc<Honest>);

/// A fixture and its honest proof at a rate the input draws, skipping (with `None`) a run the prover refuses.
pub fn draw(src: &mut Source) -> Result<Option<Drawn>, Finding> {
    let fixture = pick(src);
    let rate = programs::log_inv_rate(src);
    Ok(honest(fixture, rate)?.map(|h| (fixture, rate, h)))
}

/// A verifier error's variant, without its payload: what notes and keys name.
pub fn error_name(e: &CpuError) -> String {
    match e {
        CpuError::PublicInput => "PublicInput".to_string(),
        CpuError::Verifier(v) => verifier_error_name(v),
    }
}

pub fn verifier_error_name(e: &verifier::VerifierError) -> String {
    format!("{e:?}").split('(').next().unwrap_or_default().to_string()
}

#[cfg(test)]
mod tests {
    #[test]
    fn inline_programs_run() {
        let fixtures = super::fixtures();
        for (name, _) in super::INLINE {
            assert!(fixtures.iter().any(|f| f.name == *name), "{name} is not a fixture");
        }
    }
}
