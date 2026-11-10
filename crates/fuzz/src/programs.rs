//! The hand-written program corpus (`crates/fuzz/programs/`, and `crates/lean_compiler/tests/programs/`), and the
//! helpers every target uses to compile, run and prove a zkDSL program.
//!
//! A program states what should happen to it in comment annotations at the top of the file:
//!
//! ```text
//! # expect: ok                        (the default) it runs, and its honest proof verifies
//! # expect: exec-fail <substring>     the run fails, its error mentioning <substring> (empty: any failure)
//! # expect: compile-error <substring> parse or compile refuses it, without a panic elsewhere than the compiler
//! # expect: prove-fail <substring>    it runs, but `prove` refuses it (unconstrained reads, witness size)
//! # expect: any                       anything but a crash outside the compiler: an exploration seed
//! # public_input: <elt>, <elt>        as in lean_compiler's tests; omitted, it is discovered from the run
//! # witness <name>: <elt>, ...        one line per entry of a hint stream
//! # fuzz: slow                        prove it only at depth 2
//! ```

use crate::{Finding, catch};
use lean_compiler::{compile, parse, parse_const};
use leanvm_core::cpu::{ExecError, Execution, Fault, Program, ProveError};
use primitives::field::F192;

include!(concat!(env!("OUT_DIR"), "/programs.rs"));

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expect {
    Ok,
    ExecFail(String),
    CompileError(String),
    ProveFail(String),
    Any,
}

#[derive(Clone, Debug)]
pub struct Spec {
    pub name: &'static str,
    pub source: &'static str,
    pub public_input: Option<[F192; 2]>,
    pub witness: Vec<(String, Vec<Vec<F192>>)>,
    pub expect: Expect,
    pub slow: bool,
}

impl Spec {
    pub fn parse(name: &'static str, source: &'static str) -> Result<Self, String> {
        let mut spec = Spec {
            name,
            source,
            public_input: None,
            witness: Vec::new(),
            expect: Expect::Ok,
            slow: false,
        };
        let elt = |s: &str| parse_const(s.trim()).map_err(|e| format!("{name}: bad constant `{s}`: {e}"));
        for line in source.lines().map(str::trim) {
            if let Some(rest) = line.strip_prefix("# public_input:") {
                let parts: Vec<&str> = rest.split(',').collect();
                if parts.len() != 2 {
                    return Err(format!("{name}: `# public_input:` needs two elements"));
                }
                spec.public_input = Some([elt(parts[0])?, elt(parts[1])?]);
            } else if let Some(rest) = line.strip_prefix("# witness ") {
                let (stream, values) = rest
                    .split_once(':')
                    .ok_or(format!("{name}: `# witness` needs `name: values`"))?;
                let entry = if values.trim().is_empty() {
                    Vec::new()
                } else {
                    values.split(',').map(elt).collect::<Result<_, _>>()?
                };
                match spec.witness.iter_mut().find(|(n, _)| n == stream.trim()) {
                    Some((_, entries)) => entries.push(entry),
                    None => spec.witness.push((stream.trim().to_string(), vec![entry])),
                }
            } else if let Some(rest) = line.strip_prefix("# expect:") {
                let rest = rest.trim();
                let (kind, arg) = rest.split_once(' ').unwrap_or((rest, ""));
                let arg = arg.trim().to_string();
                spec.expect = match kind {
                    "ok" => Expect::Ok,
                    "exec-fail" => Expect::ExecFail(arg),
                    "compile-error" => Expect::CompileError(arg),
                    "prove-fail" => Expect::ProveFail(arg),
                    "any" => Expect::Any,
                    _ => return Err(format!("{name}: unknown expectation `{kind}`")),
                };
            } else if line == "# fuzz: slow" {
                spec.slow = true;
            }
        }
        Ok(spec)
    }

    /// The program with its witness streams installed.
    pub fn compile(&self) -> Result<Program, CompileFailure> {
        let mut program = compile_source(self.source)?;
        for (stream, entries) in &self.witness {
            program.set_witness(stream.clone(), entries.clone());
        }
        Ok(program)
    }
}

/// Every corpus program. A malformed annotation is a bug in the corpus, so it panics.
pub fn corpus() -> &'static [Spec] {
    static CORPUS: std::sync::OnceLock<Vec<Spec>> = std::sync::OnceLock::new();
    CORPUS.get_or_init(|| {
        PROGRAMS
            .iter()
            .map(|&(name, source)| Spec::parse(name, source).unwrap_or_else(|e| panic!("{e}")))
            .collect()
    })
}

/// Corpus programs that run and prove: the honest fixtures the soundness targets attack.
pub fn provable() -> Vec<&'static Spec> {
    corpus().iter().filter(|s| s.expect == Expect::Ok).collect()
}

/// Why a source did not become a program.
#[derive(Clone, Debug)]
pub enum CompileFailure {
    /// `parse` returned an error.
    Parse(String),
    /// `parse` returned an error by panicking, which it should never do.
    ParsePanic { message: String, location: String },
    /// `compile` panicked: documented for a malformed program.
    CompilePanic { message: String, location: String },
}

impl CompileFailure {
    pub fn message(&self) -> &str {
        match self {
            Self::Parse(m) => m,
            Self::ParsePanic { message, .. } | Self::CompilePanic { message, .. } => message,
        }
    }

    /// A panic in `parse` is a bug (it returns `Result`); one in `compile` is documented but kept for triage, and
    /// one outside the compiler's own source (an index out of bounds in a dependency, an overflow) is ranked higher.
    pub fn as_finding(&self, context: &str) -> Option<Finding> {
        match self {
            Self::Parse(_) => None,
            Self::ParsePanic { message, location } => Some(Finding::panic(message, location).in_context(context)),
            Self::CompilePanic { message, location } => {
                let finding = Finding::panic(message, location).in_context(context);
                // `expect`/`assert!` messages in the compiler are its documented rejections; anything else (an
                // index out of bounds, an overflow, an `unwrap` on `None`) is a crash.
                let documented = location.contains("lean_compiler/")
                    && !message.contains("index out of bounds")
                    && !(message.starts_with("attempt to ") && message.ends_with("with overflow"))
                    && !message.contains("called `Option::unwrap()`")
                    && !message.contains("called `Result::unwrap()`");
                Some(if documented {
                    finding.with_severity(crate::Severity::Low)
                } else {
                    finding
                })
            }
        }
    }
}

/// Parse and compile, catching the compiler's panics.
pub fn compile_source(source: &str) -> Result<Program, CompileFailure> {
    let ast = match catch(|| parse(source)) {
        Ok(Ok(ast)) => ast,
        Ok(Err(e)) => return Err(CompileFailure::Parse(e)),
        Err((message, location)) => return Err(CompileFailure::ParsePanic { message, location }),
    };
    catch(|| compile(&ast)).map_err(|(message, location)| CompileFailure::CompilePanic { message, location })
}

/// Run `program`, learning the public input it publishes when `public_input` is `None`. A run on zeros that publishes
/// `x` conflicts on the pair `{0, x}`, at the public cell or at the cell the store copies from, so `x` is tried in each
/// zero slot, keeping the first that moves the run past that conflict.
pub fn execute(program: &Program, public_input: Option<[F192; 2]>) -> (Result<Execution, ExecError>, [F192; 2]) {
    match public_input {
        Some(pi) => (program.execute(pi), pi),
        None => discover(program),
    }
}

/// The value a run conflicted on against zero, if that is how it failed.
fn published(result: &Result<Execution, ExecError>) -> Option<F192> {
    match result {
        Err(ExecError {
            fault: Fault::Conflict {
                had, new, hint: None, ..
            },
            ..
        }) if (*had == F192::ZERO) != (*new == F192::ZERO) => Some(*had + *new),
        _ => None,
    }
}

fn discover(program: &Program) -> (Result<Execution, ExecError>, [F192; 2]) {
    let mut pi = [F192::ZERO; 2];
    let mut result = program.execute(pi);
    while let Some(x) = published(&result) {
        let next = (0..2).filter(|&slot| pi[slot] == F192::ZERO).find_map(|slot| {
            let mut candidate = pi;
            candidate[slot] = x;
            let run = program.execute(candidate);
            (published(&run) != Some(x)).then_some((candidate, run))
        });
        match next {
            Some((candidate, run)) => (pi, result) = (candidate, run),
            None => break,
        }
    }
    (result, pi)
}

/// The rate a target proves at: a choice of the input, so every rate is exercised.
pub fn log_inv_rate(source: &mut crate::Source) -> usize {
    source.range(leanvm_core::pcs::MIN_LOG_INV_RATE, leanvm_core::pcs::MAX_LOG_INV_RATE)
}

/// A short name for a prove error, for notes and keys.
pub fn prove_error_kind(e: &ProveError) -> String {
    match e {
        ProveError::InvalidRate { .. } => "InvalidRate".into(),
        ProveError::PublicInputNotDigest => "PublicInputNotDigest".into(),
        ProveError::Execution(e) => format!("Execution/{}", fault_kind(&e.fault)),
        ProveError::UnconstrainedReads(_) => "UnconstrainedReads".into(),
        ProveError::WitnessOutOfRange { .. } => "WitnessOutOfRange".into(),
    }
}

pub fn fault_kind(fault: &Fault) -> &'static str {
    match fault {
        Fault::Conflict { .. } => "Conflict",
        Fault::WildPointer { .. } => "WildPointer",
        Fault::NotInK { .. } => "NotInK",
        Fault::NotAGPower { .. } => "NotAGPower",
        Fault::NotCanonical { .. } => "NotCanonical",
        Fault::BackSolveThroughZero => "BackSolveThroughZero",
        Fault::Witness(_) => "Witness",
        Fault::OutOfMemory => "OutOfMemory",
        Fault::HaltOutsideMain { .. } => "HaltOutsideMain",
        Fault::StepLimit => "StepLimit",
    }
}

/// Prove `program` on `public_input` and verify the proof: an honest run that does not verify is a completeness bug,
/// and a prover error on a run that executed is one too, unless it is the documented refusal of a witness out of range.
pub fn prove_honest(
    program: &Program,
    public_input: [F192; 2],
    log_inv_rate: usize,
    context: &str,
) -> Result<Option<leanvm_core::cpu::Proof>, Finding> {
    match leanvm_core::cpu::prove(program, public_input, log_inv_rate) {
        Ok((proof, _)) => match leanvm_core::cpu::verify(program, &public_input, &proof) {
            Ok(_) => Ok(Some(proof)),
            Err(e) => Err(Finding::high(
                format!("{context}: honest proof rejected: {e:?}"),
                format!("rate {log_inv_rate}, public input {public_input:?}"),
            )),
        },
        Err(ProveError::WitnessOutOfRange { .. }) => Ok(None),
        Err(ProveError::PublicInputNotDigest) if public_input.iter().any(|h| h.c2 != 0) => Ok(None),
        Err(e) => Err(Finding::high(
            format!("{context}: prove refused an executed run: {}", prove_error_kind(&e)),
            format!("{e}"),
        )),
    }
}

#[cfg(test)]
mod tests {
    use primitives::field::F192;

    #[test]
    fn every_annotation_parses() {
        assert!(!super::corpus().is_empty());
    }

    #[test]
    fn the_public_input_is_discovered() {
        let source =
            "def main():\n    a = 5\n    b = a * GEN\n    p = GEN ** 0\n    p[1] = a\n    p[GEN] = b\n    return\n";
        let program = super::compile_source(source).unwrap();
        let (run, pi) = super::execute(&program, None);
        assert!(run.is_ok());
        assert_eq!(
            pi,
            [
                F192::new(5, 0, 0),
                F192::new(5, 0, 0) * F192::from(primitives::field::g_pow(1))
            ]
        );
    }
}
