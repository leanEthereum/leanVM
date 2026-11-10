//! leanVM's fuzzing targets, and the machinery that runs one case of one.
//!
//! A target is a function of a [`Source`]: it draws a scenario, runs it, and checks an oracle. It returns a
//! [`Finding`] when the oracle fails; a panic is a finding too, which [`run_case`] catches. The `leanvm-fuzz` binary
//! (`bins/fuzz`) runs targets for hours in supervised worker processes, and `fuzz/` drives the same targets under
//! libFuzzer. `README.md` in this crate says what each target attacks.
//!
//! The oracles, by [`Severity`]:
//! - **Critical**: something false is accepted: a verifier passes a forged or tampered proof, a guest accepts a forged
//!   witness or an invalid child.
//! - **High**: something true is refused or computed wrong: an honest proof fails, a program miscompiles, two
//!   implementations of one function disagree, a proof depends on the thread count.
//! - **Medium**: a crash, hang or unbounded allocation where the input deserves an error: a verifier, a decoder, the
//!   public API.
//! - **Low**: a panic on a path documented to panic on bad input (the compiler on a malformed program), kept for triage.

pub mod findings;
pub mod mutate_proof;
pub mod programs;
pub mod resources;
mod selftest;
pub mod source;
pub mod targets;

pub use findings::{Finding, Severity};
pub use source::{Rng, Source};

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;

/// What a case may use beside its input.
pub struct Ctx {
    /// A directory that persists across cases and workers of one campaign: caches of expensive fixtures (honest
    /// proofs, signer sets), cross-process oracles.
    pub dir: PathBuf,
    /// How hard a target may go: `0` is a smoke test, `1` the default, `2` lets the heavy paths (full proofs of
    /// guests, large programs) run on every case rather than a sample.
    pub depth: u8,
    notes: RefCell<BTreeSet<String>>,
}

impl Ctx {
    pub fn new(dir: PathBuf, depth: u8) -> Self {
        Self {
            dir,
            depth,
            notes: RefCell::new(BTreeSet::new()),
        }
    }

    /// Record a behaviour this case reached: which mutation, which error, which branch of a scenario. A case that
    /// reaches a note no earlier case of its target reached joins the corpus, and the campaign's statistics count
    /// them, so notes are the stable-toolchain fuzzer's coverage.
    pub fn note(&self, note: impl Into<String>) {
        self.notes.borrow_mut().insert(note.into());
    }

    pub fn take_notes(&self) -> BTreeSet<String> {
        std::mem::take(&mut self.notes.borrow_mut())
    }

    /// A file under [`Self::dir`], its parent created.
    pub fn path(&self, name: &str) -> PathBuf {
        let path = self.dir.join(name);
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        path
    }
}

/// How long one case may take before the supervisor calls it a hang, and how the scheduler weighs the target.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cost {
    /// Microseconds to milliseconds: differential kernels, decoders.
    Cheap,
    /// Up to seconds: compiling and executing programs, small proofs.
    Medium,
    /// Up to minutes: proofs of the guest, aggregation.
    Heavy,
}

impl Cost {
    pub fn timeout_secs(self) -> u64 {
        match self {
            Cost::Cheap => 60,
            Cost::Medium => 600,
            Cost::Heavy => 3600,
        }
    }
}

pub type Outcome = Result<(), Finding>;

pub struct Target {
    pub name: &'static str,
    /// One line: what the target attacks and what its oracle is.
    pub about: &'static str,
    pub cost: Cost,
    pub run: fn(&mut Source, &Ctx) -> Outcome,
}

/// Every target, in a fixed order.
pub fn all_targets() -> Vec<&'static Target> {
    let mut all = targets::all();
    if std::env::var_os("LEANVM_FUZZ_SELFTEST").is_some() {
        all.extend(selftest::TARGETS);
    }
    all
}

pub fn find_target(name: &str) -> Option<&'static Target> {
    all_targets().into_iter().find(|t| t.name == name)
}

/// What one case did.
pub struct CaseResult {
    pub finding: Option<Finding>,
    pub notes: BTreeSet<String>,
    /// The input bytes the case consumed, for the corpus.
    pub consumed: Vec<u8>,
    /// Its peak heap and time.
    pub usage: resources::Usage,
}

/// The most a cheap case may hold at once: past it, an input made a kernel or a decoder allocate without bound.
const CHEAP_PEAK_BYTES: usize = 1 << 32;

/// The last panic in the process, from any thread: its message and where it was raised, which the hook records
/// before unwinding. Process-wide because a panic in a thread-pool job is raised on a worker thread and reaches the
/// case's thread only as a payload. A worker runs one case at a time.
static PANIC: std::sync::Mutex<Option<(String, String)>> = std::sync::Mutex::new(None);

fn take_panic() -> Option<(String, String)> {
    PANIC.lock().unwrap_or_else(|e| e.into_inner()).take()
}

/// Record panics for the case instead of printing them, keeping the location for the finding's key. Idempotent.
pub fn install_panic_hook() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let default = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let message = match (
                info.payload().downcast_ref::<&str>(),
                info.payload().downcast_ref::<String>(),
            ) {
                (Some(s), _) => s.to_string(),
                (_, Some(s)) => s.clone(),
                _ => "<non-string panic>".to_string(),
            };
            let location = info
                .location()
                .map_or("<unknown>".to_string(), |l| format!("{}:{}", l.file(), l.line()));
            let mut last = PANIC.lock().unwrap_or_else(|e| e.into_inner());
            // The first panic of a case is the cause; a pool re-raising it on the dispatcher is not.
            if last.is_none() {
                *last = Some((message, location));
            }
            if std::env::var_os("LEANVM_FUZZ_SHOW_PANICS").is_some() {
                default(info);
            }
        }));
    });
}

/// Run one case of `target` on `source`, turning a panic into a [`Finding`] keyed by where it was raised.
pub fn run_case(target: &Target, source: &mut Source, ctx: &Ctx) -> CaseResult {
    install_panic_hook();
    take_panic();
    let (outcome, usage) = resources::measure(|| catch_unwind(AssertUnwindSafe(|| (target.run)(source, ctx))));
    // A hook a target armed and never fired must not leak into the next case.
    targets::disarm_all();
    let mut finding = match outcome {
        Ok(Ok(())) => None,
        Ok(Err(finding)) => Some(finding),
        Err(_) => {
            let (message, location) = take_panic().unwrap_or_else(|| ("<unknown panic>".into(), "<unknown>".into()));
            Some(Finding::panic(&message, &location))
        }
    };
    if resources::installed() {
        // A new peak bucket is new behaviour: the corpus keeps the case, and its mutations climb toward costlier inputs.
        ctx.note(format!("peak heap 2^{}", usage.peak_bucket()));
        if finding.is_none() && target.cost == Cost::Cheap && usage.peak_bytes > CHEAP_PEAK_BYTES {
            finding = Some(Finding::medium(
                format!(
                    "resource: a cheap case peaked past 2^{} bytes",
                    CHEAP_PEAK_BYTES.trailing_zeros()
                ),
                format!("{} bytes in {:?}", usage.peak_bytes, usage.elapsed),
            ));
        }
    }
    CaseResult {
        finding,
        notes: ctx.take_notes(),
        consumed: source.consumed(),
        usage,
    }
}

/// libFuzzer's entry point: one case on `data`, on a thread with a deep stack. A finding at or above
/// `LEANVM_FUZZ_MIN_SEVERITY` (`medium` by default; `low` to keep the compiler's documented panics too) is raised as a
/// panic, which libFuzzer reports as a crash and keeps the input of.
pub fn libfuzzer_case(name: &'static str, data: &[u8]) {
    let threshold = std::env::var("LEANVM_FUZZ_MIN_SEVERITY")
        .ok()
        .and_then(|s| Severity::parse(&s))
        .unwrap_or(Severity::Medium);
    let data = data.to_vec();
    let finding = std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(move || {
            thread_local! {
                static CTX: Ctx = Ctx::new(
                    std::env::var_os("LEANVM_FUZZ_DIR").map_or_else(|| std::env::temp_dir().join("leanvm-fuzz"), PathBuf::from),
                    std::env::var("LEANVM_FUZZ_DEPTH").ok().and_then(|d| d.parse().ok()).unwrap_or(0),
                );
            }
            let target = find_target(name).unwrap_or_else(|| panic!("no fuzz target `{name}`"));
            CTX.with(|ctx| run_case(target, &mut Source::from_bytes(&data), ctx).finding)
        })
        .expect("spawn")
        .join()
        .expect("run_case catches panics");
    if let Some(finding) = finding.filter(|f| f.severity <= threshold) {
        panic!("{finding}");
    }
}

/// Run `f`, returning a panic as its message and location instead of unwinding: for a target that calls code
/// documented to panic (the compiler on a malformed program) and judges the panic itself.
pub fn catch<T>(f: impl FnOnce() -> T) -> Result<T, (String, String)> {
    install_panic_hook();
    take_panic();
    catch_unwind(AssertUnwindSafe(f))
        .map_err(|_| take_panic().unwrap_or_else(|| ("<unknown panic>".into(), "<unknown>".into())))
}
