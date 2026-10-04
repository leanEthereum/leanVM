//! The benchmark harness of the CLI and the `benches/` targets: repeated timing with
//! warmup, cooldown and confidence intervals, the trace tree `--tracing` prints, and
//! Bencher Metric Format output. Nothing the prover or verifier links.

use std::io::{IsTerminal, Write};
use std::time::{Duration, Instant};

mod allocator;
mod trace;
pub use allocator::Jemalloc;
pub use trace::{TraceSuppressed, init_tracing, init_tracing_from_env, suppress_tracing};

/// One line of live progress on stderr.
///
/// Measured pass times accumulate on it while transient status (warming,
/// cooling) is appended after them and erased again, so the passes stay put and
/// the whole run costs one line instead of one per pass.
///
/// Off a terminal it degrades to plain appends with no escape codes, so piped or
/// redirected output stays readable; the transient parts are simply skipped.
struct Progress {
    tty: bool,
    parts: String,
}

const PROGRESS_LABEL: &str = "  passes                      : ";

impl Progress {
    fn new() -> Self {
        Self {
            tty: std::io::stderr().is_terminal(),
            parts: String::new(),
        }
    }

    fn draw(&self, transient: &str) {
        if self.tty {
            eprint!("\r\x1b[2K{PROGRESS_LABEL}{}{transient}", self.parts);
            let _ = std::io::stderr().flush();
        }
    }

    fn status(&self, msg: &str) {
        if self.parts.is_empty() {
            self.draw(msg);
        } else {
            self.draw(&format!("  {msg}"));
        }
    }

    fn push(&mut self, secs: f64) {
        let first = self.parts.is_empty();
        if !first {
            self.parts.push_str("  ");
        }
        self.parts.push_str(&format!("{secs:.3} s"));
        if self.tty {
            self.draw("");
        } else {
            if first {
                eprint!("{PROGRESS_LABEL}");
            } else {
                eprint!("  ");
            }
            eprint!("{secs:.3} s");
            let _ = std::io::stderr().flush();
        }
    }

    fn finish(self) {
        if !self.parts.is_empty() {
            eprintln!();
        } else if self.tty {
            eprint!("\r\x1b[2K");
            let _ = std::io::stderr().flush();
        }
    }
}

/// Mean and 95%-confidence half-width of `samples` (half-width `0` for a
/// single sample). Uses the Student-t critical value for `n - 1` degrees of
/// freedom, so small sample counts are not reported as tighter than they are.
#[must_use]
fn mean_and_ci(samples: &[f64]) -> (f64, f64) {
    let n = samples.len();
    assert!(n > 0, "mean_and_ci needs at least one sample");
    let mean = samples.iter().sum::<f64>() / n as f64;
    if n < 2 {
        return (mean, 0.0);
    }
    let variance = samples.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1) as f64;
    let std_err = (variance / n as f64).sqrt();
    (mean, t_critical_95(n - 1) * std_err)
}

/// Two-sided 95% Student-t critical value, via the standard Cornish-Fisher
/// expansion around the normal quantile (exact to <0.5% for `df >= 3`).
fn t_critical_95(df: usize) -> f64 {
    let z = 1.959_964_f64;
    let df = df as f64;
    z + (z.powi(3) + z) / (4.0 * df) + (5.0 * z.powi(5) + 16.0 * z.powi(3) + 3.0 * z) / (96.0 * df.powi(2))
}

/// Wall-clock samples from one repeated measurement, in seconds.
#[derive(Clone, Debug, Default)]
pub struct Timing {
    samples: Vec<f64>,
}

impl Timing {
    /// Record one measured pass.
    pub fn push(&mut self, secs: f64) {
        self.samples.push(secs);
    }

    #[must_use]
    pub fn samples(&self) -> &[f64] {
        &self.samples
    }

    /// Mean duration in seconds.
    #[must_use]
    pub fn mean(&self) -> f64 {
        mean_and_ci(&self.samples).0
    }

    /// `" ± 0.4%"` when there is more than one sample, else empty: the suffix
    /// appended to every reported duration and throughput.
    #[must_use]
    pub fn spread(&self) -> String {
        let (mean, ci) = mean_and_ci(&self.samples);
        if self.samples.len() < 2 || mean == 0.0 {
            String::new()
        } else {
            format!(" ± {:.1}%", 100.0 * ci / mean)
        }
    }
}

/// How a benchmark repeats and paces its measured passes.
#[derive(Clone, Copy, Debug)]
pub struct Plan {
    /// Measured passes to average; at least 1.
    pub repeat: usize,
    /// Idle time before each measured pass, to let a thermally-limited host
    /// recover its clocks (see the module docs).
    pub cooldown: Duration,
}

impl Default for Plan {
    fn default() -> Self {
        Self {
            repeat: 1,
            cooldown: Duration::ZERO,
        }
    }
}

impl Plan {
    /// A plan of `repeat` measured passes, each preceded by `cooldown_secs` idle.
    #[must_use]
    pub fn new(repeat: usize, cooldown_secs: u64) -> Self {
        assert!(repeat >= 1, "a benchmark needs at least one measured pass");
        Self {
            repeat,
            cooldown: Duration::from_secs(cooldown_secs),
        }
    }

    /// Read the plan from the environment: `BENCH_REPEAT` and `BENCH_COOLDOWN`
    /// (seconds), for the crates' `benches/` targets, which `cargo bench` runs
    /// without a command line of their own. Defaults match the CLI.
    #[must_use]
    pub fn from_env() -> Self {
        Self::new(env_usize("BENCH_REPEAT", 1), env_usize("BENCH_COOLDOWN", 2) as u64)
    }

    /// Run `f` once untimed to warm up, then `self.repeat` measured passes,
    /// keeping the last result and the samples.
    ///
    /// Each call is told whether it is the FINAL measured pass, so a caller can
    /// do once-per-run work in the pass the reported numbers describe. The
    /// benchmarks use it to emit one trace tree instead of one per pass
    /// ([`suppress_tracing`]).
    pub fn warm_then_measure<T>(&self, mut f: impl FnMut(bool) -> T) -> (T, Timing) {
        let progress = Progress::new();
        progress.status("[warming]");
        // Free the warmup's result before the first measured pass allocates, so
        // every measured pass sees the same steady-state footprint.
        drop(f(false));
        self.run(f, progress, true)
    }

    fn cool_down(&self, progress: &Progress) {
        let mut left = self.cooldown;
        while !left.is_zero() {
            progress.status(&format!("[cooldown {}s]", left.as_secs_f64().ceil() as u64));
            let step = Duration::from_secs(1).min(left);
            std::thread::sleep(step);
            left -= step;
        }
    }

    /// Run measured passes without a warmup or per-pass output.
    pub fn measure_quiet<T>(&self, f: impl FnMut(bool) -> T) -> (T, Timing) {
        self.run(f, Progress::new(), false)
    }

    fn run<T>(&self, mut f: impl FnMut(bool) -> T, mut progress: Progress, echo: bool) -> (T, Timing) {
        let mut timing = Timing::default();
        let mut last = None;
        for pass in 0..self.repeat {
            drop(last.take());
            self.cool_down(&progress);
            let t = Instant::now();
            let out = f(pass + 1 == self.repeat);
            let secs = t.elapsed().as_secs_f64();
            timing.push(secs);
            if echo && self.repeat > 1 {
                progress.push(secs);
            }
            last = Some(out);
        }
        progress.finish();
        (last.expect("repeat >= 1"), timing)
    }
}

/// Peak resident set size of this process, in bytes.
///
/// Worth reporting next to any timing here: an allocator that keeps freed pages trades resident
/// memory for the page faults it removes, so a throughput number is only half the
/// picture. Read after a warmup pass, this is the steady-state footprint.
#[must_use]
pub fn peak_rss_bytes() -> u64 {
    // SAFETY: `getrusage` only writes into the `rusage` we hand it, which is
    // zeroed and correctly sized.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) };
    let max = usage.ru_maxrss as u64;
    // `ru_maxrss` is bytes on macOS and KiB on Linux.
    if cfg!(target_os = "macos") { max } else { max * 1024 }
}

/// Read a `usize` benchmark knob from the environment, defaulting when unset.
///
/// # Panics
/// If the variable is set but does not parse.
#[must_use]
pub fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .map(|s| s.parse().unwrap_or_else(|_| panic!("{key} must be an integer")))
        .unwrap_or(default)
}

/// One measure of one benchmark in Bencher Metric Format: a value, and for a
/// timing the fastest and slowest pass.
pub struct Metric {
    value: f64,
    bounds: Option<(f64, f64)>,
}

impl Metric {
    #[must_use]
    pub fn exact(value: usize) -> Self {
        Self {
            value: value as f64,
            bounds: None,
        }
    }

    /// In nanoseconds, the fastest and slowest pass as its bounds.
    #[must_use]
    pub fn nanoseconds(timing: &Timing) -> Self {
        let ns = |secs: f64| (secs * 1e9).round();
        let samples = timing.samples();
        Self {
            value: ns(timing.mean()),
            bounds: Some((
                ns(samples.iter().copied().fold(f64::INFINITY, f64::min)),
                ns(samples.iter().copied().fold(0.0, f64::max)),
            )),
        }
    }
}

/// Benchmarks and their measures as Bencher Metric Format JSON, what CI's comparisons read
/// (`.github/workflows/bench.yml`): <https://bencher.dev/docs/reference/bencher-metric-format/>.
#[must_use]
pub fn bencher_json(report: &[(String, Vec<(&str, Metric)>)]) -> String {
    let benchmarks: Vec<String> = report
        .iter()
        .map(|(name, metrics)| {
            let measures: Vec<String> = metrics
                .iter()
                .map(|(measure, m)| match m.bounds {
                    None => format!("\"{measure}\": {{\"value\": {}}}", m.value),
                    Some((lo, hi)) => format!(
                        "\"{measure}\": {{\"value\": {}, \"lower_value\": {lo}, \"upper_value\": {hi}}}",
                        m.value
                    ),
                })
                .collect();
            format!("  \"{name}\": {{{}}}", measures.join(", "))
        })
        .collect();
    format!("{{\n{}\n}}", benchmarks.join(",\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_edge_cases() {
        let mut t = Timing::default();
        t.push(1.5);
        assert_eq!(t.mean(), 1.5);
        assert_eq!(mean_and_ci(t.samples()).1, 0.0);
        assert_eq!(t.spread(), "");

        let mut t = Timing::default();
        for _ in 0..4 {
            t.push(2.0);
        }
        assert_eq!(t.mean(), 2.0);
        assert_eq!(mean_and_ci(t.samples()).1, 0.0);
        assert_eq!(t.spread(), " ± 0.0%");
    }

    #[test]
    fn ci_shrinks_as_samples_accumulate() {
        let spread = |n: usize| {
            let mut t = Timing::default();
            for i in 0..n {
                t.push(if i.is_multiple_of(2) { 1.0 } else { 1.2 });
            }
            mean_and_ci(t.samples()).1
        };
        assert!(spread(16) < spread(4), "more samples must tighten the interval");
    }

    #[test]
    fn warmup_pass_is_not_measured() {
        let mut calls = 0;
        let mut finals = 0;
        let (last, timing) = Plan::new(3, 0).warm_then_measure(|final_pass| {
            calls += 1;
            finals += usize::from(final_pass);
            calls
        });
        assert_eq!(finals, 1, "exactly one pass is announced as the final one");
        assert_eq!(calls, 4, "one warmup plus three measured passes");
        assert_eq!(last, 4);
        assert_eq!(timing.samples().len(), 3);
    }
}
