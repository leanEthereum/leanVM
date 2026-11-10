//! The campaign: `jobs` worker processes at a time, each one target for one time slice, for as long as asked.
//!
//! Isolation is the point of the processes: a stack overflow, an abort, an allocation failure, a deadlock in the
//! thread pool or a runaway allocation kills or stalls one worker, which the supervisor records as a finding against
//! the case the worker announced, and replaces.

use crate::store::{CaseInput, Store};
use fuzz::{Finding, Severity, Target};
use std::collections::BTreeMap;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

pub struct CampaignArgs {
    pub targets: Vec<&'static Target>,
    pub jobs: usize,
    pub duration: Option<Duration>,
    pub seed: u64,
    pub depth: u8,
    pub slice: Duration,
    /// `None` draws each worker's `LEANVM_NUM_THREADS`, so proofs run at many thread counts.
    pub threads: Option<usize>,
    pub mem_limit_mb: Option<u64>,
    pub timeout_scale: f64,
    pub weights: BTreeMap<String, u32>,
}

#[derive(Default, Clone)]
struct TargetStats {
    cases: u64,
    micros: u128,
    findings: BTreeMap<&'static str, u64>,
    notes: u64,
    crashes: u64,
    hangs: u64,
    workers: u64,
    /// The largest peak heap of any case, in bytes.
    peak: u64,
}

/// How much worker time a new note is worth in power scheduling, in seconds, and the most a target's weight grows.
const NOTE_VALUE: f64 = 60.0;
const MAX_BOOST: f64 = 5.0;

struct Worker {
    id: String,
    target: &'static Target,
    child: Child,
    started: Instant,
    case_started: Option<Instant>,
    in_case: bool,
    threads: usize,
    last_rss_check: Instant,
}

enum Event {
    Line(String, String),
    Closed,
}

fn spawn_reader(id: String, stdout: std::process::ChildStdout, tx: Sender<Event>) {
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines().map_while(Result::ok) {
            if let Some(rest) = line.strip_prefix("@@FUZZ ") {
                let _ = tx.send(Event::Line(id.clone(), rest.to_string()));
            }
        }
        let _ = tx.send(Event::Closed);
    });
}

/// Resident memory of `pid`, in MiB.
fn rss_mb(pid: u32) -> Option<u64> {
    if let Ok(status) = std::fs::read_to_string(format!("/proc/{pid}/status")) {
        let kb: u64 = status
            .lines()
            .find_map(|l| l.strip_prefix("VmRSS:"))?
            .trim()
            .trim_end_matches("kB")
            .trim()
            .parse()
            .ok()?;
        return Some(kb / 1024);
    }
    let out = Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout)
        .trim()
        .parse::<u64>()
        .ok()
        .map(|kb| kb / 1024)
}

/// A stable key for a dead worker, from the end of its stderr: the panic location, the kind of abort.
fn crash_key(stderr: &str, status: &str) -> String {
    let lines: Vec<&str> = stderr.lines().collect();
    if lines.iter().any(|l| l.contains("has overflowed its stack")) {
        return "stack overflow".into();
    }
    if let Some(l) = lines.iter().rev().find(|l| l.contains("memory allocation of")) {
        return format!("allocation failure: {}", fuzz::findings::normalize(l));
    }
    if let Some(i) = lines.iter().rposition(|l| l.contains("panicked at")) {
        let location = lines[i]
            .split("panicked at")
            .nth(1)
            .unwrap_or("")
            .trim()
            .trim_end_matches(':');
        let message = lines.get(i + 1).copied().unwrap_or("");
        return format!(
            "abort after panic at {location}: {}",
            fuzz::findings::normalize(message)
        );
    }
    format!("died: {status}")
}

fn tail(path: &PathBuf, max: usize) -> String {
    let text = std::fs::read_to_string(path).unwrap_or_default();
    let start = text.len().saturating_sub(max);
    let start = (start..text.len())
        .find(|&i| text.is_char_boundary(i))
        .unwrap_or(text.len());
    text[start..].to_string()
}

pub fn run(store: &Store, args: CampaignArgs) {
    let exe = std::env::current_exe().expect("own executable");
    let started = Instant::now();
    let (tx, rx): (Sender<Event>, Receiver<Event>) = channel();
    let mut workers: Vec<Worker> = Vec::new();
    let mut stats: BTreeMap<&'static str, TargetStats> =
        args.targets.iter().map(|t| (t.name, Default::default())).collect();
    let mut seed = fuzz::Rng::new(args.seed);
    let mut spawned = 0u64;
    let mut last_report = Instant::now();
    let ncpu = std::thread::available_parallelism().map_or(1, |n| n.get());
    let weights: Vec<u32> = args
        .targets
        .iter()
        .map(|t| *args.weights.get(t.name).unwrap_or(&1))
        .collect();
    // Time share per target: the target with the least worker time so far, scaled by its weight, goes next.
    let mut busy_secs: BTreeMap<&'static str, f64> = BTreeMap::new();
    let mut stopping = false;

    loop {
        if args.duration.is_some_and(|d| started.elapsed() > d) && !stopping {
            stopping = true;
            for w in &mut workers {
                let _ = w.child.kill();
            }
        }
        while !stopping && workers.len() < args.jobs {
            // Power scheduling: the target with the least worker time per unit of weight goes next, and a target whose
            // time keeps reaching new notes weighs up to `MAX_BOOST` times more, so a long campaign drifts toward the
            // targets still discovering behaviour while every target keeps at least its base share.
            let weight = |k: usize, t: &Target| {
                let busy = busy_secs.get(t.name).copied().unwrap_or(0.0);
                let notes = stats.get(t.name).map_or(0, |s| s.notes) as f64;
                let boost = if busy > 0.0 {
                    (1.0 + NOTE_VALUE * notes / busy).min(MAX_BOOST)
                } else {
                    1.0
                };
                weights[k].max(1) as f64 * boost
            };
            let (_, target) = args
                .targets
                .iter()
                .enumerate()
                .min_by(|(i, a), (j, b)| {
                    let share = |k: usize, t: &Target| busy_secs.get(t.name).copied().unwrap_or(0.0) / weight(k, t);
                    share(*i, a).total_cmp(&share(*j, b))
                })
                .expect("at least one target");
            let id = format!("w{spawned}");
            spawned += 1;
            let threads = args.threads.unwrap_or_else(|| {
                let fair = (ncpu / args.jobs).max(1);
                [1, 2, 3, fair, fair, fair][seed.below(6) as usize]
            });
            let stderr = std::fs::File::create(store.worker_file(&id, "stderr")).expect("worker stderr");
            let worker_seed = seed.next_u64();
            let mut child = Command::new(&exe)
                .arg("worker")
                .args(["--target", target.name, "--id", &id, "--out"])
                .arg(&store.out)
                .args(["--seed", &worker_seed.to_string(), "--depth", &args.depth.to_string()])
                .args(["--max-secs", &args.slice.as_secs().to_string()])
                .env("LEANVM_NUM_THREADS", threads.to_string())
                .env("RUST_BACKTRACE", "1")
                .stdout(Stdio::piped())
                .stderr(stderr)
                .spawn()
                .expect("spawn worker");
            spawn_reader(id.clone(), child.stdout.take().unwrap(), tx.clone());
            stats.get_mut(target.name).unwrap().workers += 1;
            *busy_secs.entry(target.name).or_default() += 1.0;
            workers.push(Worker {
                id,
                target,
                child,
                started: Instant::now(),
                case_started: None,
                in_case: false,
                threads,
                last_rss_check: Instant::now(),
            });
        }
        if workers.is_empty() {
            break;
        }

        // Events, for at most a second before the workers are checked again.
        let tick = Instant::now();
        while let Ok(event) = rx.recv_timeout(Duration::from_millis(200)) {
            match event {
                Event::Line(id, line) => {
                    let Some(w) = workers.iter_mut().find(|w| w.id == id) else {
                        continue;
                    };
                    let s = stats.get_mut(w.target.name).unwrap();
                    let mut parts = line.split_whitespace();
                    match parts.next() {
                        Some("START") => {
                            w.case_started = Some(Instant::now());
                            w.in_case = true;
                        }
                        Some("END") => {
                            w.in_case = false;
                            s.cases += 1;
                            let _n = parts.next();
                            s.micros += parts.next().and_then(|m| m.parse::<u128>().ok()).unwrap_or(0);
                            if let Some(sev) = parts.next().and_then(Severity::parse) {
                                *s.findings.entry(sev.as_str()).or_default() += 1;
                            }
                            if let Some(peak) = parts.next().and_then(|p| p.parse::<u64>().ok()) {
                                s.peak = s.peak.max(peak);
                            }
                        }
                        Some("NOTE") => s.notes += parts.next().and_then(|c| c.parse().ok()).unwrap_or(0),
                        _ => {}
                    }
                }
                Event::Closed => {}
            }
            if tick.elapsed() > Duration::from_secs(1) {
                break;
            }
        }

        // Dead, hung and bloated workers.
        let mut i = 0;
        while i < workers.len() {
            let w = &mut workers[i];
            let timeout = Duration::from_secs_f64(w.target.cost.timeout_secs() as f64 * args.timeout_scale);
            let mut verdict: Option<(String, String)> = None;
            match w.child.try_wait() {
                Ok(Some(status)) => {
                    if !stopping && (w.in_case || !status.success()) {
                        let describe = describe_status(&status);
                        let stderr = tail(&store.worker_file(&w.id, "stderr"), 6000);
                        verdict = Some((
                            crash_key(&stderr, &describe),
                            format!("worker {describe}\n\nstderr tail:\n{stderr}"),
                        ));
                        stats.get_mut(w.target.name).unwrap().crashes += 1;
                    }
                    *busy_secs.entry(w.target.name).or_default() += w.started.elapsed().as_secs_f64();
                    if let Some((key, detail)) = verdict {
                        record_dead(store, w, Finding::medium(key, detail));
                    }
                    let _ = std::fs::remove_file(store.worker_file(&w.id, "case"));
                    workers.remove(i);
                    continue;
                }
                Ok(None) => {}
                Err(_) => {}
            }
            if w.in_case && w.case_started.is_some_and(|t| t.elapsed() > timeout) {
                verdict = Some((
                    format!("hang: one case over {}s", timeout.as_secs()),
                    format!(
                        "killed after {}s in one case, LEANVM_NUM_THREADS={}",
                        timeout.as_secs(),
                        w.threads
                    ),
                ));
                stats.get_mut(w.target.name).unwrap().hangs += 1;
            } else if let Some(limit) = args.mem_limit_mb
                && w.last_rss_check.elapsed() > Duration::from_secs(2)
            {
                w.last_rss_check = Instant::now();
                if let Some(rss) = rss_mb(w.child.id())
                    && rss > limit
                {
                    verdict = Some((
                        format!("memory: resident set over {limit} MiB"),
                        format!("killed at {rss} MiB resident, LEANVM_NUM_THREADS={}", w.threads),
                    ));
                }
            }
            if let Some((key, detail)) = verdict {
                let _ = w.child.kill();
                let _ = w.child.wait();
                record_dead(store, w, Finding::medium(key, detail));
                *busy_secs.entry(w.target.name).or_default() += w.started.elapsed().as_secs_f64();
                workers.remove(i);
                continue;
            }
            i += 1;
        }

        if last_report.elapsed() > Duration::from_secs(10) {
            last_report = Instant::now();
            report(store, &stats, started.elapsed(), workers.len());
        }
    }
    report(store, &stats, started.elapsed(), 0);
}

fn describe_status(status: &std::process::ExitStatus) -> String {
    use std::os::unix::process::ExitStatusExt;
    match (status.code(), status.signal()) {
        (Some(code), _) => format!("exited with code {code}"),
        (_, Some(signal)) => format!("killed by signal {signal}"),
        _ => "died".into(),
    }
}

fn record_dead(store: &Store, w: &Worker, finding: Finding) {
    let case = std::fs::read(store.worker_file(&w.id, "case"))
        .map(|b| CaseInput::decode(&b))
        .unwrap_or(CaseInput {
            prefix: Vec::new(),
            tail_seed: None,
        });
    if store.record(w.target.name, &finding, &case) {
        eprintln!("NEW [{}] {}: {}", finding.severity.as_str(), w.target.name, finding.key);
    }
}

fn report(store: &Store, stats: &BTreeMap<&'static str, TargetStats>, elapsed: Duration, running: usize) {
    let mut table = format!(
        "elapsed {}s, {running} workers running\n{:<28} {:>10} {:>10} {:>7} {:>9} {:>6} {:>6} {:>6}  findings\n",
        elapsed.as_secs(),
        "target",
        "cases",
        "cases/s",
        "notes",
        "peak MiB",
        "crash",
        "hang",
        "spawns"
    );
    for (name, s) in stats {
        let rate = if s.micros > 0 {
            s.cases as f64 / (s.micros as f64 / 1e6)
        } else {
            0.0
        };
        let findings: Vec<String> = s.findings.iter().map(|(k, v)| format!("{k}:{v}")).collect();
        table += &format!(
            "{name:<28} {:>10} {:>10.1} {:>7} {:>9} {:>6} {:>6} {:>6}  {}\n",
            s.cases,
            rate,
            s.notes,
            s.peak >> 20,
            s.crashes,
            s.hangs,
            s.workers,
            findings.join(" ")
        );
    }
    let distinct = store.findings();
    let mut by_severity: BTreeMap<Severity, usize> = BTreeMap::new();
    for (severity, ..) in &distinct {
        *by_severity.entry(*severity).or_default() += 1;
    }
    let summary: Vec<String> = by_severity.iter().map(|(s, n)| format!("{} {n}", s.as_str())).collect();
    table += &format!(
        "distinct findings: {}\n",
        if summary.is_empty() {
            "none".into()
        } else {
            summary.join(", ")
        }
    );
    let _ = std::fs::write(store.out.join("stats.txt"), &table);
    eprintln!("{table}");
}
