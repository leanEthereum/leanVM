//! `cargo leanvm-fuzz`: run a fuzzing campaign over leanVM, and triage what it finds. See `crates/fuzz/README.md`.

// The system allocator, counted: each case's peak heap is measured (`fuzz::resources`). Not `bench::Jemalloc`, which
// never returns freed pages, so a worker's resident set would only grow and `--mem-limit-mb` would blame whichever
// case ran when it crossed the limit.
#[global_allocator]
static ALLOCATOR: fuzz::resources::Counting = fuzz::resources::Counting;

mod store;
mod supervisor;
mod worker;

use clap::{Parser, Subcommand};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Duration;
use store::{CaseInput, Store};

#[derive(Parser)]
#[command(about = "Fuzz leanVM: supervised workers, deduplicated findings, replayable cases")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run a campaign until `--duration` (forever by default), resuming the corpus and findings in `--out`.
    Run {
        /// Comma-separated target names or prefixes (`soundness`, `dsl-`), all by default.
        #[arg(long, default_value = "")]
        targets: String,
        /// Comma-separated target names or prefixes to leave out.
        #[arg(long, default_value = "")]
        exclude: String,
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        /// Concurrent worker processes. Default: a quarter of the logical CPUs, since proofs use the pool.
        #[arg(long)]
        jobs: Option<usize>,
        /// `30m`, `8h`, `2d`; forever if omitted.
        #[arg(long)]
        duration: Option<String>,
        /// Base seed; random if omitted (it is logged in `<out>/campaign.txt`).
        #[arg(long)]
        seed: Option<u64>,
        /// 0 smoke, 1 default, 2 heavy paths on every case.
        #[arg(long, default_value_t = 1)]
        depth: u8,
        /// Seconds a worker runs one target before the supervisor rotates it.
        #[arg(long, default_value_t = 600)]
        slice: u64,
        /// Each worker's `LEANVM_NUM_THREADS`; drawn per worker if omitted.
        #[arg(long)]
        threads: Option<usize>,
        /// Kill and report a worker whose resident set exceeds this many MiB.
        #[arg(long)]
        mem_limit_mb: Option<u64>,
        /// Multiply every target's per-case timeout.
        #[arg(long, default_value_t = 1.0)]
        timeout_scale: f64,
        /// `target=weight,...`: a larger share of worker time for some targets (default weight 1).
        #[arg(long, default_value = "")]
        weights: String,
    },
    /// List the targets.
    List,
    /// Replay one case in this process, loudly.
    Repro {
        target: String,
        /// A case file from `findings/`, a corpus entry or a libFuzzer artifact.
        #[arg(long)]
        input: Option<PathBuf>,
        /// A fresh case from this tail seed.
        #[arg(long)]
        seed: Option<u64>,
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        #[arg(long, default_value_t = 1)]
        depth: u8,
        /// Print only the finding's key (for `minimize`).
        #[arg(long)]
        quiet: bool,
    },
    /// Shrink a case's input while it still reproduces the same finding key.
    Minimize {
        target: String,
        #[arg(long)]
        input: PathBuf,
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        /// Where to write the smallest input (default: next to `--input`, `.min` appended).
        #[arg(long)]
        output: Option<PathBuf>,
    },
    /// Check every hand-written corpus program against its annotations, once each, and say how long it took.
    Programs {
        /// Only programs whose name contains this.
        #[arg(long, default_value = "")]
        filter: String,
        /// The case seed each check draws its rate and statement change from.
        #[arg(long, default_value_t = 0)]
        seed: u64,
        /// 2 proves `# fuzz: slow` programs too.
        #[arg(long, default_value_t = 1)]
        depth: u8,
        /// Check these files instead of the embedded corpus: a program being written, before it joins `programs/`.
        #[arg(long)]
        file: Vec<PathBuf>,
    },
    /// Replay a campaign against this build: every recorded finding (fixed, still there, or changed?) and every corpus
    /// entry (a regression gate: each input that ever reached new behaviour, run again).
    Replay {
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        /// Comma-separated target names or prefixes, all by default.
        #[arg(long, default_value = "")]
        targets: String,
        /// Only the recorded findings.
        #[arg(long)]
        findings_only: bool,
        /// Only the corpus.
        #[arg(long)]
        corpus_only: bool,
        /// Exit with status 1 if a finding at least this severe reproduces or appears (`critical`, `high`, `medium`, `low`).
        #[arg(long, default_value = "medium")]
        fail_on: String,
    },
    /// The guest's kill map: which checks in `lean_ethereum.py` some forged witness or child has made fail in a campaign,
    /// and which never have. A check that never fires is a blind spot of the fuzzer or a check nothing can reach.
    GuestCoverage {
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        /// Also list the checks that fired, with the targets whose cases fired them.
        #[arg(long)]
        all: bool,
    },
    /// Prove every fast provable corpus program and print digests of its bytecode and proof bytes. Proofs are
    /// deterministic, so two machines (NEON, AVX2, AVX-512) or two commits must print the same lines: a difference is
    /// a kernel that computes differently, or a change to the protocol that every verifier has to follow.
    Fingerprint {
        /// Only programs whose name contains this.
        #[arg(long, default_value = "")]
        filter: String,
        /// Comma-separated `log_inv_rate`s.
        #[arg(long, default_value = "1,2")]
        rates: String,
        /// Compare with a file an earlier run wrote, exiting with status 1 on any difference.
        #[arg(long)]
        compare: Option<PathBuf>,
    },
    /// Summarize the findings of a campaign directory.
    Report {
        #[arg(long, default_value = "fuzz-out")]
        out: PathBuf,
        /// Exit with status 1 if any unsuppressed finding is at least this severe (`critical`, `high`, `medium`, `low`).
        #[arg(long)]
        fail_on: Option<String>,
    },
    /// One worker process (the supervisor spawns these).
    #[command(hide = true)]
    Worker {
        #[arg(long)]
        target: String,
        #[arg(long)]
        id: String,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        seed: u64,
        #[arg(long, default_value_t = 1)]
        depth: u8,
        #[arg(long, default_value_t = 600)]
        max_secs: u64,
        #[arg(long, default_value_t = u64::MAX)]
        max_cases: u64,
    },
}

fn parse_duration(s: &str) -> Duration {
    let (num, unit) = s.split_at(s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len()));
    let n: u64 = num.parse().unwrap_or_else(|_| panic!("bad duration `{s}`"));
    Duration::from_secs(
        n * match unit {
            "" | "s" => 1,
            "m" => 60,
            "h" => 3600,
            "d" => 86400,
            _ => panic!("bad duration unit in `{s}`"),
        },
    )
}

fn select(spec: &str, exclude: &str) -> Vec<&'static fuzz::Target> {
    let matches = |list: &str, name: &str| {
        list.split(',')
            .filter(|p| !p.is_empty())
            .any(|p| name.starts_with(p.trim()))
    };
    let chosen: Vec<_> = fuzz::all_targets()
        .into_iter()
        .filter(|t| spec.is_empty() || matches(spec, t.name))
        .filter(|t| !matches(exclude, t.name))
        .collect();
    assert!(
        !chosen.is_empty(),
        "no target matches `{spec}`; see `cargo leanvm-fuzz list`"
    );
    chosen
}

fn target(name: &str) -> &'static fuzz::Target {
    fuzz::find_target(name).unwrap_or_else(|| panic!("no target `{name}`; see `cargo leanvm-fuzz list`"))
}

/// Run `f` on a thread with a stack deep enough for the compiler on adversarial programs.
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("spawn")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::Run {
            targets,
            exclude,
            out,
            jobs,
            duration,
            seed,
            depth,
            slice,
            threads,
            mem_limit_mb,
            timeout_scale,
            weights,
        } => {
            let store = Store::new(&out);
            let seed = seed.unwrap_or_else(|| {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64
            });
            let jobs = jobs.unwrap_or_else(|| (std::thread::available_parallelism().map_or(4, |n| n.get()) / 4).max(1));
            let weights: BTreeMap<String, u32> = weights
                .split(',')
                .filter_map(|kv| kv.split_once('='))
                .map(|(k, v)| (k.trim().to_string(), v.trim().parse().expect("weight")))
                .collect();
            let chosen = select(&targets, &exclude);
            let line = format!(
                "start seed={seed} jobs={jobs} depth={depth} targets={}\n",
                chosen.iter().map(|t| t.name).collect::<Vec<_>>().join(",")
            );
            eprint!("{line}");
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(out.join("campaign.txt"))
                .and_then(|mut f| std::io::Write::write_all(&mut f, line.as_bytes()));
            supervisor::run(
                &store,
                supervisor::CampaignArgs {
                    targets: chosen,
                    jobs,
                    duration: duration.as_deref().map(parse_duration),
                    seed,
                    depth,
                    slice: Duration::from_secs(slice),
                    threads,
                    mem_limit_mb,
                    timeout_scale,
                    weights,
                },
            );
            print_report(&store);
        }
        Command::List => {
            for t in fuzz::all_targets() {
                println!(
                    "{:<30} {:<7} {}",
                    t.name,
                    format!("{:?}", t.cost).to_lowercase(),
                    t.about
                );
            }
        }
        Command::Repro {
            target: name,
            input,
            seed,
            out,
            depth,
            quiet,
        } => {
            let t = target(&name);
            let case = match (input, seed) {
                (Some(path), _) => CaseInput::decode(&std::fs::read(&path).expect("read input")),
                (None, Some(seed)) => CaseInput {
                    prefix: Vec::new(),
                    tail_seed: Some(seed),
                },
                (None, None) => panic!("give --input or --seed"),
            };
            if !quiet {
                // SAFETY: single threaded here, before any worker thread exists.
                unsafe { std::env::set_var("LEANVM_FUZZ_SHOW_PANICS", "1") };
            }
            let store = Store::new(&out);
            let result = with_big_stack(move || {
                let ctx = fuzz::Ctx::new(store.cache_dir(), depth);
                fuzz::run_case(t, &mut case.source(), &ctx)
            });
            match (&result.finding, quiet) {
                (Some(f), true) => println!("{}", f.key),
                (Some(f), false) => {
                    println!("{f}");
                    println!("notes: {:?}", result.notes);
                    std::process::exit(1);
                }
                (None, true) => println!("-"),
                (None, false) => println!("no finding; notes: {:?}", result.notes),
            }
        }
        Command::Replay {
            out,
            targets,
            findings_only,
            corpus_only,
            fail_on,
        } => {
            let level = fuzz::Severity::parse(&fail_on).expect("a severity: critical, high, medium or low");
            let store = Store::new(&out);
            let chosen = select(&targets, "");
            let mut failing = false;
            if !corpus_only {
                failing |= replay_findings(&store, &chosen, level);
            }
            if !findings_only {
                leanvm_core::init_prover();
                failing |= with_big_stack(move || replay_corpus(&store, &chosen, level));
            }
            if failing {
                std::process::exit(1);
            }
        }
        Command::Minimize {
            target: name,
            input,
            out,
            output,
        } => minimize(&name, &input, &out, output),
        Command::GuestCoverage { out, all } => guest_coverage(&Store::new(&out), all),
        #[cfg(not(feature = "dsl"))]
        Command::Fingerprint { .. } => panic!("`fingerprint` needs the `dsl` feature"),
        #[cfg(feature = "dsl")]
        Command::Fingerprint { filter, rates, compare } => {
            leanvm_core::init_prover();
            let rates: Vec<usize> = rates.split(',').map(|r| r.trim().parse().expect("a rate")).collect();
            let lines = with_big_stack(move || fingerprint(&filter, &rates));
            for line in &lines {
                println!("{line}");
            }
            if let Some(path) = compare {
                let before = std::fs::read_to_string(&path).expect("read the earlier fingerprint");
                let before: std::collections::BTreeSet<&str> = before.lines().collect();
                let now: std::collections::BTreeSet<&str> = lines.iter().map(String::as_str).collect();
                let (gone, new): (Vec<_>, Vec<_>) =
                    (before.difference(&now).collect(), now.difference(&before).collect());
                for line in &gone {
                    eprintln!("- {line}");
                }
                for line in &new {
                    eprintln!("+ {line}");
                }
                if !gone.is_empty() || !new.is_empty() {
                    eprintln!("{} line(s) differ from {}", gone.len() + new.len(), path.display());
                    std::process::exit(1);
                }
                eprintln!("identical to {}", path.display());
            }
        }
        Command::Report { out, fail_on } => {
            let store = Store::new(&out);
            print_report(&store);
            if let Some(level) = fail_on {
                let level = fuzz::Severity::parse(&level).expect("a severity: critical, high, medium or low");
                if store.findings().iter().any(|(severity, ..)| *severity <= level) {
                    std::process::exit(1);
                }
            }
        }
        #[cfg(not(feature = "dsl"))]
        Command::Programs { .. } => panic!("`programs` needs the `dsl` feature"),
        #[cfg(feature = "dsl")]
        Command::Programs {
            filter,
            seed,
            depth,
            file,
        } => {
            leanvm_core::init_prover();
            let failed = with_big_stack(move || {
                let ctx = fuzz::Ctx::new(std::env::temp_dir().join("leanvm-fuzz-programs"), depth);
                let mut failed = 0;
                let specs: Vec<fuzz::programs::Spec> = if file.is_empty() {
                    fuzz::programs::corpus().to_vec()
                } else {
                    file.iter()
                        .map(|path| {
                            let name: &'static str = path.display().to_string().leak();
                            let source: &'static str = std::fs::read_to_string(path).expect("read the program").leak();
                            fuzz::programs::Spec::parse(name, source).unwrap_or_else(|e| panic!("{e}"))
                        })
                        .collect()
                };
                for spec in specs.iter().filter(|s| s.name.contains(filter.as_str())) {
                    let t = std::time::Instant::now();
                    let mut source = fuzz::Source::from_seed(seed);
                    let result = fuzz::catch(|| fuzz::targets::dsl::corpus::check(spec, &mut source, &ctx));
                    let verdict = match result {
                        Ok(Ok(())) => "ok".to_string(),
                        Ok(Err(f)) => {
                            failed += 1;
                            format!("FINDING {f}")
                        }
                        Err((message, location)) => {
                            failed += 1;
                            format!("PANIC at {location}: {message}")
                        }
                    };
                    println!("{:<50} {:>8.2}s  {verdict}", spec.name, t.elapsed().as_secs_f64());
                }
                failed
            });
            if failed > 0 {
                eprintln!("{failed} program(s) failed");
                std::process::exit(1);
            }
        }
        Command::Worker {
            target: name,
            id,
            out,
            seed,
            depth,
            max_secs,
            max_cases,
        } => {
            leanvm_core::init_prover();
            let t = target(&name);
            with_big_stack(move || {
                worker::run(
                    &Store::new(&out),
                    worker::WorkerArgs {
                        target: t,
                        id,
                        seed,
                        depth,
                        max_cases,
                        max_time: Duration::from_secs(max_secs),
                    },
                )
            });
        }
    }
}

fn print_report(store: &Store) {
    let findings = store.findings();
    if findings.is_empty() {
        println!("no findings in {}", store.out.display());
        return;
    }
    for (severity, target, key, hits, dir) in findings {
        println!(
            "[{:<8}] {target:<28} x{hits:<6} {key}\n           {}",
            severity.as_str(),
            dir.display()
        );
    }
}

/// Each recorded finding's first case, in a subprocess so a crash is reported rather than fatal: whether it still gives
/// its key. Returns whether one at least `level` still does.
fn replay_findings(store: &Store, targets: &[&'static fuzz::Target], level: fuzz::Severity) -> bool {
    let scratch = std::env::temp_dir().join(format!("leanvm-fuzz-replay-{}", std::process::id()));
    let (mut fixed, mut still, mut changed, mut failing) = (0, 0, 0, false);
    for (severity, target, key, _, dir) in store.findings() {
        if !targets.iter().any(|t| t.name == target) {
            continue;
        }
        let Some(case) = std::fs::read_dir(&dir)
            .into_iter()
            .flatten()
            .filter_map(Result::ok)
            .map(|e| e.path())
            .find(|p| p.file_name().is_some_and(|n| n.to_string_lossy().starts_with("case-")))
        else {
            continue;
        };
        let input = std::fs::read(&case).expect("read case");
        let now = key_of(&target, &input, &store.out, &scratch);
        let verdict = if now == "-" {
            fixed += 1;
            "fixed  "
        } else if now == key || (process_level(&key) && now.starts_with("crash")) {
            still += 1;
            failing |= severity <= level;
            "STILL  "
        } else {
            changed += 1;
            failing |= severity <= level;
            "CHANGED"
        };
        println!("{verdict} [{:<8}] {target:<28} {key}", severity.as_str());
        if verdict == "CHANGED" {
            println!("        now: {now}");
        }
    }
    let _ = std::fs::remove_file(scratch);
    println!("findings: {fixed} fixed, {still} still reproduce, {changed} changed");
    failing
}

/// Every corpus entry of `targets`, once, in this process. Returns whether a finding at least `level` appeared.
fn replay_corpus(store: &Store, targets: &[&'static fuzz::Target], level: fuzz::Severity) -> bool {
    let ctx = fuzz::Ctx::new(store.cache_dir(), 1);
    let mut failing = false;
    for target in targets {
        let corpus = store.corpus(target.name);
        if corpus.is_empty() {
            continue;
        }
        let t = std::time::Instant::now();
        let mut keys: BTreeMap<String, (fuzz::Severity, usize)> = BTreeMap::new();
        for input in &corpus {
            let result = fuzz::run_case(target, &mut CaseInput::decode(input).source(), &ctx);
            if let Some(f) = result.finding {
                keys.entry(f.key).or_insert((f.severity, 0)).1 += 1;
            }
        }
        println!(
            "{:<28} {:>6} entries {:>8.1}s  {}",
            target.name,
            corpus.len(),
            t.elapsed().as_secs_f64(),
            if keys.is_empty() { "ok" } else { "FINDINGS" }
        );
        for (key, (severity, n)) in keys {
            failing |= severity <= level && !store.suppressed(target.name, &key);
            println!("    [{:<8}] x{n:<5} {key}", severity.as_str());
        }
    }
    failing
}

/// One line per (program, rate): its cycles, and the first 16 hex digits of the Keccak of its bytecode and of its
/// proof's bytes. Programs over `2^16` cycles, slow ones and ones that do not prove are left out, deterministically.
#[cfg(feature = "dsl")]
fn fingerprint(filter: &str, rates: &[usize]) -> Vec<String> {
    let hex = |bytes: &[u8]| -> String {
        primitives::hash::hash(bytes)[..8]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    };
    let mut lines = Vec::new();
    for spec in fuzz::programs::provable()
        .into_iter()
        .filter(|s| !s.slow && s.name.contains(filter))
    {
        let Ok(program) = spec.compile() else { continue };
        let (Ok(exec), public_input) = fuzz::programs::execute(&program, spec.public_input) else {
            continue;
        };
        if exec.cycles > 1 << 16 || !exec.unconstrained_reads.is_empty() {
            continue;
        }
        let bytecode = hex(format!("{:?}", program.prog()).as_bytes());
        for &rate in rates {
            if let Ok((proof, _)) = leanvm_core::cpu::prove(&program, public_input, rate) {
                lines.push(format!(
                    "{}\trate {rate}\tcycles {}\tbytecode {bytecode}\tproof {}",
                    spec.name,
                    exec.cycles,
                    hex(&proof.to_bytes())
                ));
            }
        }
    }
    lines
}

/// The recursion guest's source, whose lines the guest's kill notes name.
const GUEST: &str = include_str!("../../../crates/rec_aggregation/guests/lean_ethereum.py");

fn guest_coverage(store: &Store, all: bool) {
    // `guest check <function> (line N)`, from every target that runs the guest.
    let mut fired: BTreeMap<usize, std::collections::BTreeSet<String>> = BTreeMap::new();
    for target in ["guest-forge", "guest-child", "aggregate-api", "aggregation-scenarios"] {
        for note in store.known_notes(target) {
            let Some(rest) = note.strip_prefix("guest check ") else {
                continue;
            };
            let line = rest
                .rsplit_once("(line ")
                .and_then(|(_, n)| n.trim_end_matches(')').parse::<usize>().ok());
            if let Some(line) = line {
                fired.entry(line).or_default().insert(target.to_string());
            }
        }
    }
    let mut function = String::new();
    let mut explicit = Vec::new();
    for (i, text) in GUEST.lines().enumerate() {
        let line = i + 1;
        let code = text.trim();
        if let Some(name) = code.strip_prefix("def ") {
            function = name.split('(').next().unwrap_or("").to_string();
        }
        if code.starts_with("assert ") || code.starts_with("assert_in_k(") || code.starts_with("assert_gpow(") {
            explicit.push((line, function.clone(), code.to_string()));
        }
    }
    let never: Vec<_> = explicit.iter().filter(|(line, ..)| !fired.contains_key(line)).collect();
    println!(
        "explicit checks: {} in lean_ethereum.py, {} fired at least once, {} never",
        explicit.len(),
        explicit.len() - never.len(),
        never.len()
    );
    let implicit = fired.keys().filter(|l| !explicit.iter().any(|(e, ..)| e == *l)).count();
    println!(
        "implicit checks that fired (stores into written cells, keccak outputs, range-check derefs): {implicit} lines"
    );
    println!("\nnever fired:");
    for (line, function, code) in &never {
        println!("  {line:>5}  {function:<32} {code}");
    }
    if all {
        println!("\nfired:");
        let lines: Vec<&str> = GUEST.lines().collect();
        for (line, targets) in &fired {
            let code = lines.get(line - 1).map_or("", |l| l.trim());
            let targets: Vec<&str> = targets.iter().map(String::as_str).collect();
            println!("  {line:>5}  {:<40} {code}", targets.join(","));
        }
    }
}

/// How long one replayed case may run before it counts as the hang it may be.
const KEY_TIMEOUT: Duration = Duration::from_secs(600);

/// Whether a key was recorded by the supervisor for a dead or killed worker, rather than returned by the target: such
/// a finding reproduces as a crash or a timeout, not as its key.
fn process_level(key: &str) -> bool {
    [
        "stack overflow",
        "died",
        "abort after panic",
        "hang",
        "memory",
        "allocation failure",
    ]
    .iter()
    .any(|p| key.starts_with(p))
}

/// The finding key `input` reproduces, from a subprocess so crashes count.
fn key_of(name: &str, input: &[u8], out: &std::path::Path, scratch: &std::path::Path) -> String {
    std::fs::write(scratch, input).expect("write scratch input");
    let stdout_file = scratch.with_extension("stdout");
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["repro", name, "--quiet", "--input"])
        .arg(scratch)
        .arg("--out")
        .arg(out)
        .stdout(std::fs::File::create(&stdout_file).expect("repro stdout"))
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("run repro");
    let deadline = std::time::Instant::now() + KEY_TIMEOUT;
    let status = loop {
        if let Some(status) = child.try_wait().expect("wait for repro") {
            break status;
        }
        if std::time::Instant::now() > deadline {
            let _ = child.kill();
            let _ = child.wait();
            return "crash: timeout".to_string();
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let stdout = std::fs::read_to_string(&stdout_file).unwrap_or_default();
    let _ = std::fs::remove_file(stdout_file);
    match stdout.lines().last() {
        Some(key) if status.success() => key.to_string(),
        _ => format!("crash: {status}"),
    }
}

/// Delta debugging on the input bytes: remove chunks, then zero bytes, keeping each edit that keeps the key.
fn minimize(name: &str, input: &std::path::Path, out: &std::path::Path, output: Option<PathBuf>) {
    let case = CaseInput::decode(&std::fs::read(input).expect("read input"));
    let scratch = std::env::temp_dir().join(format!("leanvm-fuzz-min-{}", std::process::id()));
    // A case with a tail replays from its consumed bytes once recorded: start from the case file itself.
    let mut best = case.encode();
    let key = key_of(name, &best, out, &scratch);
    assert_ne!(key, "-", "the input does not reproduce a finding");
    println!("key: {key}");
    // First drop the tail seed if the prefix alone keeps the key.
    let raw = case.prefix.clone();
    if case.tail_seed.is_some() && key_of(name, &raw, out, &scratch) == key {
        best = raw;
    }
    if best.starts_with(b"LVFZ1") {
        println!("the finding needs its tail seed; keeping the case file");
    } else {
        let mut chunk = best.len().next_power_of_two();
        while chunk >= 1 {
            let mut i = 0;
            while i < best.len() {
                let mut candidate = best.clone();
                candidate.drain(i..(i + chunk).min(best.len()));
                if key_of(name, &candidate, out, &scratch) == key {
                    best = candidate;
                    println!("{} bytes", best.len());
                } else {
                    i += chunk;
                }
            }
            chunk /= 2;
        }
        for i in 0..best.len() {
            if best[i] != 0 {
                let mut candidate = best.clone();
                candidate[i] = 0;
                if key_of(name, &candidate, out, &scratch) == key {
                    best = candidate;
                }
            }
        }
    }
    let output = output.unwrap_or_else(|| input.with_extension("min"));
    std::fs::write(&output, &best).expect("write output");
    let _ = std::fs::remove_file(scratch);
    println!("{} bytes: {}", best.len(), output.display());
}
