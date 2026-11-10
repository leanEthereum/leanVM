//! `cargo leanvm-fuzz`: run a fuzzing campaign over leanVM, and triage what it finds. See `crates/fuzz/README.md`.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

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
        Command::Minimize {
            target: name,
            input,
            out,
            output,
        } => minimize(&name, &input, &out, output),
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

/// The finding key `input` reproduces, from a subprocess so crashes count.
fn key_of(name: &str, input: &[u8], out: &std::path::Path, scratch: &std::path::Path) -> String {
    std::fs::write(scratch, input).expect("write scratch input");
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["repro", name, "--quiet", "--input"])
        .arg(scratch)
        .arg("--out")
        .arg(out)
        .output()
        .expect("run repro");
    let stdout = String::from_utf8_lossy(&output.stdout);
    match stdout.lines().last() {
        Some(key) if output.status.success() => key.to_string(),
        _ => format!("crash: {}", output.status),
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
