//! A worker process: one target, cases until its time slice ends, reporting to the supervisor on stdout.
//!
//! Protocol, one line each, prefixed `@@FUZZ`:
//! - `START <n>` before case `n`, whose input is already in `workers/<id>.case`, so a crash names its case;
//! - `END <n> <micros> <finding severity or ->` after it;
//! - `NOTE <count>` when the case reached notes new to this worker.

use crate::store::{CaseInput, Store};
use fuzz::{Ctx, Rng, Target, run_case, source::mutate};
use std::collections::BTreeSet;
use std::io::Write;
use std::time::{Duration, Instant};

pub struct WorkerArgs {
    pub target: &'static Target,
    pub id: String,
    pub seed: u64,
    pub depth: u8,
    pub max_cases: u64,
    pub max_time: Duration,
}

fn say(line: &str) {
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "@@FUZZ {line}");
    let _ = out.flush();
}

pub fn run(store: &Store, args: WorkerArgs) {
    let ctx = Ctx::new(store.cache_dir(), args.depth);
    let mut rng = Rng::new(args.seed);
    let mut known: BTreeSet<String> = store.known_notes(args.target.name);
    let mut corpus = store.corpus(args.target.name);
    let start = Instant::now();
    let mut last_sync = Instant::now();
    // Open once: a cheap target runs thousands of cases a second, each announced here before it runs.
    let case_file = std::fs::File::create(store.worker_file(&args.id, "case")).expect("worker case file");
    for n in 0..args.max_cases {
        if start.elapsed() > args.max_time {
            break;
        }
        if last_sync.elapsed() > Duration::from_secs(120) {
            known.extend(store.known_notes(args.target.name));
            corpus = store.corpus(args.target.name);
            last_sync = Instant::now();
        }
        // Mostly fresh cases while the corpus is small, mostly its neighbours once it has grown.
        let mutate_share = (corpus.len() as u64 * 4).min(70);
        let prefix = if !corpus.is_empty() && rng.below(100) < mutate_share {
            let base = &corpus[rng.below(corpus.len() as u64) as usize];
            let other = &corpus[rng.below(corpus.len() as u64) as usize];
            mutate(base, &mut rng, Some(other))
        } else {
            Vec::new()
        };
        let case = CaseInput {
            prefix,
            tail_seed: Some(rng.next_u64()),
        };
        let encoded = case.encode();
        let _ = case_file.set_len(encoded.len() as u64);
        let _ = std::os::unix::fs::FileExt::write_all_at(&case_file, &encoded, 0);
        say(&format!("START {n}"));
        let t = Instant::now();
        let mut source = case.source();
        let result = run_case(args.target, &mut source, &ctx);
        let micros = t.elapsed().as_micros();
        let severity = match &result.finding {
            Some(finding) => {
                store.record(args.target.name, finding, &case);
                finding.severity.as_str()
            }
            None => "-",
        };
        let fresh: Vec<String> = result.notes.into_iter().filter(|note| !known.contains(note)).collect();
        if !fresh.is_empty() {
            // A recording that hit its cap replays only with its seed: keep the case file instead.
            let input = if result.consumed.len() == source.consumed_len() {
                result.consumed
            } else {
                case.encode()
            };
            store.add_to_corpus(args.target.name, &input, &fresh);
            corpus.push(input);
            say(&format!("NOTE {}", fresh.len()));
            known.extend(fresh);
        }
        say(&format!("END {n} {micros} {severity}"));
    }
}
