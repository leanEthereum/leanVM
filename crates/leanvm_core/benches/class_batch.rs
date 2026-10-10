//! Each instruction class's flock circuit proven alone, on a batch of its instances with exactly 16 pool threads.
//!
//! The circuits and witness generators are the VM's own, so this is a proof's flock stage, one class at a time:
//!
//! ```text
//!     witness     the class's generator (word arithmetic, or the walk of the gate list)
//!     commit      the packed witness, as its own WHIR commitment
//!     reduction   flock's zerocheck and lincheck
//!     opening     the stacked opening of the reduction's claim
//! ```
//!
//! An argument keeps the classes whose name contains it, none keeps every class with a circuit.
//!
//! ```text
//! BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo bench -p leanvm --bench class_batch -- hash mul
//! ```
//!
//! `BENCH_TRACING=1` prints the final pass's span tree (`RUST_LOG` adjusts it).
//! With `-- --json` it prints, in place of the reports, each class's proving time as Bencher Metric Format JSON.
//! The time excludes the witness, and each benchmark is named `flock-<class>-batch-<n>-16thread`, measure `latency`, with the actual `threads` count.

use std::num::NonZeroUsize;
use std::time::Instant;

use bench::{Metric, Plan, Timing, bencher_json};
use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
use flock::Witness;
use flock::circuit::Circuit;
use flock::reduction::{self, Instance};
use leanvm::{Fill, MIN_MU, TableId, Word};
use pcs::ring_switch::RingSwitch;
use pcs::stack::{CommittedStack, StackCommitment, Statement};
use pcs::whir::{Config, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, config_for_rate};
use primitives::field::F64;
use primitives::pretty_integer;
use primitives::test_util::Rng;

#[global_allocator]
static ALLOCATOR: bench::Counting<bench::Jemalloc> = bench::Counting(bench::Jemalloc);

/// The most input words of a class circuit: HASH's counter, flags and twelve block words.
const ROW_WORDS: usize = 14;

/// One instance's input words, the circuit's ports first.
type Row = [u64; ROW_WORDS];

/// The stages of a prove pass, timed apart.
const STAGES: [&str; 4] = ["witness", "commit", "reduction", "opening"];

fn main() {
    parallel::init_with_threads(NonZeroUsize::new(16).unwrap()).expect("initialize exact 16-thread benchmark pool");
    bench::init_tracing_from_env();
    let json = std::env::args().any(|arg| arg == "--json");
    let filters: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| !a.starts_with('-'))
        .map(|a| a.to_uppercase())
        .collect();
    let n_log_requested = bench::env_usize("FLOCK_N_LOG", 16);

    let mut report = Vec::new();
    for table in TableId::ALL {
        let name = table.spec().name;
        if !filters.is_empty() && !filters.iter().any(|f| name.contains(f.as_str())) {
            continue;
        }
        let Some(batch) = ClassBatch::new(table, n_log_requested) else {
            continue;
        };
        let (prove, n) = batch.bench(json);
        report.push((
            format!("flock-{}-batch-{n}-16thread", name.to_lowercase()),
            vec![
                ("latency", Metric::nanoseconds(&prove)),
                ("threads", Metric::exact(parallel::num_threads())),
            ],
        ));
    }
    if json {
        println!("{}", bencher_json(&report));
    }
}

/// A batch of one class's random instances, and the commitment's shape.
struct ClassBatch {
    name: &'static str,
    circuit: Circuit,
    fill: Fill,
    rows: Vec<Row>,
    n_log: usize,
    mu: usize,
    config: Config,
}

impl ClassBatch {
    /// `2^n_log` instances of `table`'s class, grown until the packed witness fills a commitment.
    ///
    /// Every value port gets a random word, the flags port a legal word, cycling through them.
    /// A class with no circuit has none.
    fn new(table: TableId, n_log: usize) -> Option<Self> {
        let spec = table.spec();
        let class = spec.circuit.as_ref()?;
        let circuit = spec.class.circuit();
        let n_inputs = circuit.n_input_words();
        assert!(n_inputs <= ROW_WORDS, "{} has more input words than a row", spec.name);

        // Packed 64 bits a word, so `2^(k_log + n_log - 6)` committed words.
        let n_log = n_log.max(MIN_MU + 6 - circuit.k_log());
        let mu = circuit.k_log() + n_log - 6;

        let legal = spec.class.legal_flags();
        let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ table.index() as u64);
        let rows = (0..1usize << n_log)
            .map(|i| {
                std::array::from_fn(|k| match class.inputs.get(k) {
                    Some(Word::Flags) => legal[i % legal.len()],
                    Some(_) => rng.next_u64(),
                    None => 0,
                })
            })
            .collect();
        Some(Self {
            name: spec.name,
            circuit,
            fill: class.fill,
            rows,
            n_log,
            mu,
            config: config_for_rate(mu, LOG_INV_RATE_0).expect("WHIR configuration"),
        })
    }

    /// The packed witness, by the class's own generator.
    fn witness(&self) -> Witness {
        let (rows, n, n_log) = (&self.rows, self.circuit.n_input_words(), self.n_log);
        match self.fill {
            Fill::Walk => self.circuit.witness_by_walk(rows, &rows[0], n_log, |row, words| {
                words.copy_from_slice(&row[..n]);
            }),
            Fill::Instance(instance) => self
                .circuit
                .witness_by_instance(rows, &rows[0], n_log, |row, z, az, bz| {
                    instance(&row[..n], z, az, bz);
                }),
            Fill::Batch8(batch) => self
                .circuit
                .witness_by_batch8(rows, &rows[0], n_log, |rows, z, az, bz| {
                    batch(&rows.map(|row| &row[..n]), z, az, bz);
                }),
        }
    }

    /// One prove pass, and each stage's seconds.
    fn prove(&self) -> (ProofTranscript, [f64; 4]) {
        let _span = tracing::info_span!("Flock prove", n_log = self.n_log).entered();
        let t = Instant::now();
        let witness = self.witness();
        let witness_s = t.elapsed().as_secs_f64();

        let mut ps = ProverState::from_label(b"flock-class-batch");
        let t = Instant::now();
        let committed = CommittedStack::new(&mut ps, as_field(&witness.z), self.mu, self.config.clone());
        let commit_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let instance = Instance::of(self.circuit.block(), self.n_log, &witness);
        let claim = reduction::prove(&[instance], &mut ps).pop().expect("one circuit");
        let reduction_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let ring = RingSwitch {
            offset: 0,
            qflock_vars: self.mu,
            claims: vec![claim],
        };
        let z = as_field(&witness.z);
        let rings = [ring];
        committed.open(
            &mut ps,
            z,
            Statement {
                points: &[],
                rings: &rings,
            },
        );
        let opening_s = t.elapsed().as_secs_f64();

        (ps.into_proof(), [witness_s, commit_s, reduction_s, opening_s])
    }

    /// Replay `proof`, panicking on any refusal.
    fn verify(&self, proof: &ProofTranscript) {
        let block = self.circuit.block();
        let mut vs = VerifierState::from_label(b"flock-class-batch", proof);
        let commitment = StackCommitment::receive(&mut vs, self.mu, 1 << INITIAL_FOLDING_FACTOR, self.config.clone())
            .expect("immutable anchored commitment");
        let replay = reduction::verify(&[(block.shape(), self.n_log)], &mut vs)
            .expect("the reduction verifies")
            .remove(0);
        replay.matrices.check(block.circuit).expect("the matrices settle");
        let ring = RingSwitch {
            offset: 0,
            qflock_vars: self.mu,
            claims: vec![replay.claim],
        };
        let rings = [ring];
        commitment
            .verify(
                &mut vs,
                Statement {
                    points: &[],
                    rings: &rings,
                },
            )
            .expect("the opening verifies");
        vs.finish().expect("transcript fully consumed");
    }

    /// Time the batch's proving and verifying, printing a report unless `quiet`.
    ///
    /// Returns the proving time, witness excluded, and the batch size.
    fn bench(&self, quiet: bool) -> (Timing, usize) {
        let plan = Plan::from_env();
        let mut passes = Vec::new();
        let (proof, _) = plan.warm_then_measure(|final_pass| {
            let _quiet = (!final_pass).then(bench::suppress_tracing);
            let (proof, secs) = self.prove();
            passes.push(secs);
            proof
        });
        // The warmup pushed the first pass's stages too.
        let stages: [Timing; 4] = std::array::from_fn(|s| {
            let mut timing = Timing::default();
            passes[1..].iter().for_each(|secs| timing.push(secs[s]));
            timing
        });
        let mut prove = Timing::default();
        passes[1..].iter().for_each(|secs| prove.push(secs[1..].iter().sum()));
        let (_, verify) = Plan::new(plan.repeat, 0).measure_quiet(|_| self.verify(&proof));

        let n = self.rows.len();
        if !quiet {
            let ms = |t: &Timing| format!("{:>8.1} ms{}", t.mean() * 1e3, t.spread());
            println!(
                "\n{}: {} instances of 2^{} bits, {} threads",
                self.name,
                pretty_integer(&n),
                self.circuit.k_log(),
                parallel::num_threads()
            );
            for (stage, timing) in STAGES.iter().zip(&stages) {
                println!("  {stage:<26}: {}", ms(timing));
            }
            println!("  {:<26}: {}", "prove (witness excluded)", ms(&prove));
            println!("  {:<26}: {}", "verify", ms(&verify));
            println!(
                "  {:<26}: {:>11} instances/s",
                "throughput",
                pretty_integer(&((n as f64 / prove.mean()).round() as u64))
            );
        }
        (prove, n)
    }
}

/// The packed words as the committed column, viewed in place.
const fn as_field(z: &[u64]) -> &[F64] {
    // SAFETY: `F64` is `repr(transparent)` over `u64`.
    unsafe { std::slice::from_raw_parts(z.as_ptr().cast(), z.len()) }
}
