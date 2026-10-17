//! `binary-spartan prove <circuit.r1cs> <witness.bin> [--spark] [--self-check] [--repeat N] [--cooldown S] [--tracing]`
//!
//! Loads a Clean block R1CS and a batch witness, checks satisfaction, proves and verifies, and prints the shape,
//! the proof size and the prove and verify times (one warmup, then `--repeat` measured passes). `--tracing` prints
//! the final proving pass's span tree.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use bench::{Plan, Timing};
use binary_spartan::block::BlockR1cs;
use binary_spartan::format::{R1csFile, WitnessFile};
use binary_spartan::proof::{self, Mode, Proof};
use binary_spartan::spark;
use std::process::ExitCode;
use std::time::Instant;

const USAGE: &str = "usage: binary-spartan prove <circuit.r1cs> <witness.bin> [--spark] [--self-check] [--repeat N] \
                     [--cooldown S] [--tracing]";

struct Args {
    circuit: String,
    witness: String,
    spark: bool,
    self_check: bool,
    repeat: usize,
    cooldown: u64,
    tracing: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut args = std::env::args().skip(1);
    if args.next().as_deref() != Some("prove") {
        return Err(USAGE.into());
    }
    let mut paths = Vec::new();
    let (mut spark, mut self_check, mut repeat, mut cooldown, mut tracing) = (false, false, 1usize, 2u64, false);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--spark" => spark = true,
            "--self-check" => self_check = true,
            "--tracing" => tracing = true,
            "--repeat" => {
                repeat = args
                    .next()
                    .and_then(|n| n.parse().ok())
                    .filter(|&n| n > 0)
                    .ok_or("--repeat takes a positive integer")?;
            }
            "--cooldown" => {
                cooldown = args
                    .next()
                    .and_then(|n| n.parse().ok())
                    .ok_or("--cooldown takes a number of seconds")?;
            }
            _ if arg.starts_with("--") => return Err(format!("unknown flag {arg}\n{USAGE}")),
            _ => paths.push(arg),
        }
    }
    let [circuit, witness] = <[String; 2]>::try_from(paths).map_err(|_| USAGE.to_string())?;
    Ok(Args {
        circuit,
        witness,
        spark,
        self_check,
        repeat,
        cooldown,
        tracing,
    })
}

fn ms(timing: &Timing) -> String {
    format!("{:.1} ms{}", timing.mean() * 1e3, timing.spread())
}

fn run(args: &Args) -> Result<(), String> {
    leanvm_core::init_prover();
    if args.tracing {
        bench::init_tracing();
    }
    let read = |path: &str| std::fs::read(path).map_err(|e| format!("{path}: {e}"));
    let file = R1csFile::parse(&read(&args.circuit)?).map_err(|e| format!("{}: {e}", args.circuit))?;
    let block = BlockR1cs::new(&file).map_err(|e| format!("{}: {e}", args.circuit))?;
    let batch = WitnessFile::parse(&read(&args.witness)?).map_err(|e| format!("{}: {e}", args.witness))?;
    if batch.n_signals != block.n_signals {
        return Err(format!(
            "witness has {} signals, circuit {}",
            batch.n_signals, block.n_signals
        ));
    }

    let k_log = block.k_log();
    let mut z = vec![0u64; (1usize << k_log) / 64];
    for i in 0..batch.n_instances {
        z.fill(0);
        block.layout_instance(batch.instance(i), &mut z);
        if let Some(row) = block.first_violation(&z) {
            return Err(format!("instance {i} violates constraint {row}"));
        }
    }
    let shape = proof::Shape::new(&block, batch.n_instances).map_err(|e| format!("unsupported batch: {e}"))?;
    let m = &block.matrices;
    println!(
        "circuit: {} constraints, {} signals ({} public), nnz A/B/C = {}/{}/{}",
        block.n_constraints,
        block.n_signals,
        block.n_public,
        m.a.nnz(),
        m.b.nnz(),
        m.c.nnz()
    );
    println!(
        "batch: {} instances, satisfied; k_log = {}, n_log = {}",
        batch.n_instances, shape.k_log, shape.n_log
    );

    let pk = args.spark.then(|| {
        let t = Instant::now();
        let pk = spark::preprocess(m, proof::LOG_INV_RATE);
        println!("spark preprocess: {:.1} ms", t.elapsed().as_secs_f64() * 1e3);
        pk
    });
    let vk = pk.as_ref().map(|pk| pk.verifier_key());
    let prove_mode = pk.as_ref().map_or(Mode::Direct, Mode::Spark);
    let verify_mode = vk.as_ref().map_or(Mode::Direct, Mode::Spark);
    let publics = proof::publics(&block, &batch);

    let plan = Plan::new(args.repeat, args.cooldown);
    let (p, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        proof::prove(&block, &batch, prove_mode)
    });
    let p = p.map_err(|e| format!("prove: {e}"))?;
    let (verdict, verify_time) =
        Plan::new(args.repeat, 0).measure_quiet(|_| proof::verify(&block, &publics, &p, verify_mode));
    verdict.map_err(|e| format!("verify: {e}"))?;
    let size = bincode::serialized_size(&p).map_err(|e| e.to_string())?;
    println!(
        "prove {}, verify {}, proof {size} bytes ({} scalars, {} opening phases)",
        ms(&prove_time),
        ms(&verify_time),
        p.stream.len(),
        p.merkle.len()
    );

    if args.self_check {
        let rejects = |publics: &[u64], p: &Proof| proof::verify(&block, publics, p, verify_mode).is_err();
        if block.n_public > 0 {
            let mut flipped = publics.clone();
            flipped[0] ^= 1 << 1;
            check(rejects(&flipped, &p), "flipped public bit")?;
        }
        let bytes = bincode::serialize(&p).map_err(|e| e.to_string())?;
        for at in [bytes.len() / 3, bytes.len() / 2, bytes.len() - 1] {
            let mut bad = bytes.clone();
            bad[at] ^= 0x01;
            let rejected = bincode::deserialize::<Proof>(&bad).map_or(true, |q| rejects(&publics, &q));
            check(rejected, &format!("proof byte {at} of {} mutated", bytes.len()))?;
        }
        if args.spark {
            // SPARK runs last, so the final scalar of the stream is its own.
            let mut bad = p.clone();
            bad.stream.last_mut().expect("non-empty stream").c0 ^= 1;
            check(rejects(&publics, &bad), "SPARK scalar mutated")?;
        }
    }
    Ok(())
}

fn check(rejected: bool, what: &str) -> Result<(), String> {
    if rejected {
        println!("self-check: {what}: rejected");
        Ok(())
    } else {
        Err(format!("self-check: {what}: ACCEPTED"))
    }
}

fn main() -> ExitCode {
    match parse_args().and_then(|args| run(&args)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
