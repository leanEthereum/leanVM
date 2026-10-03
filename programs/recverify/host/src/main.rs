//! Host of `programs/recverify`, the leanVM verifier as a leanVM guest: prove an inner run, lay out the guest's
//! advice (the inner program, its output and the proof), then run the guest on the interpreter and count.
//!
//! ```text
//! recverify-host <recverify elf> fib <n> [core]     Fibonacci n (a multiple of 1000), verified in the guest
//! recverify-host <recverify elf> xmss <n> [core]    leanXMSS over n signatures, verified in the guest
//! recverify-host <recverify elf> prim <op> <n>      n of one primitive in the guest, or 100 + op checks one (its `primitive` codes)
//! recverify-host <recverify elf> words <log_ram> <log_advice> <rows per table...>
//! ```
//!
//! `core` runs `verify_core` in the guest rather than the whole verifier. `RATE` is the inner proof's log inverse
//! rate (1), `PROFILE=<file>` writes the guest's steps per pc and the pc's table, `PROFILE_CALLS=<file>` its calls
//! (`Calls`). `words` is the committed size of a modelled run of this guest, with RAM and the advice resized.
//!
//! The guest's run is streamed, never recorded: `Machine::step` one instruction at a time, counting the steps at each
//! pc, which give the rows per table, the fill and the committed size exactly. Recording it (`cpu::Program::execute`,
//! `measure`, `prove`) keeps every row, tens of GiB for the billions of steps a verification takes. `MEASURE=1`
//! checks the streamed numbers against `cpu::Program::measure`, and is refused past `MAX_TRACED_STEPS`, before
//! anything is recorded.

use std::collections::HashMap;
use std::fmt::Debug;
use std::io::Write;
use std::str::FromStr;

use leanvm_core::cpu::filler::Plan;
use leanvm_core::cpu::{DeferredClaims, Program};
use leanvm_core::pcs::{self, Rate};
use leanvm_core::rv::asm::*;
use leanvm_core::rv::{self, Machine, Region, RegisterFile};
use leanvm_core::tables::{self, N_TABLES};

/// The longest guest run `MEASURE=1` records in full.
const MAX_TRACED_STEPS: u64 = 1 << 22;

/// The guest's stack: the top megabyte of RAM (`guest/link.ld`).
const STACK_WORDS: usize = (1 << 20) / 8;

struct Inner {
    text: Vec<u32>,
    entry_pc: u64,
    image: Vec<u64>,
    log_ram: usize,
    log_advice: usize,
    advice: Vec<u64>,
}

fn fibonacci(n: usize) -> Inner {
    const UNROLL: usize = 1000;
    assert!(
        n >= UNROLL && n.is_multiple_of(UNROLL),
        "Fibonacci n is a multiple of {UNROLL}"
    );
    let mut text = Asm::new();
    text.li(Reg::A0, 0)
        .li(Reg::A1, 1)
        .li(Reg::T0, (n / UNROLL) as u64)
        .label("loop");
    for _ in 0..UNROLL / 2 {
        text.r(Add, Reg::A0, Reg::A0, Reg::A1).r(Add, Reg::A1, Reg::A0, Reg::A1);
    }
    text.i(Addi, Reg::T0, Reg::T0, -1)
        .branch(Bne, Reg::T0, Reg::ZERO, "loop")
        .li(Reg::A1, 0)
        .exit();
    Inner {
        text: text.finish(),
        entry_pc: Region::TEXT.base(),
        image: vec![],
        log_ram: 2,
        log_advice: 0,
        advice: vec![],
    }
}

fn leanxmss(n: usize) -> Inner {
    let guest = rv::Guest::from_elf(leanxmss_host::ELF).expect("the leanXMSS guest");
    Inner {
        text: guest.text,
        entry_pc: guest.entry_pc,
        image: guest.image,
        log_ram: guest.log_ram,
        log_advice: guest.log_advice,
        advice: leanxmss_host::batch(n).advice,
    }
}

fn parse<T: FromStr>(s: &str) -> T
where
    T::Err: Debug,
{
    s.parse().unwrap_or_else(|e| panic!("{s}: {e:?}"))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!(
            "usage: recverify-host <recverify elf> fib <n> [core] | xmss <n> [core] | prim <op> <n> | words <log_ram> <log_advice> <rows per table...>"
        );
        std::process::exit(2);
    }
    let elf = std::fs::read(&args[1]).unwrap_or_else(|e| panic!("{}: {e}", args[1]));
    match args[2].as_str() {
        "words" => words(&elf, &args[3..]),
        "prim" => {
            let outer = Program::from_elf(&elf).expect("the guest's ELF");
            let (op, n): (u64, u64) = (parse(&args[3]), parse(&args[4]));
            let advice = [u64::MAX, op, n];
            println!("prim {op} x {n}");
            let run = run(&outer, &advice);
            let shape = report(&outer, &run);
            measure_if_asked(&outer, &advice, &run, &shape);
            if op >= 100 {
                // A check: `[mismatches, n, first mismatching input]`.
                let [mismatches, checked, first, _] = run.output;
                println!(
                    "check of operation {}: {mismatches} mismatches in {checked} inputs",
                    op - 100
                );
                assert_eq!(mismatches, 0, "operation {} first differs on input {first}", op - 100);
            }
        }
        workload => {
            let outer = Program::from_elf(&elf).expect("the guest's ELF");
            let core = args.get(4).is_some_and(|a| a == "core");
            verify_in_guest(&outer, workload, parse(&args[3]), core);
        }
    }
}

/// Prove the inner run and verify it natively, then verify it in the guest, whose output must be the statement the
/// native verifier accepted.
fn verify_in_guest(outer: &Program, workload: &str, n: usize, core: bool) {
    let inner = match workload {
        "fib" => fibonacci(n),
        "xmss" => leanxmss(n),
        other => panic!("unknown inner workload {other}"),
    };
    let rate = Rate::new(std::env::var("RATE").map_or(1, |r| parse(&r))).expect("a supported rate");
    let program = Program::new(
        &inner.text,
        inner.entry_pc,
        inner.image.clone(),
        inner.log_ram,
        inner.log_advice,
    )
    .expect("the inner program");
    leanvm_core::init_prover();
    let (proof, output, stats) = program.prove(&inner.advice, rate).expect("the inner run proves");
    let claims = program
        .verify_core(&output, &proof)
        .expect("the inner proof's core verifies natively");
    program
        .check_deferred(&claims)
        .expect("the inner proof's deferred claims hold natively");
    let proof = proof.to_bytes();
    println!(
        "inner: {workload} {n}, text {} instructions ({} entries), log_inv_rate {}, proof {} bytes, {}",
        inner.text.len(),
        program.rv().entries().len(),
        rate.log_inv_rate(),
        proof.len(),
        stats.details()
    );

    let text: Vec<u8> = inner.text.iter().flat_map(|w| w.to_le_bytes()).collect();
    let mut advice = vec![u64::from(core), inner.text.len() as u64];
    advice.extend(le_words(&text));
    advice.extend([inner.entry_pc, inner.image.len() as u64]);
    advice.extend(&inner.image);
    advice.extend([inner.log_ram as u64, inner.log_advice as u64]);
    advice.extend(output);
    advice.push(proof.len() as u64);
    advice.extend(le_words(&proof));

    // The statement the guest must commit, as the native verifier accepted it.
    let mut public = leanvm_guest::PublicValues::new();
    public.commit(&digest_words(program.digest()));
    public.commit(&output);
    if core {
        let words = claim_words(&claims);
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let hash = digest_words(&primitives::hash::hash(&bytes));
        println!("inner: deferred claims {} words", words.len());
        public.commit(&hash);
    }
    let expected = public.digest();

    println!(
        "outer: {} mode, text {} instructions, log_ram {}, log_advice {}, advice used {} words",
        if core { "verify_core" } else { "full" },
        outer.rv().entries().len(),
        outer.rv().log_ram(),
        outer.rv().log_advice(),
        advice.len()
    );
    let run = run(outer, &advice);
    assert_eq!(
        run.output, expected,
        "the guest commits the statement the native verifier accepted"
    );
    println!("outer: committed {:016x?}, the native verifier's statement", run.output);
    let shape = report(outer, &run);
    measure_if_asked(outer, &advice, &run, &shape);
}

/// A 32-byte digest as four little-endian words, as the guest commits it.
fn digest_words(digest: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().expect("eight bytes")))
}

/// Bytes as little-endian words, the last zero-padded.
fn le_words(bytes: &[u8]) -> impl Iterator<Item = u64> + '_ {
    bytes.chunks(8).map(|c| {
        let mut word = [0; 8];
        word[..c.len()].copy_from_slice(c);
        u64::from_le_bytes(word)
    })
}

/// The guest's `claim_words`: the deferred claims as words, every `F192` its three coefficients, in field order.
fn claim_words(claims: &DeferredClaims) -> Vec<u64> {
    use primitives::field::F192;
    let mut words = Vec::new();
    let mut put = |xs: &[F192]| words.extend(xs.iter().flat_map(|x| [x.c0, x.c1, x.c2]));
    for (c, p) in &claims.program.terms {
        put(&[*c]);
        put(&p.bytecode);
        put(&p.twist);
        put(&[p.image_weight]);
        put(&p.image_point);
    }
    put(&[claims.program.value]);
    for claim in &claims.circuits {
        for (c, form) in &claim.terms {
            put(&[*c, form.alpha, form.z_skip]);
            put(&form.x_inner_rest);
            put(&form.r_inner_rest);
            put(&form.s_hat_v);
        }
        put(&[claim.value]);
    }
    words
}

/// A streamed run of the guest: its steps, the steps at each text index, and its output.
struct Run {
    steps: u64,
    by_index: Vec<u64>,
    output: [u64; 4],
}

/// `PROFILE_CALLS`: a shadow call stack, a call linking `ra` and a return being a `jalr` through `ra` that links
/// nothing. It writes, per caller and callee entry pc, the steps spent inside the callee and the calls, then per
/// callee the calls under the two frames below the root (the verifier's stages).
#[derive(Default)]
struct Calls {
    /// (callee pc, steps at entry); the root's caller is pc 0.
    stack: Vec<(u64, u64)>,
    edges: HashMap<(u64, u64), (u64, u64)>,
    by_stage: HashMap<(u64, u64, u64), u64>,
}

impl Calls {
    fn step(&mut self, entry: &rv::Entry, pc: u64, steps: u64) {
        if entry.link && entry.ad == 1 {
            let frame = |d: usize| self.stack.get(d).map_or(0, |f| f.0);
            *self.by_stage.entry((frame(1), frame(2), pc)).or_default() += 1;
            self.stack.push((pc, steps));
        } else if entry.jalr
            && entry.a1 == 1
            && entry.ad == RegisterFile::SINK
            && let Some((callee, start)) = self.stack.pop()
        {
            let caller = self.stack.last().map_or(0, |f| f.0);
            let edge = self.edges.entry((caller, callee)).or_default();
            edge.0 += steps - start;
            edge.1 += 1;
        }
    }

    fn write(&self, path: &str, steps: u64) {
        let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap_or_else(|e| panic!("{path}: {e}")));
        writeln!(f, "total {steps}").unwrap();
        for ((caller, callee), (inclusive, calls)) in &self.edges {
            writeln!(f, "{caller:#x} {callee:#x} {inclusive} {calls}").unwrap();
        }
        for ((stage, substage, callee), calls) in &self.by_stage {
            writeln!(f, "stage {stage:#x} {substage:#x} {callee:#x} {calls}").unwrap();
        }
    }
}

/// Run the guest on the interpreter, one step at a time, counting the steps at each text index.
fn run(outer: &Program, advice: &[u64]) -> Run {
    let entries = outer.rv().entries();
    let calls_path = std::env::var("PROFILE_CALLS").ok();
    let mut calls = calls_path.as_ref().map(|_| Calls::default());
    let mut machine = Machine::new(outer.rv(), advice);
    let mut by_index = vec![0u64; entries.len()];
    let mut steps = 0u64;
    while !machine.halted() {
        let step = machine
            .step()
            .unwrap_or_else(|t| panic!("trap at pc {:#x} after {steps} steps: {t:?}", machine.pc()));
        by_index[step.index] += 1;
        steps += 1;
        if let Some(calls) = &mut calls {
            calls.step(&entries[step.index], machine.pc(), steps);
        }
    }
    if let (Some(path), Some(calls)) = (calls_path, calls) {
        calls.write(&path, steps);
    }
    let output = machine.output().expect("the guest exits");

    // RAM in use: the heap grows up from the image, the stack down from the top megabyte.
    let ram = machine.memory().ram();
    let (heap, stack) = ram.split_at(ram.len() - STACK_WORDS);
    let heap_top = heap.iter().rposition(|&w| w != 0).map_or(0, |i| i + 1);
    let stack_depth = stack.iter().position(|&w| w != 0).map_or(0, |i| STACK_WORDS - i);
    println!(
        "outer: RAM {} words; heap and image up to word {heap_top} (2^{:.2}), stack {stack_depth} words",
        ram.len(),
        (heap_top.max(1) as f64).log2()
    );
    Run {
        steps,
        by_index,
        output,
    }
}

/// What a proof of the run would commit: the rows each table executed, its height with the fill, and the stack.
struct Shape {
    rows: [usize; N_TABLES],
    filled: [usize; N_TABLES],
    mu: usize,
    committed: usize,
}

/// The run's shape from its step counts, printed, and `PROFILE=<file>` (steps per pc and the pc's table).
fn report(outer: &Program, run: &Run) -> Shape {
    let entries = outer.rv().entries();
    let mut rows = [0usize; N_TABLES];
    for (entry, &count) in entries.iter().zip(&run.by_index) {
        if count > 0 {
            rows[tables::table_of(entry.class).expect("an executed entry has a table")] += count as usize;
        }
    }
    let filled = Plan::solve(rows).filled(rows);
    let (mu, committed) = outer.stack_sizes(filled);
    let log2 = |x: usize| (x.max(1) as f64).log2();
    let per_table: Vec<String> = (0..N_TABLES)
        .map(|t| {
            format!(
                "{} {} (2^{:.3}, height 2^{})",
                tables::CLASSES[t].name,
                rows[t],
                log2(rows[t]),
                filled[t].trailing_zeros()
            )
        })
        .collect();
    println!(
        "outer: {} steps (2^{:.3}), {} cycles with the fill; rows {}",
        run.steps,
        (run.steps.max(1) as f64).log2(),
        filled.iter().sum::<usize>(),
        per_table.join(", ")
    );
    println!(
        "outer: committed {committed} words (2^{:.3}), stack 2^{mu}, MAX_MU {}: {}",
        log2(committed),
        pcs::MAX_MU,
        if mu <= pcs::MAX_MU {
            "fits one proof"
        } else {
            "does not fit one proof"
        }
    );
    // Committed words one more row costs in each table: the stacked size's slope at 2^20 rows, the rest empty.
    let slopes: Vec<String> = (0..N_TABLES)
        .map(|t| {
            let at = |log: usize| {
                let mut counts = [0; N_TABLES];
                counts[t] = 1 << log;
                outer.stack_sizes(counts).1
            };
            format!(
                "{} {:.2}",
                tables::CLASSES[t].name,
                (at(21) - at(20)) as f64 / f64::from(1 << 20)
            )
        })
        .collect();
    println!("outer: committed words per row: {}", slopes.join(", "));
    if let Ok(path) = std::env::var("PROFILE") {
        let mut f = std::io::BufWriter::new(std::fs::File::create(&path).unwrap_or_else(|e| panic!("{path}: {e}")));
        for (i, (&count, entry)) in run.by_index.iter().zip(entries).enumerate() {
            if count > 0 {
                let table = tables::CLASSES[tables::table_of(entry.class).expect("an executed entry has a table")].name;
                writeln!(f, "{:#x} {count} {table}", outer.rv().pc_of(i)).unwrap();
            }
        }
    }
    Shape {
        rows,
        filled,
        mu,
        committed,
    }
}

/// `MEASURE=1`: the streamed shape against `cpu::Program::measure`, which records the run's whole trace, so only for
/// a run of at most `MAX_TRACED_STEPS`.
fn measure_if_asked(outer: &Program, advice: &[u64], run: &Run, shape: &Shape) {
    if std::env::var_os("MEASURE").is_none() {
        return;
    }
    if run.steps > MAX_TRACED_STEPS {
        eprintln!(
            "MEASURE refused: the guest ran {} steps, past MAX_TRACED_STEPS ({MAX_TRACED_STEPS}). `cpu::Program::measure` \
             records every row of the run, which at billions of steps is tens of GiB; the streamed numbers above are exact.",
            run.steps
        );
        std::process::exit(1);
    }
    let stats = outer.measure(advice).expect("the guest's run measures");
    assert_eq!(stats.base_counts, shape.rows, "the rows each table executed");
    assert_eq!(stats.counts, shape.filled, "the heights with the fill");
    assert_eq!(stats.committed, shape.committed, "the committed size");
    assert!(shape.mu <= pcs::MAX_MU);
    println!(
        "outer: MEASURE agrees: {} cycles, committed {} words",
        stats.cycles, stats.committed
    );
}

/// `words <log_ram> <log_advice> <rows per table...>`: the committed size of a modelled run of this guest, the rows
/// being those each table executes, before the fill.
fn words(elf: &[u8], args: &[String]) {
    assert_eq!(
        args.len(),
        2 + N_TABLES,
        "words <log_ram> <log_advice> <rows of each of the {N_TABLES} tables>"
    );
    let guest = rv::Guest::from_elf(elf).expect("the guest's ELF");
    let resized = Program::new(
        &guest.text,
        guest.entry_pc,
        guest.image,
        parse(&args[0]),
        parse(&args[1]),
    )
    .expect("the guest, resized");
    let rows: [usize; N_TABLES] = std::array::from_fn(|t| parse(&args[2 + t]));
    let (mu, committed) = resized.stack_sizes(Plan::solve(rows).filled(rows));
    println!(
        "committed {committed} words (2^{:.3}), stack 2^{mu}",
        (committed.max(1) as f64).log2()
    );
}
