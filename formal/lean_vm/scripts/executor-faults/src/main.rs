//! The executors on `KECCAK` window cases and the compiler suite's programs, each again with every `aligned` flag
//! cleared: the stable and the experimental Rust executors against each other (a difference fails the run), and a
//! case directory per run for `lake exe leanvm-execute` (`Statement/Prover/Execute.lean`), with `fault.txt` where
//! the Rust faults, `memory.bin` and `trace.txt` where it halts.
//!
//! Usage: `cargo run --release --manifest-path scripts/executor-faults/Cargo.toml -- <output dir>`.
#[allow(dead_code, unused_imports)]
#[path = "../../../../../crates/zkdsl_compiler/tests/suite/py_source.rs"]
mod py_source;

use isa::{Program, RHint};
use lean_vm_core as stable;
use primitives as sprim;
use sprim::field::F128;
use std::path::Path;
use zkdsl_compiler::{compile, parse};

type Witness = Vec<(String, Vec<Vec<F128>>)>;

fn windows_sources() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for k in 1..=16 {
        out.push((format!("pin{k}"), format!(
"def h(p: StackBuf({k}), t: StackBuf(4), st: StackBuf(13)):
    a = StackBuf(2)
    keccak([p[0], p[0]], [p[0], p[0]], a, tail=t)
    b = StackBuf(2)
    keccak_cells([p[0]], b, state=st)
    return a[0] + b[1]

def main():
    p = StackBuf({k})
    for i in unroll(0, {k}):
        p[i] = const(i + 1)
    t = StackBuf(4)
    for i in unroll(0, 4):
        t[i] = const(i + 7)
    st = StackBuf(13)
    keccak([1, 2], [3, 4], st)
    a = StackBuf(2)
    keccak([p[0], p[0]], [p[0], p[0]], a, tail=t)
    b = StackBuf(2)
    keccak_cells([p[0]], b, state=st)
    x = h(p, t, st)
    assert x == a[0] + b[1]
    return
")));
        for wrong in ["", "d", "s"] {
            let fill = |name: &str, n: usize| {
                if name == wrong {
                    format!("    for i in unroll(0, {n}):\n        {name}[i] = 0\n")
                } else {
                    format!("    keccak([5, 6], [7, 8], {name})\n")
                }
            };
            out.push((format!("pout{k}{wrong}"), format!(
"def check(p: StackBuf({k}), d: StackBuf(2), s: StackBuf(13)):
    keccak([p[0], 6], [7, 8], d)
    keccak([p[0], 6], [7, 8], s)
    return

def main():
    p = StackBuf({k})
    for i in unroll(0, {k}):
        p[i] = 5
    d = StackBuf(2)
{}    s = StackBuf(13)
{}    check(p, d, s)
    return
", fill("d", 2), fill("s", 13))));
        }
    }
    let body = "    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    d = StackBuf(2)
    keccak([h[0], x], [x, h[1]], d, tail=a)
    e = StackBuf(13)
    keccak_cells([d[0]], e, state=h)
    f = StackBuf(2)
    keccak([e[0], e[1]], [d[1], x], f, tail=a)
    return e[0] + e[12] + f[1]
";
    for n in 1..=17 {
        out.push((format!("fixed{n}"), format!(
"def fixed(x):
    pad = StackBuf({n})
    for k in unroll(0, {n}):
        pad[k] = x
    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    q = addr(pad)
    assert q[1] == x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    return h[0] + h[12]

def free(x):
    a = StackBuf(4)
    for k in unroll(0, 4):
        a[k] = x
    h = StackBuf(13)
    keccak([x, x], [x, x], h, tail=a)
    return h[0] + h[12]

def main():
    y = fixed(5)
    assert y == free(5)
    return
")));
        out.push((format!("several{n}"), format!(
"def fixed(x):
    pad = StackBuf({n})
    for k in unroll(0, {n}):
        pad[k] = x
    q = addr(pad)
    assert q[1] == x
{body}
def free(x):
{body}
def main():
    y = fixed(5)
    assert y == free(5)
    return
")));
    }
    let mut src = String::from(
"def free(a, b, c, d):
    t = StackBuf(4)
    t[0] = a
    t[1] = b
    t[2] = c
    t[3] = d
    h = StackBuf(2)
    keccak([1, 2], [3, 4], h, tail=t)
    return h[0]

def main():
    m = StackBuf(17)
    for i in unroll(0, 17):
        m[i] = const(i + 1)
");
    for i in 0..14 {
        src += &format!("    h{i} = StackBuf(2)\n    keccak([1, 2], [3, 4], h{i}, tail=m[{i}:{i} + 4])\n    assert h{i}[0] == free(m[{i}], m[{i} + 1], m[{i} + 2], m[{i} + 3])\n");
    }
    src += "    return\n";
    out.push(("sliding".to_string(), src));
    out
}

fn clear_aligned(compiled: &mut isa::CompiledProgram) -> usize {
    let mut n = 0;
    for hints in compiled.hints.values_mut() {
        for h in hints.iter_mut() {
            match h {
                RHint::Alloc { aligned, .. } | RHint::AllocFrames { aligned, .. } | RHint::AllocArm { aligned, .. } => {
                    n += usize::from(*aligned);
                    *aligned = false;
                }
                _ => {}
            }
        }
    }
    n
}

fn lean_fault(f: &stable::cpu::Fault) -> Option<String> {
    use stable::cpu::Fault::*;
    match f {
        KeccakAcrossWindow { cell, cells } => Some(format!("keccakAcrossWindow {cell} {cells}")),
        Conflict { cell, .. } => Some(format!("conflict {cell}")),
        OutOfMemory => Some("outOfMemory".into()),
        StepLimit => Some("stepLimit".into()),
        _ => None,
    }
}

fn main() {
    <exp::ExperimentalProver as isa::Prover>::init();
    let args: Vec<String> = std::env::args().collect();
    let checkout = &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../..");
    let out = Path::new(args.get(1).expect("usage: executor-faults <output dir>"));
    let mut cases: Vec<(String, String, Witness, [F128; 2])> = windows_sources()
        .into_iter()
        .map(|(n, s)| (n, s, Vec::new(), [F128::ZERO; 2]))
        .collect();
    let mut paths: Vec<_> = std::fs::read_dir(checkout.join("crates/zkdsl_compiler/tests/programs"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    for p in paths {
        let src = std::fs::read_to_string(&p).unwrap();
        let pi = py_source::public_input(&src).unwrap_or([F128::ZERO; 2]);
        let w = py_source::witness(&src);
        cases.push((p.file_stem().unwrap().to_string_lossy().replace('_', "-"), src, w, pi));
    }
    let (mut agree, mut differ, mut faults, mut unsupported) = (0, 0, 0, 0);
    for (name, src, witness, pi) in cases {
        let Ok(ast) = parse(&src) else { println!("{name}: no parse"); continue };
        let compiled = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| compile(&ast))) {
            Ok(c) => c,
            Err(_) => { println!("{name}: compiler panics"); continue }
        };
        for cleared in [false, true] {
            let mut c = compiled.clone();
            if cleared && clear_aligned(&mut c) == 0 { continue; }
            let case = if cleared { format!("{name}-unaligned") } else { name.clone() };
            let program = Program::from(c);
            let s = stable::cpu::execute(&program, &witness, pi);
            let ew: Vec<(String, Vec<Vec<eprim::field::F128>>)> = witness.iter()
                .map(|(n, es)| (n.clone(), es.iter().map(|e| e.iter().map(|v| exp::cpu::from_scalar(stable::cpu::to_scalar(v))).collect()).collect()))
                .collect();
            let epi = pi.map(|v| exp::cpu::from_scalar(stable::cpu::to_scalar(&v)));
            let e = exp::cpu::execute(&program, &ew, epi);
            let same = match (&s, &e) {
                (Ok(a), Ok(b)) => a.cycles == b.cycles && a.mem.len() == b.mem.len()
                    && (0..a.mem.len()).all(|i| stable::cpu::to_scalar(&a.mem.word(i)) == exp::cpu::to_scalar(&b.mem.word(i))),
                (Err(a), Err(b)) => a.pc == b.pc && format!("{:?}", a.fault) == format!("{:?}", b.fault),
                _ => false,
            };
            if same { agree += 1 } else { differ += 1; println!("{case}: STABLE/EXPERIMENTAL DIFFER: {:?} vs {:?}", s.as_ref().map(|x| x.cycles).map_err(|x| x.to_string()), e.as_ref().map(|x| x.cycles).map_err(|x| x.to_string())); }
            let dir = out.join(&case);
            std::fs::create_dir_all(&dir).unwrap();
            let table: Vec<u8> = program.stacked_bytecode().iter().flat_map(|w| w.to_le_bytes()).collect();
            std::fs::write(dir.join("bytecode.bin"), &table).unwrap();
            std::fs::write(dir.join("public_input.bin"), stable::cpu::public_input_bytes(&pi)).unwrap();
            let sw: Vec<(String, Vec<Vec<verifier::E>>)> = witness.iter()
                .map(|(n, es)| (n.clone(), es.iter().map(|e| e.iter().map(stable::cpu::to_scalar).collect()).collect()))
                .collect();
            std::fs::write(dir.join("advice.txt"), program.export_hints(&sw)).unwrap();
            match s {
                Ok(exec) => {
                    if !exec.unconstrained_reads.is_empty() {
                        println!("{case}: Rust ok with {} unconstrained reads (Lean faults by design)", exec.unconstrained_reads.len());
                    }
                    let memory: Vec<u8> = (0..exec.mem.len()).map(|i| exec.mem.word(i))
                        .flat_map(|w| [w.c0, w.c1]).flat_map(u64::to_le_bytes).collect();
                    std::fs::write(dir.join("memory.bin"), memory).unwrap();
                    let log_mem = exec.mem.len().trailing_zeros();
                    std::fs::write(dir.join("trace.txt"), format!("{log_mem} {} 1\n", exec.cycles)).unwrap();
                    println!("{case}: ok, {} cycles", exec.cycles);
                }
                Err(err) => match lean_fault(&err.fault) {
                    Some(f) => { faults += 1; std::fs::write(dir.join("fault.txt"), format!("{} {f}\n", err.pc)).unwrap(); println!("{case}: fault {} {f}", err.pc); }
                    None => { unsupported += 1; std::fs::remove_dir_all(&dir).unwrap(); println!("{case}: fault not comparable: {err}"); }
                },
            }
        }
    }
    println!("stable/experimental: {agree} agree, {differ} differ; {faults} comparable faults, {unsupported} other faults");
    if differ > 0 {
        std::process::exit(1);
    }
}
