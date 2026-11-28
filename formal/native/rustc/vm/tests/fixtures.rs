//! `leanvm_verify` against the deployed verifier (`Proof::from_bytes`, then `verify_execution`) on
//! the verifier fixtures (`formal/lean_vm/scripts/export-verifier-fixtures-rust.sh DIR`, `DIR` in
//! `$VM_FIXTURES`, else `/tmp/vmfix`) and on altered copies of each wire: `run/reference/src/vm.rs`'s
//! (cut, extended, a bit flipped in the first and the last byte of every field) and bits flipped at
//! pseudo-random positions.

use std::collections::BTreeSet;
use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// `decodedWords L` (`NativeVm/Input.lean`).
fn decoded_words(l: usize) -> usize {
    1 + 2 * (l / 16) + 1 + 8 * (3 + 256 * (1 + 64 + 4 * 32))
}

/// `NativeVm.Code.workWords n`.
fn work_words(n: usize) -> usize {
    (n + 2).max(60720).max(85438)
}

/// The areas of one call: the context, the decoded and the working areas, the wire's words.
struct Areas {
    ctx: Vec<u64>,
    decoded: Vec<u64>,
    work: Vec<u64>,
    wire: Vec<u64>,
}

impl Areas {
    fn new() -> Self {
        Self { ctx: vec![0; 175], decoded: Vec::new(), work: vec![0xa5a5_a5a5_a5a5_a5a5; work_words(0)], wire: Vec::new() }
    }

    /// `leanvm_verify` on the context `NativeVm/Input.lean` lays out.
    fn verify(&mut self, bytecode: &[u64], public: &[u64; 4], wire: &[u8]) -> u64 {
        self.wire.clear();
        self.wire.extend(wire.chunks(8).map(|c| c.iter().rev().fold(0, |w, &b| (w << 8) | u64::from(b))));
        self.decoded.clear();
        self.decoded.resize(decoded_words(wire.len()), 0xa5a5_a5a5_a5a5_a5a5);
        self.work.resize(work_words(bytecode.len()), 0xa5a5_a5a5_a5a5_a5a5);
        let c = &mut self.ctx;
        c[0] = self.wire.as_ptr() as u64;
        c[1] = wire.len() as u64;
        c[2] = bytecode.as_ptr() as u64;
        c[3] = bytecode.len() as u64;
        c[4..8].copy_from_slice(public);
        c[8] = self.decoded.as_mut_ptr() as u64;
        c[9] = self.decoded.len() as u64;
        c[10] = self.work.as_mut_ptr() as u64;
        c[11] = self.work.len() as u64;
        // SAFETY: the context and the areas it points to, as `leanvm_verify` asks.
        unsafe { native_vm::leanvm_verify(c.as_mut_ptr()) }
    }
}

/// A field of the encoding: its name, its first byte, its length (`reference/src/vm.rs`).
struct Field {
    name: String,
    start: usize,
    len: usize,
}

fn u32_at(bytes: &[u8], at: usize) -> usize {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
}

/// The fields of an honest encoding, the per-phase ones of the first and the last phase.
fn fields(bytes: &[u8]) -> Vec<Field> {
    let mut out = Vec::new();
    let mut at = 0;
    let take = |out: &mut Vec<Field>, at: &mut usize, name: String, len: usize, keep: bool| {
        if keep && len > 0 {
            out.push(Field { name, start: *at, len });
        }
        *at += len;
    };
    let stream = u32_at(bytes, at);
    take(&mut out, &mut at, "stream-count".into(), 4, true);
    take(&mut out, &mut at, "stream-first".into(), 16, stream > 0);
    take(&mut out, &mut at, String::new(), 16 * stream.saturating_sub(2), false);
    take(&mut out, &mut at, "stream-last".into(), 16, stream > 1);
    let phases = u32_at(bytes, at);
    take(&mut out, &mut at, "phase-count".into(), 4, true);
    for p in 0..phases {
        let keep = p == 0 || p + 1 == phases;
        let queries = u32_at(bytes, at);
        take(&mut out, &mut at, format!("p{p}-query-count"), 4, keep);
        let positions: BTreeSet<usize> = (0..queries).map(|j| u32_at(bytes, at + 4 * j)).collect();
        take(&mut out, &mut at, format!("p{p}-positions"), 4 * queries, keep);
        let height = u32_at(bytes, at);
        take(&mut out, &mut at, format!("p{p}-height"), 4, keep);
        take(&mut out, &mut at, format!("p{p}-leaf-width"), 4, keep);
        let row = u32_at(bytes, at);
        take(&mut out, &mut at, format!("p{p}-row-width"), 4, keep);
        take(&mut out, &mut at, format!("p{p}-leaves"), 8 * row * positions.len(), keep);
        let mut nodes = positions;
        let mut siblings = 0;
        for _ in 0..height {
            siblings += nodes.iter().filter(|&&node| !nodes.contains(&(node ^ 1))).count();
            nodes = nodes.iter().map(|&node| node >> 1).collect();
        }
        take(&mut out, &mut at, format!("p{p}-siblings"), 32 * siblings, keep);
    }
    assert_eq!(at, bytes.len(), "the wire's fields do not cover it");
    out
}

/// The wire's altered copies, by name: `reference/src/vm.rs`'s, then `random` bit flips.
fn variants(wire: &[u8], random: usize) -> Vec<(String, Vec<u8>)> {
    let l = wire.len();
    let mut out = vec![
        ("honest".to_string(), wire.to_vec()),
        ("cut-1".into(), wire[..l - 1].to_vec()),
        ("cut-8".into(), wire[..l - 8].to_vec()),
        ("cut-half".into(), wire[..l / 2].to_vec()),
        ("cut-to-3".into(), wire[..3].to_vec()),
        ("cut-to-0".into(), Vec::new()),
        ("extra-1".into(), [wire, &[0]].concat()),
        ("extra-8".into(), [wire, &[0; 8]].concat()),
    ];
    for field in fields(wire) {
        for (suffix, byte, bit) in [("lo", field.start, 0), ("hi", field.start + field.len - 1, 7)] {
            let mut w = wire.to_vec();
            w[byte] ^= 1 << bit;
            out.push((format!("flip-{}-{suffix}", field.name), w));
        }
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64 ^ l as u64;
    for k in 0..random {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let bit = (state >> 11) as usize % (8 * l);
        let mut w = wire.to_vec();
        w[bit / 8] ^= 1 << (bit % 8);
        out.push((format!("random-{k}-bit-{bit}"), w));
    }
    out
}

/// What the crate `verifier` says of a wire; a panic is a rejection.
fn reference(bytecode: &verifier::Bytecode, public: &[u8; 32], wire: &[u8]) -> bool {
    panic::catch_unwind(AssertUnwindSafe(|| {
        verifier::Proof::from_bytes(wire).is_some_and(|proof| verifier::verify_execution(bytecode, public, &proof).is_ok())
    }))
    .unwrap_or(false)
}

/// A fixture: its name, bytecode words, public input, wire.
struct Fixture {
    name: String,
    words: Vec<u64>,
    public: [u8; 32],
    wire: Vec<u8>,
}

fn fixtures() -> Vec<Fixture> {
    let dir = PathBuf::from(std::env::var("VM_FIXTURES").unwrap_or_else(|_| "/tmp/vmfix".into()));
    let mut found: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e} (export the fixtures first)", dir.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("proof.wire").is_file())
        .collect();
    found.sort();
    assert!(!found.is_empty(), "no fixture under {}", dir.display());
    found
        .iter()
        .map(|path: &PathBuf| {
            let read = |file: &str| fs::read(Path::new(path).join(file)).unwrap();
            let bytecode = read("bytecode.bin");
            Fixture {
                name: path.file_name().unwrap().to_string_lossy().into_owned(),
                words: bytecode.chunks_exact(8).map(|w| u64::from_le_bytes(w.try_into().unwrap())).collect(),
                public: read("public_input.bin").try_into().unwrap(),
                wire: read("proof.wire"),
            }
        })
        .collect()
}

fn public_words(public: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(public[8 * i..8 * i + 8].try_into().unwrap()))
}

#[test]
fn agrees_with_the_deployed_verifier() {
    let random: usize = std::env::var("VM_RANDOM_FLIPS").ok().and_then(|s| s.parse().ok()).unwrap_or(16);
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut areas = Areas::new();
    let (mut total, mut accepted, mut bad) = (0, 0, Vec::new());
    for f in fixtures() {
        let program = verifier::Bytecode::new(&f.words).unwrap();
        let public = public_words(&f.public);
        for (variant, wire) in variants(&f.wire, random) {
            let expect = reference(&program, &f.public, &wire);
            let got = areas.verify(&f.words, &public, &wire);
            total += 1;
            accepted += usize::from(expect);
            if got != u64::from(expect) {
                bad.push(format!("{}/{variant}: expected {}, got {got}", f.name, u8::from(expect)));
            }
        }
    }
    panic::set_hook(hook);
    assert!(bad.is_empty(), "{} of {total} disagree:\n{}", bad.len(), bad.join("\n"));
    println!("{total} cases agree, {accepted} accepted");
}

/// Times both verifiers on each fixture's honest wire, in this process: `cargo test --release
/// -- --ignored --nocapture timing`.
#[test]
#[ignore]
fn timing() {
    let reps: u32 = std::env::var("VM_REPS").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let mut areas = Areas::new();
    let (mut native_total, mut crate_total) = (0.0, 0.0);
    println!("{:24} {:>12} {:>12} {:>7}", "fixture", "native ms", "crate ms", "ratio");
    for f in fixtures() {
        let program = verifier::Bytecode::new(&f.words).unwrap();
        let public = public_words(&f.public);
        assert_eq!(areas.verify(&f.words, &public, &f.wire), 1);
        let best = |run: &mut dyn FnMut()| {
            (0..reps)
                .map(|_| {
                    let start = Instant::now();
                    run();
                    start.elapsed().as_secs_f64() * 1e3
                })
                .fold(f64::INFINITY, f64::min)
        };
        let native = best(&mut || assert_eq!(areas.verify(&f.words, &public, &f.wire), 1));
        let reference = best(&mut || {
            let proof = verifier::Proof::from_bytes(&f.wire).unwrap();
            verifier::verify_execution(&program, &f.public, &proof).unwrap();
        });
        native_total += native;
        crate_total += reference;
        println!("{:24} {native:12.3} {reference:12.3} {:7.2}", f.name, native / reference);
    }
    println!("{:24} {native_total:12.3} {crate_total:12.3} {:7.2}", "total", native_total / crate_total);
}
