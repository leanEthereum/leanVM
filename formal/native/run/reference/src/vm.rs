//! The leanVM verifier's cases: the verifier fixtures (`formal/lean_vm/scripts/export-verifier-fixtures-rust.sh`, one
//! directory per proof holding `bytecode.bin`, `public_input.bin` and `proof.wire`), each with its honest wire and
//! altered copies, and what the crate `verifier` (`Proof::from_bytes`, then `verify_execution`) says of each.
//!
//! For a fixture `F` it writes `DIR/vm_F.bytecode` and `DIR/vm_F.public` (the fixture's two files as they are), and per
//! case `DIR/vm_F_<name>.wire` and `DIR/vm_F_<name>.case`, the text `scheme vm`, `expect 0` (or `1`), then
//! `bytecode PATH`, `public PATH`, `wire PATH`, one per line, absolute paths. The harness lays the files out as
//! `rustc/vm/src/lib.rs` requires. The cases: `honest`, the wire as exported; the wire cut (`cut-1`, `cut-8`, `cut-half`,
//! `cut-to-3`, `cut-to-0`, the last ones bytes dropped or the first ones kept) or extended (`extra-1`, `extra-8`, zero
//! bytes appended); and a bit flipped in the first byte (`flip-<field>-lo`, bit 0) and in the last (`flip-<field>-hi`,
//! bit 7) of each field of the encoding (`crates/verifier/src/wire.rs`, `Proof::to_bytes`): the stream's count, its
//! first and last elements, the phase count, and of the first and the last phase (`p0`, `p<k>`) the query count, the
//! positions, the height, the leaf width, the row width, the leaves and the siblings.

use std::collections::BTreeSet;
use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;

/// A field of the encoding: its name, its first byte and its length.
struct Field {
    name: String,
    start: usize,
    len: usize,
}

struct Fields<'a> {
    bytes: &'a [u8],
    at: usize,
    out: Vec<Field>,
}

impl Fields<'_> {
    fn u32(&self, at: usize) -> usize {
        u32::from_le_bytes(self.bytes[at..at + 4].try_into().expect("four bytes")) as usize
    }

    /// The next `len` bytes, as the field `name` if `keep` (and not empty).
    fn take(&mut self, name: String, len: usize, keep: bool) {
        if keep && len > 0 {
            self.out.push(Field { name, start: self.at, len });
        }
        self.at += len;
    }

    /// A `u32` count, as the field `name` if `keep`.
    fn count(&mut self, name: String, keep: bool) -> usize {
        let n = self.u32(self.at);
        self.take(name, 4, keep);
        n
    }
}

/// The fields of an honest encoding (`Proof::to_bytes`), the per-phase ones of the first and the last phase.
fn fields(bytes: &[u8]) -> Vec<Field> {
    let mut f = Fields { bytes, at: 0, out: Vec::new() };
    let stream = f.count("stream-count".into(), true);
    f.take("stream-first".into(), 16, stream > 0);
    f.take(String::new(), 16 * stream.saturating_sub(2), false);
    f.take("stream-last".into(), 16, stream > 1);
    let phases = f.count("phase-count".into(), true);
    for p in 0..phases {
        let keep = p == 0 || p + 1 == phases;
        let queries = f.count(format!("p{p}-query-count"), keep);
        let positions: BTreeSet<usize> = (0..queries).map(|j| f.u32(f.at + 4 * j)).collect();
        f.take(format!("p{p}-positions"), 4 * queries, keep);
        let height = f.count(format!("p{p}-height"), keep);
        f.count(format!("p{p}-leaf-width"), keep);
        let row = f.count(format!("p{p}-row-width"), keep);
        f.take(format!("p{p}-leaves"), 8 * row * positions.len(), keep);
        // The siblings the encoding keeps: per level, those of the level's nodes whose sibling is not a node.
        let mut nodes = positions;
        let mut siblings = 0;
        for _ in 0..height {
            siblings += nodes.iter().filter(|&&node| !nodes.contains(&(node ^ 1))).count();
            nodes = nodes.iter().map(|&node| node >> 1).collect();
        }
        f.take(format!("p{p}-siblings"), 32 * siblings, keep);
    }
    assert_eq!(f.at, bytes.len(), "the wire's fields do not cover it");
    f.out
}

/// The wire's altered copies, by name.
fn variants(wire: &[u8]) -> Vec<(String, Vec<u8>)> {
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
    out
}

/// Adversarial and boundary malformed wire encodings that satisfy `EntryPre` and must be rejected.
fn adversarial_wires(honest: &[u8]) -> Vec<(String, Vec<u8>)> {
    let u32s = |xs: &[u32]| -> Vec<u8> { xs.iter().flat_map(|x| x.to_le_bytes()).collect() };
    let mut out = vec![
        ("bad-stream-u32max".into(), u32s(&[u32::MAX])),
        ("bad-phases-0".into(), u32s(&[0, 0])),
        ("bad-phases-9".into(), u32s(&[0, 9])),
        ("bad-phases-u32max".into(), u32s(&[0, u32::MAX])),
        ("bad-queries-0".into(), u32s(&[0, 1, 0, 1, 1, 1])),
        ("bad-queries-257".into(), u32s(&[0, 1, 257])),
        ("bad-height-33".into(), u32s(&[0, 1, 1, 0, 33, 1, 1])),
        ("bad-leaf-65".into(), u32s(&[0, 1, 1, 0, 1, 65, 1])),
        ("bad-row-gt-leaf".into(), u32s(&[0, 1, 1, 0, 1, 2, 3])),
        ("bad-pos-oob".into(), u32s(&[0, 1, 1, 2, 1, 1, 1])),
    ];
    // Announced-size and trailing-stream mutations on top of an honest wire (stream starts at byte 4,
    // 16 bytes per scalar: log_memory at scalar 0, log_inv_rate at scalar 7).
    let stream_count = u32::from_le_bytes(honest[0..4].try_into().unwrap()) as usize;
    if stream_count >= 8 {
        let mut set_scalar = |name: &str, idx: usize, lo: u64, hi: u64| {
            let mut w = honest.to_vec();
            let off = 4 + 16 * idx;
            w[off..off + 8].copy_from_slice(&lo.to_le_bytes());
            w[off + 8..off + 16].copy_from_slice(&hi.to_le_bytes());
            out.push((name.into(), w));
        };
        set_scalar("bad-ann-logmem-0", 0, 0, 0);
        set_scalar("bad-ann-logmem-31", 0, 31, 0);
        set_scalar("bad-ann-rate-0", 7, 0, 0);
        set_scalar("bad-ann-rate-5", 7, 5, 0);
        let lo0 = u64::from_le_bytes(honest[4..12].try_into().unwrap());
        set_scalar("bad-ann-high-limb", 0, lo0, 1);

        // Append one unconsumed scalar to the stream.
        let mut w = Vec::with_capacity(honest.len() + 16);
        w.extend_from_slice(&(stream_count as u32 + 1).to_le_bytes());
        let stream_end = 4 + 16 * stream_count;
        w.extend_from_slice(&honest[4..stream_end]);
        w.extend_from_slice(&[0u8; 16]);
        w.extend_from_slice(&honest[stream_end..]);
        out.push(("bad-trailing-stream".into(), w));
    }
    out
}

/// What the crate `verifier` says of a wire: it decodes and verifies; only caught verifier panics are silenced.
fn verdict(bytecode: &verifier::Bytecode, public: &[u8; 32], wire: &[u8]) -> bool {
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        verifier::Proof::from_bytes(wire).is_some_and(|proof| verifier::verify_execution(bytecode, public, &proof).is_ok())
    }))
    .unwrap_or(false);
    panic::set_hook(hook);
    result
}

/// Writes the cases of every fixture under `fixtures` to `dir`; returns their stems and verdicts, in order.
pub fn cases(dir: &Path, fixtures: &Path) -> Vec<(String, bool)> {
    let mut found: Vec<_> = fs::read_dir(fixtures)
        .unwrap_or_else(|e| panic!("{}: {e}", fixtures.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("proof.wire").is_file())
        .collect();
    found.sort();
    assert!(!found.is_empty(), "no fixture under {}", fixtures.display());

    let mut list = Vec::new();
    for (fixture_idx, fixture) in found.into_iter().enumerate() {
        let name = fixture.file_name().unwrap().to_str().unwrap().to_string();
        assert!(!name.contains('_'), "{name}: a fixture name with `_`");
        let read = |file: &str| fs::read(fixture.join(file)).unwrap_or_else(|e| panic!("{name}/{file}: {e}"));
        let (bytecode, public, wire) = (read("bytecode.bin"), read("public_input.bin"), read("proof.wire"));
        assert!(bytecode.len() % 8 == 0, "{name}: bytecode.bin is not whole words");
        let words: Vec<u64> = bytecode.chunks_exact(8).map(|w| u64::from_le_bytes(w.try_into().unwrap())).collect();
        let program = verifier::Bytecode::new(&words).unwrap_or_else(|e| panic!("{name}: bytecode: {e}"));
        let public_digest: [u8; 32] = public[..].try_into().unwrap_or_else(|_| panic!("{name}: public input not 32 bytes"));

        let (bytecode_path, public_path) = (dir.join(format!("vm_{name}.bytecode")), dir.join(format!("vm_{name}.public")));
        fs::write(&bytecode_path, &bytecode).unwrap();
        fs::write(&public_path, &public).unwrap();
        let mut emit_case = |variant: &str, bc_path: &Path, pub_path: &Path, w: &[u8], expect: bool| {
            let stem = format!("vm_{name}_{variant}");
            let wire_path = dir.join(format!("{stem}.wire"));
            fs::write(&wire_path, w).unwrap();
            let text = format!(
                "scheme vm\nexpect {}\nbytecode {}\npublic {}\nwire {}\n",
                u8::from(expect),
                bc_path.display(),
                pub_path.display(),
                wire_path.display()
            );
            fs::write(dir.join(format!("{stem}.case")), text).unwrap();
            list.push((stem, expect));
        };

        for (variant, w) in variants(&wire) {
            let expect = verdict(&program, &public_digest, &w);
            assert!(expect || variant != "honest", "vm_{name}_{variant}: the crate rejects the honest proof");
            emit_case(&variant, &bytecode_path, &public_path, &w, expect);
        }

        // Public input mutations (first and last byte).
        for (suffix, byte, bit) in [("lo", 0usize, 0u32), ("hi", 31, 7)] {
            let mut p = public_digest;
            p[byte] ^= 1 << bit;
            let expect = verdict(&program, &p, &wire);
            assert!(!expect, "vm_{name}_flip-public-{suffix}: mutated public input still verifies");
            let p_path = dir.join(format!("vm_{name}_flip-public-{suffix}.public"));
            fs::write(&p_path, p).unwrap();
            emit_case(&format!("flip-public-{suffix}"), &bytecode_path, &p_path, &wire, expect);
        }

        // Bytecode operand mutations: slot 4 of instruction 0 (word `4 * n_insts`) is an unconstrained operand
        // across every opcode, so the mutated bytecode remains a valid LeanISA encoding.
        let n_insts = words.len() >> 4;
        for (suffix, bit) in [("lo", 0u32), ("hi", 63)] {
            let mut w_bc = words.clone();
            w_bc[4 * n_insts] ^= 1u64 << bit;
            let mut_prog = verifier::Bytecode::new(&w_bc).unwrap_or_else(|e| panic!("{name}: mutated bytecode: {e}"));
            let expect = verdict(&mut_prog, &public_digest, &wire);
            assert!(!expect, "vm_{name}_flip-bytecode-{suffix}: mutated bytecode still verifies");
            let bc_bytes: Vec<u8> = w_bc.iter().flat_map(|w| w.to_le_bytes()).collect();
            let b_path = dir.join(format!("vm_{name}_flip-bytecode-{suffix}.bytecode"));
            fs::write(&b_path, bc_bytes).unwrap();
            emit_case(&format!("flip-bytecode-{suffix}"), &b_path, &public_path, &wire, expect);
        }

        // Adversarial malformed wire cases (once, on the first fixture).
        if fixture_idx == 0 {
            for (variant, w) in adversarial_wires(&wire) {
                let expect = verdict(&program, &public_digest, &w);
                assert!(!expect, "vm_{name}_{variant}: adversarial wire verifies");
                emit_case(&variant, &bytecode_path, &public_path, &w, expect);
            }
        }
    }
    list
}
