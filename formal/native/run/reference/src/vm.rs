//! The leanVM verifier's cases: the verifier fixtures (`formal/lean_vm/scripts/export-verifier-fixtures-rust.sh`, one
//! directory per proof holding `bytecode.bin`, `public_input.bin` and `proof.wire`), each with its honest wire and
//! altered copies, and what the crate `verifier` (`Proof::from_bytes`, then `verify_execution`) says of each.
//!
//! For a fixture `F` it writes `DIR/vm_F.bytecode` and `DIR/vm_F.public` (the fixture's two files as they are), and per
//! case `DIR/vm_F_<name>.wire` and `DIR/vm_F_<name>.case`, the text `scheme vm`, `expect 0` (or `1`), then
//! `bytecode PATH`, `public PATH`, `wire PATH`, one per line, absolute paths. The harness lays the files out as
//! `NativeVm/Input.lean` says. The cases: `honest`, the wire as exported; the wire cut (`cut-1`, `cut-8`, `cut-half`,
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

/// What the crate `verifier` says of a wire: it decodes and verifies; a panic is a rejection.
fn verdict(bytecode: &verifier::Bytecode, public: &[u8; 32], wire: &[u8]) -> bool {
    panic::catch_unwind(AssertUnwindSafe(|| {
        verifier::Proof::from_bytes(wire).is_some_and(|proof| verifier::verify_execution(bytecode, public, &proof).is_ok())
    }))
    .unwrap_or(false)
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

    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut list = Vec::new();
    for fixture in found {
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
        for (variant, w) in variants(&wire) {
            let stem = format!("vm_{name}_{variant}");
            let expect = verdict(&program, &public_digest, &w);
            assert!(expect || variant != "honest", "{stem}: the crate rejects the honest proof");
            let wire_path = dir.join(format!("{stem}.wire"));
            fs::write(&wire_path, &w).unwrap();
            let text = format!(
                "scheme vm\nexpect {}\nbytecode {}\npublic {}\nwire {}\n",
                u8::from(expect),
                bytecode_path.display(),
                public_path.display(),
                wire_path.display()
            );
            fs::write(dir.join(format!("{stem}.case")), text).unwrap();
            list.push((stem, expect));
        }
    }
    panic::set_hook(hook);
    list
}
