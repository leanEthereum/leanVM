//! `leanvm-rust-wire`: leanVM's proof wire encoding (`crates/fiat_shamir/src/wire.rs`,
//! `Proof::from_bytes` and `Proof::to_bytes`) on byte files, so that `scripts/wire-diff.py` can set
//! its results beside the Lean transcription's (`lake exe wire-diff`, cli/WireDiff.lean) on the
//! same bytes.
//!
//!     leanvm-rust-wire decode <wire> <plain out>
//!     leanvm-rust-wire encode <plain> <wire out>
//!     leanvm-rust-wire vector <wire out>
//!     leanvm-rust-wire --batch < lines of tab-separated commands
//!
//! `decode` runs `Proof::from_bytes` and prints `none`, or `some`, writing the proof it gives in the
//! plain rendering below, followed by `reencode-ok` when `Proof::to_bytes` of it gives back the
//! input and `reencode-differs` otherwise. `encode` reads a proof in the plain rendering and writes
//! `Proof::to_bytes` of it, printing `encoded`, followed by `roundtrip-ok` when `Proof::from_bytes`
//! gives back the proof (`roundtrip-differs` otherwise); `malformed` for a file that is no plain
//! rendering. `vector` writes the bytes of the proof of wire.rs's test
//! `proof_round_trips_through_its_one_encoding`, after checking the test's assertions on them, and
//! prints `vector <length>`. A panic is printed as `panic <message>`. In `--batch` mode every line
//! of standard input is one command, its words separated by tabs, and one result line is printed
//! for it, in order.
//!
//! The plain rendering of a proof hashes nothing and prunes nothing: every count a little-endian
//! `u32`, every word and position a little-endian `u64`; the stream's length and its elements, each
//! three words `c0, c1, c2`; the number of phases, and for each its number of paths, and for each
//! path its position, its leaf's length and words, its siblings' count and their 32 bytes each.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use fiat_shamir::merkle::{MerklePath, hash_pair, hash_words, open};
use fiat_shamir::transcript::Proof;
use primitives::field::{F64, F192};

#[path = "../../rust-verifier-cli/src/plain.rs"]
mod plain;
use plain::Reader;

fn put_u32(out: &mut Vec<u8>, value: usize) {
    out.extend(u32::try_from(value).expect("a count fits in u32").to_le_bytes());
}

/// The plain rendering of `proof`.
fn plain(proof: &Proof) -> Vec<u8> {
    let mut out = Vec::new();
    put_u32(&mut out, proof.stream.len());
    for element in &proof.stream {
        for word in [element.c0, element.c1, element.c2] {
            out.extend(word.to_le_bytes());
        }
    }
    put_u32(&mut out, proof.merkle.len());
    for phase in &proof.merkle {
        put_u32(&mut out, phase.len());
        for path in phase {
            out.extend(path.leaf_index.to_le_bytes());
            put_u32(&mut out, path.leaf.len());
            for word in &path.leaf {
                out.extend(word.0.to_le_bytes());
            }
            put_u32(&mut out, path.siblings.len());
            for sibling in &path.siblings {
                out.extend(sibling);
            }
        }
    }
    out
}

/// The proof whose plain rendering `bytes` are, if they are one.
fn from_plain(bytes: &[u8]) -> Option<Proof> {
    let mut input = Reader(bytes);
    let count = input.u32()?;
    let stream = input.scalars(count)?.into_iter().map(|[c0, c1, c2]| F192::new(c0, c1, c2)).collect();
    let merkle = input.phases(|leaf_index, leaf, siblings| MerklePath {
        leaf_index,
        leaf: leaf.into_iter().map(F64).collect(),
        siblings,
    })?;
    input.0.is_empty().then_some(Proof { stream, merkle })
}

/// The proof of wire.rs's test `proof_round_trips_through_its_one_encoding`, its encoding, with the
/// test's assertions checked.
fn vector() -> Vec<u8> {
    let rows = [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]].map(|row| row.map(F64));
    let leaf = |q: usize| hash_words(&rows[q]);
    let node = |level: usize, i: usize| match level {
        0 => leaf(i),
        _ => hash_pair(&leaf(2 * i), &leaf(2 * i + 1)),
    };
    let proof = Proof {
        stream: vec![F192::new(1, 2, 3)],
        merkle: vec![open(4, &[3, 1, 3], 3, node, |q| &rows[q])],
    };
    let bytes = proof.to_bytes();
    assert_eq!(bytes.len(), (4 + 24) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 2 * 32);
    assert_eq!(Proof::from_bytes(&bytes), Some(proof));
    assert_eq!(Proof::from_bytes(&[&bytes[..], &[0]].concat()), None);
    bytes
}

fn decode(input: &str, output: &str) -> Result<String, String> {
    let bytes = std::fs::read(input).map_err(|e| format!("{input}: {e}"))?;
    Ok(match Proof::from_bytes(&bytes) {
        None => "none".into(),
        Some(proof) => {
            std::fs::write(output, plain(&proof)).map_err(|e| format!("{output}: {e}"))?;
            let again = catch_unwind(AssertUnwindSafe(|| proof.to_bytes()));
            match again {
                Ok(again) if again == bytes => "some reencode-ok".into(),
                Ok(_) => "some reencode-differs".into(),
                Err(_) => "some reencode-panic".into(),
            }
        }
    })
}

fn encode(input: &str, output: &str) -> Result<String, String> {
    let bytes = std::fs::read(input).map_err(|e| format!("{input}: {e}"))?;
    let Some(proof) = from_plain(&bytes) else {
        return Ok("malformed".into());
    };
    let wire = proof.to_bytes();
    std::fs::write(output, &wire).map_err(|e| format!("{output}: {e}"))?;
    Ok(if Proof::from_bytes(&wire).as_ref() == Some(&proof) {
        "encoded roundtrip-ok".into()
    } else {
        "encoded roundtrip-differs".into()
    })
}

fn run(words: &[&str]) -> String {
    let result = catch_unwind(AssertUnwindSafe(|| match words {
        ["decode", input, output] => decode(input, output),
        ["encode", input, output] => encode(input, output),
        ["vector", output] => {
            let bytes = vector();
            std::fs::write(output, &bytes)
                .map(|()| format!("vector {}", bytes.len()))
                .map_err(|e| format!("{output}: {e}"))
        }
        _ => Err(format!("unknown command: {}", words.join(" "))),
    }));
    match result {
        Ok(Ok(line)) => line,
        Ok(Err(error)) => format!("error {error}"),
        Err(payload) => format!(
            "panic {}",
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "a panic without a message".into())
                .replace('\n', " ")
        ),
    }
}

fn main() {
    // Panics are reported on the result line, not on standard error.
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["--batch"] => {
            let stdout = std::io::stdout();
            let mut out = stdout.lock();
            for line in std::io::stdin().lock().lines() {
                let line = line.expect("read standard input");
                if line.is_empty() {
                    continue;
                }
                let words: Vec<&str> = line.split('\t').collect();
                writeln!(out, "{}", run(&words)).expect("write standard output");
                out.flush().expect("flush standard output");
            }
        }
        [] => {
            eprintln!("usage: leanvm-rust-wire decode <wire> <plain out> | encode <plain> <wire out>");
            eprintln!("       leanvm-rust-wire vector <wire out> | --batch < lines of tab-separated commands");
            std::process::exit(2);
        }
        words => {
            let line = run(words);
            println!("{line}");
            if line.starts_with("error") || line.starts_with("panic") {
                std::process::exit(1);
            }
        }
    }
}
