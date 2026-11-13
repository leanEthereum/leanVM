//! `leanvm-rust-verify`: the deployed Rust verifier of leanVM (`crates/verifier`,
//! `verify_execution`) on a proof's files, so that its verdicts can be set beside the Lean
//! verifier's (`lake exe leanvm-verify`) on the same bytes. Two forms of the proof:
//!
//! * structured: the scalar stream (`stream.bin`, 16-byte little-endian elements, two limbs
//!   each) and the Merkle openings phase by phase (`merkle_phases.bin`), the `verifier` crate's
//!   `Proof { stream, merkle_openings: Vec<Vec<MerklePath>> }` (`crates/verifier/src/transcript.rs`)
//!   written out field by field, every number little-endian: the phase count (`u32`); per phase
//!   its path count (`u32`); per path its `leaf_index` (`u64`), its leaf's length (`u32`) and
//!   words (`u64` each), its sibling count (`u32`) and siblings (32 bytes each). Bytes left over,
//!   or too few, are a rejection;
//! * the wire: `Proof::to_bytes`'s one encoding (`crates/fiat_shamir/src/wire.rs`), decoded by
//!   `Proof::from_bytes`, which unprunes the paths (`None` is a rejection), then verified.
//!
//! The bytecode is read as little-endian 64-bit words (a length that is not a multiple of 8 is
//! rejected) and the public input as 32 bytes (any other length is rejected), as the Lean
//! verifier reads them (`decodeWords`, `decodeDigest`).
//!
//!     leanvm-rust-verify <bytecode> <public input> <stream> <merkle phases>
//!     leanvm-rust-verify <bytecode> <public input> <proof.wire>
//!     leanvm-rust-verify --batch < cases
//!
//! A single case prints `verification succeeded` (exit 0) or `verification failed: <reason>`
//! (exit 1). A panic of the verifier is caught and reported as `verification panicked: <message>`
//! (exit 3): it is a rejection, but one the caller should see. In `--batch` mode every line of
//! standard input names four files (structured) or three (wire), separated by tabs, and one
//! verdict line is printed for it (`accept`, `reject <reason>` or `panic <message>`), in order.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

mod plain;
use plain::Reader;

enum Verdict {
    Accept,
    Reject(String),
    Panic(String),
}

/// The structured Merkle openings (`merkle_phases.bin`, the module's doc).
fn merkle_phases(bytes: &[u8]) -> Result<Vec<Vec<verifier::MerklePath>>, String> {
    let mut input = Reader(bytes);
    let phases = input
        .phases(|leaf_index, leaf, siblings| verifier::MerklePath {
            leaf_index,
            leaf: leaf.into_iter().map(verifier::K).collect(),
            siblings,
        })
        .ok_or("the Merkle phases end early")?;
    if !input.0.is_empty() {
        return Err("bytes after the Merkle phases".into());
    }
    Ok(phases)
}

fn stream(bytes: &[u8]) -> Result<Vec<verifier::E>, String> {
    if bytes.len() % 16 != 0 {
        return Err("the stream is not a whole number of field elements".into());
    }
    let scalars = Reader(bytes).scalars(bytes.len() / 16).expect("a whole number of scalars");
    Ok(scalars.into_iter().map(|[c0, c1]| verifier::E { c0, c1 }).collect())
}

/// `Proof::from_bytes`, then the `verifier` crate's form of the proof (`leanvm_core::cpu::scalar_proof`).
fn wire(bytes: &[u8]) -> Result<verifier::Proof, String> {
    let proof = fiat_shamir::transcript::Proof::from_bytes(bytes).ok_or("wire decoding failed")?;
    let path = |path: &fiat_shamir::merkle::MerklePath| verifier::MerklePath {
        leaf_index: path.leaf_index,
        leaf: path.leaf.iter().map(|word| verifier::K(word.0)).collect(),
        siblings: path.siblings.clone(),
    };
    Ok(verifier::Proof {
        stream: proof
            .stream
            .iter()
            .map(|element| verifier::E { c0: element.c0, c1: element.c1 })
            .collect(),
        merkle_openings: proof.merkle.iter().map(|phase| phase.iter().map(path).collect()).collect(),
    })
}

fn verify_bytes(files: &[Vec<u8>]) -> Result<(), String> {
    let (bytecode, public_input) = (&files[0], &files[1]);
    if bytecode.len() % 8 != 0 {
        return Err("bytecode is not a whole number of 64-bit words".into());
    }
    let table: Vec<u64> = bytecode
        .chunks_exact(8)
        .map(|word| u64::from_le_bytes(word.try_into().expect("eight bytes")))
        .collect();
    let public_input: &[u8; 32] = public_input[..]
        .try_into()
        .map_err(|_| format!("the public input has {} bytes, not 32", public_input.len()))?;
    let proof = match files {
        [_, _, proof] => wire(proof)?,
        [_, _, scalars, phases] => verifier::Proof { stream: stream(scalars)?, merkle_openings: merkle_phases(phases)? },
        _ => unreachable!("three or four files"),
    };
    let bytecode = verifier::Bytecode::new(&table);
    verifier::verify_execution(&bytecode, public_input, &proof)
        .map(|_| ())
        .map_err(|error| error.to_string())
}

fn verify_files(paths: &[&str]) -> Verdict {
    let mut files = Vec::new();
    for path in paths {
        match std::fs::read(path) {
            Ok(bytes) => files.push(bytes),
            Err(error) => return Verdict::Reject(format!("{path}: {error}")),
        }
    }
    match catch_unwind(AssertUnwindSafe(|| verify_bytes(&files))) {
        Ok(Ok(())) => Verdict::Accept,
        Ok(Err(reason)) => Verdict::Reject(reason),
        Err(payload) => Verdict::Panic(
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "a panic without a message".into()),
        ),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [flag] if flag == "--batch" => {
            // Panics are reported on the verdict line, not on standard error.
            std::panic::set_hook(Box::new(|_| {}));
            let stdout = std::io::stdout();
            let mut out = stdout.lock();
            for line in std::io::stdin().lock().lines() {
                let line = line.expect("read standard input");
                if line.is_empty() {
                    continue;
                }
                let paths: Vec<&str> = line.split('\t').collect();
                let verdict = if paths.len() == 3 || paths.len() == 4 {
                    verify_files(&paths)
                } else {
                    Verdict::Reject(format!("expected three or four tab-separated paths: {line}"))
                };
                let text = match verdict {
                    Verdict::Accept => "accept".to_string(),
                    Verdict::Reject(reason) => format!("reject {}", reason.replace('\n', " ")),
                    Verdict::Panic(message) => format!("panic {}", message.replace('\n', " ")),
                };
                writeln!(out, "{text}").expect("write standard output");
                out.flush().expect("flush standard output");
            }
        }
        paths if paths.len() == 3 || paths.len() == 4 => {
            std::panic::set_hook(Box::new(|_| {}));
            let paths: Vec<&str> = paths.iter().map(String::as_str).collect();
            match verify_files(&paths) {
                Verdict::Accept => println!("verification succeeded"),
                Verdict::Reject(reason) => {
                    println!("verification failed: {reason}");
                    std::process::exit(1);
                }
                Verdict::Panic(message) => {
                    println!("verification panicked: {message}");
                    std::process::exit(3);
                }
            }
        }
        _ => {
            eprintln!("usage: leanvm-rust-verify <bytecode> <public input> <stream> <merkle phases>");
            eprintln!("       leanvm-rust-verify <bytecode> <public input> <proof.wire>");
            eprintln!("       leanvm-rust-verify --batch < lines of four or three tab-separated paths");
            std::process::exit(2);
        }
    }
}
