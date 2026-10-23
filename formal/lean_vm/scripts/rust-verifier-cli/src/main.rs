//! `leanvm-rust-verify`: the deployed Rust verifier of leanVM (`crates/verifier`,
//! `verify_execution`) on the four files the Python verifier's CLI reads
//! (`python-verifier/verifier.py`, `main`), so that its verdicts can be set beside the Lean
//! verifier's (`lake exe leanvm-verify`) on the same bytes.
//!
//! The files are decoded as the Python's `main` decodes them: the bytecode as little-endian
//! 64-bit words (a length that is not a multiple of 8 is rejected), the public input as 32 bytes
//! (any other length is rejected), and the stream and openings by `verifier::Proof::load`, the
//! `verifier` crate's reader of exactly this encoding.
//!
//!     leanvm-rust-verify <bytecode> <public input> <stream> <openings>
//!     leanvm-rust-verify --batch < cases
//!
//! The first form prints `verification succeeded` (exit 0) or `verification failed: <reason>`
//! (exit 1). A panic of the verifier is caught and reported as `verification panicked: <message>`
//! (exit 3): it is a rejection, but one the caller should see. In `--batch` mode every line of
//! standard input names four files, separated by tabs, and one verdict line is printed for it
//! (`accept`, `reject <reason>` or `panic <message>`), in order.

use std::io::{BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

enum Verdict {
    Accept,
    Reject(String),
    Panic(String),
}

fn verify_bytes(bytecode: &[u8], public_input: &[u8], stream: &[u8], openings: &[u8]) -> Result<(), String> {
    if bytecode.len() % 8 != 0 {
        return Err("bytecode is not a whole number of 64-bit words".into());
    }
    let table: Vec<u64> = bytecode
        .chunks_exact(8)
        .map(|word| u64::from_le_bytes(word.try_into().expect("eight bytes")))
        .collect();
    let public_input: &[u8; 32] = public_input
        .try_into()
        .map_err(|_| format!("the public input has {} bytes, not 32", public_input.len()))?;
    let proof = verifier::Proof::load(stream, openings).map_err(|error| error.to_string())?;
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
    match catch_unwind(AssertUnwindSafe(|| verify_bytes(&files[0], &files[1], &files[2], &files[3]))) {
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
                let verdict = if paths.len() == 4 {
                    verify_files(&paths)
                } else {
                    Verdict::Reject(format!("expected four tab-separated paths: {line}"))
                };
                let text = match verdict {
                    Verdict::Accept => "accept".to_string(),
                    Verdict::Reject(reason) => format!("reject {reason}"),
                    Verdict::Panic(message) => format!("panic {}", message.replace('\n', " ")),
                };
                writeln!(out, "{text}").expect("write standard output");
                out.flush().expect("flush standard output");
            }
        }
        [bytecode, public_input, stream, openings] => {
            std::panic::set_hook(Box::new(|_| {}));
            match verify_files(&[bytecode, public_input, stream, openings]) {
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
            eprintln!("usage: leanvm-rust-verify <bytecode> <public input> <stream> <openings>");
            eprintln!("       leanvm-rust-verify --batch < lines of four tab-separated paths");
            std::process::exit(2);
        }
    }
}
