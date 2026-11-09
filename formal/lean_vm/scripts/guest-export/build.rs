//! The overlay: leanVM's `rec_aggregation` sources, copied verbatim into `OUT_DIR` (the guest
//! with them, so their `include_str!("../guests/lean_ethereum.py")` still resolves), with one
//! line appended to `aggregation.rs` that declares this crate's `src/export/` as its child
//! module `lean_export`. Nothing under `crates/` is written.

use std::path::{Path, PathBuf};

/// leanVM, relative to this crate: this repository. `LEANVM_DIR` overrides it.
const DEFAULT_LEANVM: &str = "../../../..";

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_file() {
            println!("cargo:rerun-if-changed={}", path.display());
            std::fs::copy(&path, to.join(entry.file_name())).unwrap();
        } else if path.is_dir() {
            copy_dir(&path, &to.join(entry.file_name()));
        }
    }
}

/// Every `.rs` file under `dir`.
fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// A named field's line, `    name: T,`, made crate-visible.
fn widen_named_field(l: &str) -> String {
    match l.strip_prefix("    ") {
        Some(rest)
            if rest.split_once(':').is_some_and(|(n, _)| {
                !n.is_empty() && n.chars().all(|c| c.is_alphanumeric() || c == '_')
            }) =>
        {
            format!("    pub(crate) {rest}")
        }
        _ => l.to_string(),
    }
}

/// A one-line tuple struct `pub(crate) struct N(A, B);` with its private fields made crate-visible.
fn widen_tuple_fields(l: &str) -> String {
    let Some(head_end) = l.strip_prefix("pub(crate) struct ").and_then(|r| {
        let name_len = r.find(|c: char| !(c.is_alphanumeric() || c == '_'))?;
        r[name_len..].starts_with('(').then_some("pub(crate) struct ".len() + name_len + 1)
    }) else {
        return l.to_string();
    };
    let Some(body) = l[head_end..].strip_suffix(");") else { return l.to_string() };
    // The fields, split at the commas outside brackets.
    let (mut fields, mut depth, mut start) = (Vec::new(), 0i32, 0);
    for (i, c) in body.char_indices() {
        match c {
            '(' | '<' | '[' => depth += 1,
            ')' | '>' | ']' => depth -= 1,
            ',' if depth == 0 => {
                fields.push(&body[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    fields.push(&body[start..]);
    let fields: Vec<String> = fields
        .iter()
        .map(|f| {
            let f = f.trim();
            if f.is_empty() || f.starts_with("pub") { f.to_string() } else { format!("pub(crate) {f}") }
        })
        .collect();
    format!("{}{});", &l[..head_end], fields.join(", "))
}

fn main() {
    println!("cargo:rerun-if-env-changed=LEANVM_DIR");
    println!("cargo:rerun-if-changed=build.rs");
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let leanvm = std::env::var("LEANVM_DIR").map(PathBuf::from).unwrap_or_else(|_| manifest.join(DEFAULT_LEANVM));
    let leanvm = leanvm
        .canonicalize()
        .unwrap_or_else(|e| panic!("leanVM's tree {}: {e}", leanvm.display()));
    let crate_dir = leanvm.join("crates/rec_aggregation");
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("rec_aggregation");
    // A fresh copy: a file leanVM moved or removed must not linger from an earlier pin.
    let _ = std::fs::remove_dir_all(&out);
    copy_dir(&crate_dir.join("src"), &out.join("src"));
    copy_dir(&crate_dir.join("guests"), &out.join("guests"));

    let export = manifest.join("src/export/mod.rs");
    // `aggregation` is a directory module (`aggregation/mod.rs`) since leanVM #670.
    let aggregation = [out.join("src/aggregation/mod.rs"), out.join("src/aggregation.rs")]
        .into_iter()
        .find(|p| p.is_file())
        .expect("rec_aggregation has an aggregation module");
    // Since #670 the module's private items live in its submodules: the exporters, a child of
    // `aggregation`, read them as they read `aggregation.rs`'s, so every top-level item there is
    // made crate-visible, and so is every field of a struct declared there (a tuple struct's on
    // its line, a named struct's at four spaces in its block); only the copy, the module's own
    // `pub` items are unchanged.
    if aggregation.ends_with("mod.rs") {
        let mut files = Vec::new();
        rust_files(aggregation.parent().unwrap(), &mut files);
        for f in files.iter().filter(|f| **f != aggregation) {
            let text = std::fs::read_to_string(f).unwrap();
            let mut in_struct = false;
            let text: String = text
                .lines()
                .map(|l| {
                    let item = ["fn ", "struct ", "enum ", "const ", "type ", "static ", "trait ", "mod "]
                        .iter()
                        .any(|k| l.starts_with(k))
                        && !l.starts_with("const _");
                    let l = l.replacen("pub(super) ", "pub(crate) ", 1);
                    let l = if item { format!("pub(crate) {l}") } else { l };
                    let l = if in_struct { widen_named_field(&l) } else { widen_tuple_fields(&l) };
                    if l.starts_with("pub(crate) struct ") && l.ends_with('{') {
                        in_struct = true;
                    } else if l.starts_with('}') {
                        in_struct = false;
                    }
                    format!("{l}\n")
                })
                .collect();
            std::fs::write(f, text).unwrap();
        }
    }
    let mut text = std::fs::read_to_string(&aggregation).unwrap();
    text.push_str(&format!(
        "\n// Appended by leanvm-guest-export's build.rs.\n#[path = {:?}]\npub mod lean_export;\n",
        export.display().to_string()
    ));
    std::fs::write(&aggregation, text).unwrap();

    // leanVM's `lean_compiler` as this crate's module `compiler_overlay`, for the exporters that
    // read the parsed guest (`Ast`'s functions are crate-private since leanVM #669): its sources
    // copied, `lib.rs` as the module's `mod.rs`, and `crate::` paths pointed at the module.
    let compiler = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("compiler_overlay");
    let _ = std::fs::remove_dir_all(&compiler);
    copy_dir(&leanvm.join("crates/lean_compiler/src"), &compiler);
    std::fs::rename(compiler.join("lib.rs"), compiler.join("mod.rs")).unwrap();
    let mut files = Vec::new();
    rust_files(&compiler, &mut files);
    for f in files {
        let text = std::fs::read_to_string(&f).unwrap();
        std::fs::write(&f, text.replace("crate::", "crate::compiler_overlay::")).unwrap();
    }

    // The leanVM checkout and commit the data is exported from, for the generated headers.
    // The headers name the commit the formalization cites (`formal/leanvm-rev`), not this tree's
    // HEAD, so the data stays current across commits that leave the guest alone.
    let pin = manifest.join("../../../leanvm-rev");
    let rev = std::fs::read_to_string(&pin).unwrap_or_else(|e| panic!("{}: {e}", pin.display()));
    println!("cargo:rustc-env=LEANVM_REV={}", rev.trim());
    println!("cargo:rerun-if-changed={}", pin.display());
    println!("cargo:rustc-env=LEANVM_DIR={}", leanvm.display());

    let overlay = format!(
        "#[path = {:?}]\npub mod aggregation;\n\n#[cfg(feature = \"signers-cache\")]\n#[path = {:?}]\npub mod signers_cache;\n\n#[path = {:?}]\npub mod compiler_overlay;\n",
        aggregation.display().to_string(),
        out.join("src/signers_cache.rs").display().to_string(),
        compiler.join("mod.rs").display().to_string()
    );
    std::fs::write(out.join("overlay.rs"), overlay).unwrap();
}
