//! Embed every hand-written program under `programs/`, and the compiler's own test programs, as `(name, source)`.

use std::path::{Path, PathBuf};

fn collect(dir: &Path, prefix: &str, out: &mut Vec<(String, PathBuf)>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            collect(&path, &format!("{prefix}{name}/"), out);
        } else if name.ends_with(".py") {
            out.push((format!("{prefix}{name}"), path));
        }
    }
}

fn main() {
    let root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let mut programs = Vec::new();
    let ours = root.join("programs");
    let compiler = root.join("../lean_compiler/tests/programs");
    collect(&ours, "", &mut programs);
    collect(&compiler, "lean_compiler/", &mut programs);
    println!("cargo:rerun-if-changed={}", ours.display());
    println!("cargo:rerun-if-changed={}", compiler.display());
    let mut code = String::from("pub static PROGRAMS: &[(&str, &str)] = &[\n");
    for (name, path) in &programs {
        println!("cargo:rerun-if-changed={}", path.display());
        code += &format!("    ({name:?}, include_str!({:?})),\n", path.canonicalize().unwrap());
    }
    code += "];\n";
    std::fs::write(
        PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("programs.rs"),
        code,
    )
    .unwrap();
}
