//! `--version`: the bindings release (`bindings/Cargo.toml`) and the prover.

fn main() {
    let path = "../../bindings/Cargo.toml";
    println!("cargo::rerun-if-changed={path}");
    let manifest = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let version = manifest
        .split("[workspace.package]")
        .nth(1)
        .and_then(|section| {
            let mut lines = section.lines().take_while(|line| !line.trim_start().starts_with('['));
            lines.find_map(|line| line.trim().strip_prefix("version = "))
        })
        .and_then(|value| value.strip_prefix('"')?.strip_suffix('"'))
        .unwrap_or_else(|| panic!("{path}: no [workspace.package] version"));
    let prover = if std::env::var_os("CARGO_FEATURE_EXPERIMENTAL_PROVER").is_some() {
        "experimental"
    } else {
        "stable"
    };
    println!("cargo::rustc-env=LEANVM_SIDECAR_VERSION={version} ({prover} prover)");
}
