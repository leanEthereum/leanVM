//! The guest the prover loads, `guests/lean_ethereum.compiled`, is the Lean back end's compilation of
//! `guests/lean_ethereum.py` at the fixed point on its own size, and it is not committed: this script writes it with
//! `formal/lean_vm/scripts/guest-artifact` when a file it is compiled from changed since the last build, or takes the
//! file `LEANVM_GUEST_ARTIFACT` names, written by that script from the same tree.

use std::path::{Path, PathBuf};
use std::process::Command;

/// What the artefact is compiled from: the guest, the placeholders (this crate's sources), the source's export
/// (`guest-export --source`, with the parser), and the Lean back end with its driver. Directories holding a `.lake`
/// are not listed, since a Lean build writes there.
const INPUTS: &[&str] = &[
    "guests/lean_ethereum.py",
    "crates/aggregation/src",
    "crates/zkdsl/src",
    "formal/lean_vm/scripts/guest-artifact",
    "formal/lean_vm/scripts/guest-export/src",
    "formal/lean_vm/scripts/guest-export/build.rs",
    "formal/lean_vm/scripts/guest-export/Cargo.toml",
    "formal/lean_vm/cli/GuestArtifact.lean",
    "formal/lean_vm/LeanVM/Compiler",
    "formal/lean_vm/LeanVM/Core",
    "formal/lean_vm/lakefile.toml",
    "formal/lean_vm/lake-manifest.json",
    "formal/lean_vm/lean-toolchain",
    "formal/Statement/Fast",
    "formal/Statement/Field.lean",
    "formal/Statement/Keccak.lean",
    "formal/Statement/LeanIsa.lean",
    "formal/Statement/LeanVmVerifier.lean",
    "guests/lean_ethereum.compiled",
];

/// The variables a build script inherits that would retarget the nested cargo build of `guest-export` (a wrapper such
/// as clippy's, another target's flags or target directory).
const NESTED_CARGO_UNSET: &[&str] = &[
    "CARGO_TARGET_DIR",
    "CARGO_BUILD_TARGET",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTFLAGS",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CLIPPY_ARGS",
    "CARGO_MAKEFLAGS",
    "MAKEFLAGS",
    "MFLAGS",
];

fn main() {
    let root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    println!("cargo:rerun-if-env-changed=LEANVM_GUEST_ARTIFACT");
    let artifact = match std::env::var_os("LEANVM_GUEST_ARTIFACT") {
        Some(path) => {
            let path = PathBuf::from(path);
            println!("cargo:rerun-if-changed={}", path.display());
            path
        }
        None => {
            for input in INPUTS {
                println!("cargo:rerun-if-changed={}", root.join(input).display());
            }
            write_artifact(&root);
            root.join("guests/lean_ethereum.compiled")
        }
    };
    let artifact = artifact
        .canonicalize()
        .unwrap_or_else(|e| panic!("the guest's artefact {}: {e}", artifact.display()));
    println!("cargo:rustc-env=LEANVM_GUEST_ARTIFACT_PATH={}", artifact.display());
}

/// `lake`'s directory: on the `PATH`, else elan's default.
fn lean_bin() -> Option<PathBuf> {
    let on_path = Command::new("lake").arg("--version").output().is_ok_and(|o| o.status.success());
    if on_path {
        return Some(PathBuf::new());
    }
    let elan = std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".elan")))?;
    elan.join("bin/lake").is_file().then(|| elan.join("bin"))
}

fn write_artifact(root: &Path) {
    let Some(bin) = lean_bin() else {
        panic!(
            "building `aggregation` compiles the guest with the Lean back end (formal/lean_vm/scripts/guest-artifact), \
             which needs the Lean toolchain: install elan (https://github.com/leanprover/elan), which reads \
             formal/lean_vm/lean-toolchain, and python3; or set LEANVM_GUEST_ARTIFACT to a guests/lean_ethereum.compiled \
             that script wrote from this tree"
        )
    };
    let mut cmd = Command::new(root.join("formal/lean_vm/scripts/guest-artifact"));
    for var in NESTED_CARGO_UNSET {
        cmd.env_remove(var);
    }
    if !bin.as_os_str().is_empty() {
        let path = std::env::var_os("PATH").unwrap_or_default();
        let paths = std::iter::once(bin).chain(std::env::split_paths(&path));
        cmd.env("PATH", std::env::join_paths(paths).unwrap());
    }
    // Its progress on stderr: a build script's stdout is cargo's instructions.
    cmd.stdout(std::process::Stdio::from(std::io::stderr()));
    let status = cmd.status().unwrap_or_else(|e| panic!("formal/lean_vm/scripts/guest-artifact: {e}"));
    assert!(
        status.success(),
        "formal/lean_vm/scripts/guest-artifact failed ({status}): the guest does not compile, or its Lean build failed"
    );
}
