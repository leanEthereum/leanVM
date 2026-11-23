// Written by ../../generate.sh.
fn main() {
    println!("cargo::rerun-if-env-changed=RUSTC_WRAPPER");
    println!("cargo::rerun-if-changed=Cargo.toml");
    println!("cargo::rerun-if-changed=../../../../scripts/tier-rustc");
}
