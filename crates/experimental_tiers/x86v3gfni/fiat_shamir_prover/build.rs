// Written by ../../generate.sh.
fn main() {
    println!("cargo::rerun-if-env-changed=RUSTC_WRAPPER");
    println!("cargo::rerun-if-changed=Cargo.toml");
    let wrapper = "../../../../scripts/tier-rustc";
    if std::path::Path::new(wrapper).exists() {
        println!("cargo::rerun-if-changed={wrapper}");
    }
}
