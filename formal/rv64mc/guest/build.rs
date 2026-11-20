fn main() {
    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-link-arg=-T{dir}/link.x");
    // Keep the relocations in the image: they pair each `auipc` with its users exactly, for the proof generator.
    println!("cargo:rustc-link-arg=--emit-relocs");
    // No linker relaxation: a call stays `auipc; jalr` whatever its distance, so code size does not depend on layout.
    println!("cargo:rustc-link-arg=--no-relax");
    println!("cargo:rerun-if-changed=link.x");
}
