# Adaptations from PR #738

The guest is `formal/rv64/guest` of `origin/FV-rust-verifier-via-riscv`, copied file by file. What changed for current `main`:

- **A `no_std` verifier without touching `crates/`.** #738 made `crates/verifier` itself `no_std`, and reworked `bytecode.rs`, `layout.rs`, `bus.rs` and `whir.rs` for cycle count. Here `crates/verifier` stays as it is: `../scripts/nostd-verifier.sh` writes a mechanical `no_std` + `alloc` copy to `verifier-nostd/` (gitignored): `std::` becomes `core::` (`alloc::` for `collections`), and each module imports `Box`, `String`, `ToString`, `ToOwned`, `Vec`, `vec!` and `format!` from a crate-level `prelude`. None of #738's algorithmic rewrites are applied. `Cargo.toml` depends on that copy, so run the script before `cargo build`.
- **Scalars are two words.** `E` is now `K[y]/(y^2 + xy + 1)`, two `K` limbs (`E::new(c0, c1)`), so each stream scalar in the input is 2 words, not 3.
- **`Bytecode::new` is fallible.** It returns a `Result` now; an `Err` halts with `a0 = 0` (reject), like any other `VerifierError`.
- Everything else is unchanged: memory map and `link.x`, entry, bump allocator, halting convention, the input's word layout, toolchain `nightly-2026-10-03` with `-Zbuild-std`, rustflags, release profile. The repository's root `.cargo/config.toml` also hands `-C target-cpu=native` to this target, which rustc ignores with one warning per feature, as it did in #738.

Build, from this directory: `../scripts/nostd-verifier.sh && cargo build --release`. Output: `target/riscv64im-unknown-none-elf/release/verifier-rv64`, a static non-PIE `EXEC`, not stripped.
