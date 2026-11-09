# Extracting

## Tools

`tools/extract/extract.sh --tools-only` checks each pin in `toolchain.toml` and prints the install command for a missing one:

| Tool | Install |
|---|---|
| cargo-hax | `cargo install --locked --git https://github.com/cryspen/hax --rev <hax_commit> cargo-hax --force` |
| charon, aeneas | `cargo hax tools install` |
| charon's Rust | `rustup toolchain install <rust_toolchain> --profile minimal --component rustc-dev,llvm-tools,rust-src --target <target>` |

## Running

```sh
tools/extract/extract.sh            # extract every crate not in state `stub`, install, build
tools/extract/extract.sh --check    # and fail unless the output is what is committed
```

## A crate's first extraction

1. In its `crate.toml`, set `state = "extracted"` (or `"scoped"` with `start_from`). Delete `stub/`, and point its `srcDir` in `lakefile.toml` at `crates/<crate>/extraction`.
2. Write `extraction/<Lib>.lean`, importing `<Lib>.Extraction`.
3. Run `tools/extract/extract.sh`. It stops at each template with no `Assumptions/` file: write it, each hole `opaque` or mirrored.
4. Where an item does not extract, prefer a pre patch to a transcription. Its header says what it changes and why the meaning is kept.
5. Run `tools/check-layout.py` and `tools/extract/extract.sh --check`.

## Moving a pin

hax, charon and aeneas move together with the `aeneas` and `hax` revs in `lakefile.toml` and with `lean-toolchain`. Aeneas's Mathlib must be the statement's, so a Lean bump of `formal/` and a hax bump are one change.
