# Rust to Lean extraction

The Rust crates that declare a scenario are translated to Lean by [hax](https://hax.cryspen.com/)'s Lean backend (Charon, then Aeneas), so that Lean can state and prove things about the code that runs, not about a transcription of it. This directory is the infrastructure: one command extracts and typechecks, and nothing it generates is committed. Nothing is proved here yet. What the extractions leave out, and why, is in [LIMITATIONS.md](LIMITATIONS.md).

Extracted today: `verifier`, `keccak256`, `lean_xmss` and `lean_sphincs`. Adding a crate is a `hax.toml` beside its `Cargo.toml` ([Adding a crate](#adding-a-crate)).

## Using it

```bash
formal/extraction/hax.sh setup      # once: cargo-hax, charon, aeneas, charon's Rust nightly
formal/extraction/hax.sh check      # extract every scenario, build it in Lean, print the report
```

`check` is what CI runs. `hax.sh extract` alone regenerates the Lean without building it (`-p <crate>` for one crate), and `cd formal/extraction && lake build` builds what is there. Lean comes from [elan](https://github.com/leanprover/elan), which reads `lean-toolchain`.

The extraction never blocks a Rust change. The `Extraction` workflow runs weekly, on demand, and on pull requests that change the extraction itself. When the Rust has moved under it, `repair.py` brings it back ([After the Rust changes](#after-the-rust-changes)), and `.claude/skills/update-extraction` walks an agent through it.

## Layout

```
hax.toml                                  pins charon, aeneas, the Lean toolchain and the hax Lean library
crates/<crate>/hax.toml                   the crate's scenario: what is extracted, what is left opaque and why
crates/<crate>/proofs/<scenario>/
  patches/pre/NN-*.patch                  Rust rewrites, applied only while extracting
  patches/pre/tests                       optional: the tests that pin what the patches touch
  patches/post/NN-*.patch                 rewrites of the generated Lean (a last resort)
  lean/                                   generated and gitignored: the Lean package hax writes
    <Pkg>/Extraction/                     the translation
    <Pkg>/Assumptions/                    the Rust items left opaque, as axioms
formal/extraction/
  hax.sh                                  setup, extract, check, test, run commands on the patched source
  repair.py                               after the Rust changed: re-fits the patches, leaves opaque what no longer translates
  mechanical.py                           generates the patch of the rewrites that recur everywhere (run by hax.sh)
  wire.py                                 wires every package into this workspace (run by hax.sh)
  report.sh                               what each extraction takes on trust, as a table
  CoreModelsExt/                          models of standard-library items the hax Lean library lacks
  proofs/<crate>/                         proofs about an extraction, a Lake package of their own (proofs/lean_sphincs/README.md)
  lakefile.toml, Extraction/              generated and gitignored: the workspace, written by wire.py
```

Committed: the scenarios, the patches, the scripts, `CoreModelsExt` and the proofs. Generated: everything under a `lean/` directory, and this workspace's lakefile, manifest and `Extraction/` roots. The one committed lock of the Lean dependencies is `CoreModelsExt/lake-manifest.json`, which every generated manifest copies; `lake update` in `CoreModelsExt` moves it.

A scenario's `opaque` list names the items extracted as signatures only (axioms in `Assumptions/`), and its `exclude` list the items left out altogether. Each entry sits under a comment saying what stops it, so the lists are also the work left.

This directory is the one Lake workspace: it requires every package by path, with `CoreModelsExt`, so Aeneas's Lean library, the hax Lean library and Mathlib resolve once, in `formal/extraction/.lake/packages`. A crate's extraction imports those of the crates it depends on, which declare the items it uses from them.

The extraction is of the portable code: `hax.sh` switches off the hardware features the crates dispatch on, so every `cfg(target_feature)` choice takes its fallback and the result is the same on any host.

## After the Rust changes

Most changes extract cleanly and need nothing. When `hax.sh check` (or the weekly workflow) fails:

```bash
formal/extraction/repair.py patches     # keep the patch hunks whose context is still there, drop the rest
formal/extraction/repair.py extract     # every scenario, in dependency order (or name crate directories)
formal/extraction/hax.sh test           # clippy and the tests, on the patched source
formal/extraction/hax.sh check
```

`repair.py extract` runs the extraction and the Lean build of each crate, round after round, until both pass. Whatever Aeneas leaves a `sorry` in, ignores the body of, or Lean rejects goes on the scenario's `opaque` list under a "Not yet triaged" heading, with the error reported. An item whose signature is the problem goes on `exclude`, and an entry naming an item that is gone is removed. It prints each change. It only ever makes the extraction smaller, so what it adds is the list to work back down ([Winning items back](#winning-items-back)).

What it does not do:

- **A crate that is renamed, moved or split** needs its `hax.toml` scenario and `proofs/<scenario>/patches` moved with it (`git mv`), and the old generated `lean/` directory deleted.
- **A crash that names no item** (Aeneas stops on the whole crate) is bisected by marking modules opaque (`"crate::module"`), then narrowed.
- **A patch hunk that still applies can be wrong for the new code.** `repair.py patches` checks context, not meaning. `hax.sh test` is what catches it.

Run one extraction at a time in a checkout: `hax.sh` patches the source while it runs, and reverts it after.

## Winning items back

An opaque item becomes a translated one by the cheapest of these that works. Take the entry off the list, then `repair.py extract <crate dir>` says whether it holds.

1. **A model in `CoreModelsExt`**, when Lean reports an unknown `core.*` or `alloc.*` constant: a definition where the Rust is short, an `opaque` otherwise. One model clears every crate that uses the item.
2. **A rule in `mechanical.py`**, when the same rewrite recurs across crates. It is regenerated from the source on every run, so it never goes stale.
3. **A patch in `patches/pre/`**, for an item worth having a body for. Each patch is upkeep when the code under it changes, so keep them few and small.
4. **Leave it opaque**, with the reason.

Generated Lean is never edited by hand: what cannot be fixed in the Rust or by a model goes in a `post/` patch, applied to the output of every extraction.

## Patches

A patch in `pre/` rewrites Rust the toolchain cannot translate into Rust it can, without changing what it computes: an iterator adapter whose closure takes a reference becomes a fold or a loop, a mutable iterator becomes an indexed loop, a function-pointer field becomes a method. Patches are applied in name order for the length of `hax.sh extract` and reverted after, so the committed source never carries them.

Before them, `hax.sh` applies a patch it generates, with `mechanical.py`, from the source as it stands. Tracing spans go (`#[tracing::instrument]`, span guards, `in_scope` wrappers), and each anonymous `const _: () = assert!(..)`, whose Aeneas name `__N` Lean rejects, is named `_ASSERT_<hash>` after a hash of its item. A scenario names such an assertion by that name, which `python3 formal/extraction/mechanical.py` prints.

`hax.sh test` holds every patched crate to two checks: clippy is clean on the patched source, and the crate's tests pass on it (`cargo test -p <crate>`, or each line of its `patches/pre/tests`, such as the verifier's checks against real proofs). `hax.sh patched <command>` runs any command on the patched source, which is also how to inspect it.

When the source changes a little under a patch, `hax.sh refresh` rebases the patches onto it with git, keeping hunks `repair.py patches` would drop: it replays each patch as a commit on the last commit they all applied to, rebases those onto `HEAD` in a scratch worktree (`target/hax-refresh`), and writes them back. A conflict stops it; resolve it there, `git add`, then `hax.sh refresh --continue` (`--skip` drops a patch the source no longer needs, `--abort` drops the refresh).

## Adding a crate

Add `crates/<crate>/hax.toml`:

```toml
[scenario.<crate-name>]
backend = "lean"
opaque = []
exclude = []
```

Then `formal/extraction/repair.py extract crates/<crate>`, which fills the two lists until the crate extracts. Extract the crates it depends on first, or with it: their extractions declare the items it uses. Then work the list down as above.

## What the extraction trusts

`report.sh` counts, per extraction, the definitions extracted, the Rust items left opaque, the bodies Aeneas could not translate (`sorry`), and the patches. CI prints it on every run. Between the Lean and the Rust that runs stand:

- **The toolchain.** Charon, Aeneas, and the hax Lean library's models of `core` and `alloc` are trusted to translate faithfully.
- **The assumptions.** Opaque items are axioms with no body; the models in `CoreModelsExt` are as good as their definitions, and its `opaque`s are assumptions too.
- **The patches.** The Lean describes the patched Rust; the tests are the evidence that it computes what the committed Rust does.
- **The portable paths.** The SIMD and other hardware-specific code the crates run on x86-64 and aarch64 is not extracted.

## Proofs

`proofs/lean_sphincs` proves that leanSPHINCS's extracted `verify` is the statement's `Sphincs.verifyWithKeccak` (`formal/Statement/LeanSphincs.lean`), with no hypothesis: down to Keccak-f[1600], which it also checks against FIPS 202's through [hash-specs](https://github.com/Verified-zkEVM/hash-specs). Its README says what the theorem rests on and what proving it found. `hax.sh check` builds it, scans it for escapes (`sorry`, `native_decide`, `bv_decide`, `axiom`, set options) and compares the theorem's axioms with the committed list.

## Versions

The root `hax.toml` pins Charon, Aeneas, the Lean toolchain and the hax Lean library, and `hax.sh` pins `cargo-hax`. They move together: an Aeneas build fixes the Lean library its output needs, and that library fixes the Lean toolchain and Mathlib. The toolchain here is therefore the one Aeneas targets, v4.35.0, one behind the rest of `formal/`: Aeneas's Lean library does not compile on v4.36.0 (`AeneasMeta/BvEnumToBitVec.lean`), at the pinned build or at its latest. Move it when an Aeneas build does.
