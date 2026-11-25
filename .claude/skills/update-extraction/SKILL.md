---
name: update-extraction
description: Bring the hax Rust-to-Lean extraction back to green after the Rust source changed, add a crate to it, or win opaque items back. Use when the Extraction workflow fails, when `formal/extraction/hax.sh check` fails, or when asked to update, repair, extend or improve the Lean extraction of a crate.
---

# Update the Lean extraction

Crates with a `hax.toml` are translated to Lean by hax (Charon, then Aeneas). Nothing generated is committed, so "updating the extraction" means changing the small set of committed inputs until `hax.sh check` passes again. You do not need to know the toolchain: the scripts do the mechanical part and this file says what to do where they stop. `formal/extraction/README.md` is the reference.

**What you may edit:** `crates/**/hax.toml`, `crates/**/proofs/*/patches/`, and `formal/extraction/` (scripts, `CoreModelsExt/`, docs).

**What you never edit:** the Rust under `crates/**/src` (a patch rewrites it for the length of an extraction only), and generated Lean (anything under a `lean/` directory, and `formal/extraction/lakefile.toml`, `lake-manifest.json`, `Extraction/`).

**Done means:** `formal/extraction/hax.sh check` and `formal/extraction/hax.sh test` both pass, and `git status` shows changes only in the editable set above.

## 0. Set up, once per machine

```bash
formal/extraction/hax.sh setup      # cargo-hax, charon, aeneas, charon's Rust nightly
```

Lean comes from elan. The first `check` downloads Mathlib's build cache.

Run one extraction at a time per checkout: `hax.sh` patches the Rust source while it runs and reverts it after. If a run is killed, `git status` shows the patched files; `git checkout -- crates` restores them.

## 1. See what is broken

```bash
formal/extraction/hax.sh check
```

If it passes, there is nothing to do. Otherwise the failure is one of these, and step 2 handles the first four:

| what you see | meaning |
| --- | --- |
| `error: <patch> no longer applies to the Rust source` | the code under a patch changed |
| Aeneas errors, or a `sorry` in `Extraction/` | new Rust that Aeneas cannot translate |
| Lean errors in a `lean/` package | translated code uses something Lean has no model for |
| `failed to resolve item path` | a scenario names an item that was renamed or deleted |
| a crate directory is gone or new | a crate moved (step 3) |

## 2. Repair

```bash
formal/extraction/repair.py patches     # keeps patch hunks whose context is still there, drops the rest
formal/extraction/repair.py extract     # every scenario, in dependency order; or name crate directories
```

`repair.py extract` loops extraction and Lean build per crate until both pass. It moves whatever no longer translates onto the scenario's `opaque` list (signature only, an axiom) or `exclude` list (left out), under a "Not yet triaged" heading with the error, and removes entries for items that are gone. It prints every change. Keep that output for the pull request description.

If it stops with "no progress", it prints what is left. The cases:

- **Aeneas crashes on the whole crate and names no item.** Bisect: add a module to `opaque` (`"crate::module"`), rerun, and narrow to the item once the crash is gone.
- **An item fails even when opaque.** Its signature does not translate (`dyn Fn`, a function pointer, an `impl Iterator` result). Move it from `opaque` to `exclude`.
- **Aeneas reports an internal error at `iter/traits/iterator.rs`.** The crate reaches the `Iterator` trait's untranslatable methods. The tool adds the excludes itself; if a crate's own impl of `Sum` or `Product` triggers it, exclude that impl.
- **A crate uses an item its dependency keeps opaque inside an opaque module.** Name the item in the dependency's `include` list.

## 3. A crate that moved

`repair.py` does not follow these.

- **Renamed or moved:** `git mv` its `hax.toml` and `proofs/<scenario>/patches` with it, rename the scenario to match, and delete the old generated `proofs/<scenario>/lean`.
- **Split:** one scenario per new crate, the old lists divided between them.
- **Deleted:** delete its `hax.toml` and `proofs/`.
- **New, and wanted:** see "Adding a crate" in the README. Do not add `experimental_*` crates.

Then step 2.

## 4. Win items back

Step 2 only shrinks the extraction. Go through the "Not yet triaged" entries and try, cheapest first:

1. **A model in `formal/extraction/CoreModelsExt`**, when the error is `unknown constant` or `unknown identifier` for a `core.*`, `alloc.*` or `std.*` name. Write a definition where the Rust is short and an `opaque` otherwise, following the neighbouring models. One model clears every crate that uses the item.
2. **A rule in `mechanical.py`**, when the same rewrite is needed in several places.
3. **A patch in `patches/pre/`**, for an item worth a body: a verifier check, a signature scheme's `verify`, core arithmetic. The usual rewrites are an iterator chain into an indexed loop, an early `return` or `?` inside a loop into a flag checked after it, and a function-pointer field into a method. To write one: edit the Rust, save `git diff > crates/<crate>/proofs/<scenario>/patches/pre/NN-what-it-does.patch`, then `git checkout` the source. The patch must not change what the code computes.
4. **Leave it**, moving the entry under a comment that says what stops it.

After each attempt, take the entry off the list and run `formal/extraction/repair.py extract crates/<crate>`: if the fix did not hold, the entry comes back. Fewer patches is better than more coverage: each patch is upkeep when the code under it changes.

## 5. Verify

```bash
formal/extraction/hax.sh test       # clippy and tests on the patched source
formal/extraction/hax.sh check      # extract, build in Lean, no `sorry`, print the report
```

`hax.sh test` is not optional after touching patches: a hunk can still apply and be wrong for the new code. The Lean build has one known warning, `dupNamespace` in `CoreModelsExt/Collections.lean`. Fix any other; never silence one with `set_option` or an `allow`.

## 6. Hand over

- If `LIMITATIONS.md` names something that changed (a module now opaque, a crate added), update it. No counts or dates in it: `report.sh` prints the counts.
- If the tool needed help with a case it could have handled, teach `repair.py` the case.
- In the pull request, say what went opaque, what was won back, and paste `repair.py`'s output. The title is a conventional commit, such as `chore(formal): update the Lean extraction`.
