---
name: sync-fork
description: Sync this fork's main with leanEthereum/leanVM main, then re-extract the Rust to Lean and repair the proofs about the extraction. Use when asked to sync, update or catch up the fork with upstream, or to bring the extraction and its proofs back to green after upstream moved.
---

# Sync the fork with upstream, re-extract, and repair the proofs

This fork is upstream's Rust, plus the hax extraction of it to Lean, plus proofs about that extraction. The Rust is never edited here. What the fork owns:

- each extracted crate's `hax.toml` and `proofs/<scenario>/patches/`,
- `formal/extraction/` (scripts, `CoreModelsExt/`, docs),
- `formal/extraction/proofs/<package>/`, the proofs about the extracted code,
- `.github/workflows/extraction.yml` and `.claude/skills/`.

**Done means:** the fork's `main` is **zero commits behind** `leanEthereum/leanVM:main`; `formal/extraction/hax.sh check` passes (every scenario extracts with no `sorry`, the workspace builds, every proof package builds and its axioms are the pinned ones); the patched crates' tests pass; and no theorem statement got weaker.

The remotes are `origin` for upstream (leanEthereum/leanVM) and `fork` for dhsorens/leanVM. Check with `git remote -v` before pushing. Work on `main` in the main checkout, not on a side branch or in a worktree, and push to the fork's `main`. Nothing here opens or updates a pull request on purpose; note that an open upstream pull request whose head is the fork's `main` moves with every push, and say so in the report.

`formal/extraction/README.md` is the reference for the tools, and the `update-extraction` skill has the detail of repairing an extraction. This file is the order to do things in, and the part about proofs.

## 0. Before touching anything

```bash
git status --short                     # must be clean apart from untracked files of the user's
git fetch origin && git fetch fork
git rev-list --left-right --count main...fork/main      # 0 0: local main is the fork's
git log --oneline main..origin/main                     # what is coming in
git diff --stat main...origin/main -- crates            # which crates it touches
formal/extraction/hax.sh check                          # the baseline: must pass before the merge
```

If the baseline does not pass, fix that first and commit it on its own: otherwise you cannot tell what the merge broke. Note the warnings the proof packages print (the baseline is none from their own files).

Export `CARGO_TARGET_DIR` to the checkout's `target` if you use more than one checkout. Run one `hax.sh` command at a time: it patches the Rust source while it runs and reverts it after. If a run is killed, `git status` shows patched files under `crates/**/src`; `git checkout -- crates/**/src` restores them. Never commit those.

## 1. Merge

```bash
git merge origin/main
```

Merge, do not rebase: the fork's history stays a fast-forward of what is pushed, so the push needs no force. Conflicts can only be in files both sides touch (`AGENTS.md`, a workflow, `formal/` tooling); take upstream's and re-apply the fork's addition.

A crate that upstream renamed, moved, split, deleted or added: follow "A crate that moved" in the `update-extraction` skill before going on.

## 2. Rebase the patches

```bash
formal/extraction/hax.sh patched true      # do the patches still apply?
formal/extraction/hax.sh refresh           # if not: rebase them onto the new source
```

`refresh` replays each patch as a commit on the last source it applied to and rebases those onto `HEAD`, in a scratch tree at `target/hax-refresh`. Where it stops on a conflict:

- Keep **upstream's new code with the patch's rewrite on it**. Read both sides; do not pick one.
- Resolve **only the conflicted hunks**. `git checkout --ours <file>` on a whole file throws away the patch's other hunks in that file, which merged cleanly. Use it only when the code the patch rewrote is gone.
- When upstream moved the patched code into a new function, the rewrite follows it there.
- A changed signature (a new parameter type, say) has to be carried into everything the patch added: delegating impls, helper functions, test helpers.
- `git add` the files, then `hax.sh refresh --continue`. A patch whose rewrite is no longer needed: `--skip`.

`repair.py patches` is the blunt alternative (it drops every hunk whose context changed). Prefer `refresh`: a dropped hunk is a function that goes opaque, and a proof that loses the body it was about.

## 3. Re-extract and repair

```bash
formal/extraction/hax.sh check
```

What fails now is new Rust that Aeneas or Lean cannot take. `formal/extraction/repair.py extract <crate dir>...` moves it onto the scenario's `opaque` or `exclude` list and says what it moved; keep its output for the report. Two cautions:

- **Do not let it make opaque anything a proof needs a body for.** Before running it on a crate that a proof package covers, list the extracted functions the proofs unfold (`grep -rhoE '\b(keccak256|lean_sphincs)\.[A-Za-z0-9_.]+' formal/extraction/proofs/*/` is a start). If one of them stops translating, that is a patch to write or extend (step 4 of `update-extraction`), not an opaque entry.
- An entry for an item the proofs do not reach may stay opaque with its reason. Then try to win it back as `update-extraction` describes, cheapest fix first.

## 4. Repair the proofs

`hax.sh check` builds every package under `formal/extraction/proofs/` and stops at the first error. For a faster loop, in the package:

```bash
cd formal/extraction/proofs/<package>
lake build 2>&1 | grep -E 'error|warning: \./|✖'
lake env lean <Package>Proofs/<File>.lean      # one file
```

What upstream changes do to a proof, and what to do:

| what changed | what you see | what to do |
| --- | --- | --- |
| a function was renamed or moved | unknown constant | rename in the proofs |
| a function's body changed shape (a loop split, a helper introduced) | a `simp`/`step` proof no longer closes, or closes a different goal | prove a lemma for the new helper, and rebuild the caller's proof on it |
| a type changed (a field added, an array length) | type mismatch in `Defs.lean`'s representation maps | fix the map, then every lemma that mentions it |
| the scheme itself changed (a tweak, a parameter, a new check) | the lemma is now false | the statement in `formal/Statement/` must have changed with it upstream; re-prove against the new statement. If upstream changed the Rust and not the statement, **stop and report it**: that is a finding, not something to prove around |
| a proved function went opaque | the proof needs a body that is gone | go back to step 3 and get the body back |

Rules that do not bend:

- **The top-level theorems keep their statements and stay hypothesis-free.** Do not add a hypothesis, weaken a conclusion, or restrict the inputs to make a proof go through. If a statement has to change, say so in the report, with the reason.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by` or `set_option` in a proof package: `hax.sh check` rejects them. For bitvector goals use the kernel-checked `bv_bits` macro in `Common.lean`.
- The axioms of each theorem named in a package's `Axioms.lean` must stay those in its `axioms` file (`propext`, `Classical.choice`, `Quot.sound`). Regenerate that file only when a theorem was added or renamed, never to accept a new axiom.
- Never edit generated Lean (anything under a crate's `proofs/<scenario>/lean/`).
- No new warnings from the package's own files. Fix them with the fix the linter prints; never silence one.

Lean pitfalls that have cost time here:

- `simp only [Aeneas.Std.bind_ok]` can fail silently next to `usize` literals; `erw` does it.
- `simp` rewrites `l[i]!` to `l[i]?.getD default`; state hypotheses in that form.
- A hypothesis whose type is a `match` on the statement's verifier makes `omega`, `congr 1` and linters evaluate Keccak. `generalize` the scrutinee and clear the hypothesis first, and use `congrArg` instead of `congr`.
- Loops: `rw [loop.eq_def]`, then `simp only [hbody, Aeneas.Std.bind_ok]`; for a loop with an invariant, `loop_induct` in `Digest.lean`.

## 5. Verify

All of these, on the merged tree, before pushing:

```bash
formal/extraction/hax.sh check       # extract, build, no `sorry`, proofs build, axioms pinned
formal/extraction/hax.sh test        # clippy and the tests, on the patched source
```

`hax.sh test` is not optional after `refresh`: a hunk can apply and still be wrong for the new code. If its clippy step fails, check whether the same lints fail on the unpatched committed source with the same toolchain (`cargo clippy -p <crate> -- -D warnings`). If they do, the failure is upstream's, not the patches': run the tests themselves, each line of every `patches/pre/tests` file as `hax.sh patched cargo test --release <line>`, and report the clippy failure rather than fixing upstream's Rust.

Compare `formal/extraction/report.sh` with the baseline: definitions with bodies should not have gone down, and opaque items not up, without a line in the report saying why.

## 6. Record and push

- Update `formal/extraction/LIMITATIONS.md` and a proof package's `README.md` where they name something that changed. No counts or dates in them.
- If a tool needed help with a case it could have handled, teach the tool, or add the case to this file.
- Commit in steps a reader can follow: the merge, the patches, the scenarios, the proofs, the docs. Conventional-commit titles. No attribution trailers.
- Push and confirm:

```bash
git push fork main
git fetch fork && git rev-list --left-right --count origin/main...fork/main    # first number must be 0
```

Report in a few lines: the commits merged; which patches needed a hand and why; what went opaque and what was won back; which proofs changed and whether any statement did; the `report.sh` table; and anything left for a decision.
