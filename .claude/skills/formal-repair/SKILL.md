---
name: formal-repair
description: Bring leanVM's formal/ proofs back to green after a change to the Rust verifier, the guest (guests/lean_ethereum.py), the ISA, a signature scheme, a protocol parameter, the wire encoding, or a Lean dependency (Mathlib, ArkLib, CompPoly, VCVio, Clean, EthLib). Use when lean.yml's jobs fail after a Rust or guest change, when check-all.sh fails, when a regeneration breaks proofs, or when asked to repair, port or update the formalization. Covers triage by root cause, fixing at the owning layer, and making the repair durable.
---

# Repair the proofs after a change

A change to the Rust or the guest breaks proofs in clusters: one moved definition, one renumbered body, one new check, and dozens of failures downstream. Repair the cause, at the layer that owns it, not each failure where it shows. The recipes for each kind of change are `formal/AGENTS.md`, "Changing the spec": read the one for your change first; this skill does not repeat them.

**Never** edit a statement to make a proof pass (a statement change goes to the maintainers through `formal-statements`), hand-edit a generated file, or raise a budget to make a timeout go away.

**Done means:** `./check-all.sh lean vectors` passes from `formal/` (the real build, kernel included, the axioms and the Rust comparisons), `python3 -I scripts/check-fresh` passes from `formal/lean_vm` after a regeneration, `scripts/regen-guest.sh --check` reports nothing stale, no statement changed unless the maintainers agreed to it, and no budget was raised.

## 1. Classify the change

Which kind is it: a guest change, a verifier change, a protocol parameter, an ISA, scheme or wire change, or a dependency bump? `formal/AGENTS.md` gives each kind's path through the loop: Rust first, transcribe, regenerate, templates, adapt the proofs, gate. A change can be several kinds; follow each recipe.

For a dependency bump, change the pin (`rev`) in every project's `lakefile.toml` that requires it, update each `lake-manifest.json`, and fetch the caches (`lake exe cache get`) before building.

## 2. Regenerate

From `formal/lean_vm`: `scripts/regen-guest.sh --jobs N` writes everything derived from the guest. Its `changes` step prints each function whose body changed, was added or removed, with the hand-written modules that state or name it: the proofs to adapt. Keep that list.

## 3. List every failure in one run

```sh
python3 -I ../lake-build.py . LeanVM LeanVMTests --dev --keep-going > build.log 2>&1; echo "exit $?"
```

`--dev` skips the kernel on `LeanVM` for speed and `--keep-going` lists every failure; never use it for a claim (`formal/AGENTS.md`, "lean_vm"). Run other projects' builds the same way from their directories. Do not pipe a build into `tail`: the pipe hides its exit status.

## 4. Group failures by root cause

Sort the errors by the first declaration that broke, not by file. Typical causes:

- a definition changed shape, and every proof that unfolds it broke: fix or add its contract lemma (its normal form, its spec lemma) in the owning module, and the consumers follow;
- a guest function's body changed: its template or reference function and its meaning proof (`formal/AGENTS.md`, step 4 "Templates");
- a name or position moved: a proof cited a position instead of a stable name; switch it to `fn%`, `val%`, `pos%`, `guest_const%` or `lit%`, which survive the next move;
- a pinned value in the tests changed: re-derive it from the Rust or the specification, never from the Lean under test;
- an upstream lemma was renamed or its statement changed: fix the uses, and if many proofs relied on its old form, add a local lemma with the old form proved once.

One root cause, one fix. If the same edit is needed in many files, the missing piece is a lemma or a generator rule: add it, and the files need no edit or one mechanical one.

## 5. Fix at the owning layer

- A proof about a layer uses its contract; repair the contract, not the call sites.
- A generated file is fixed in its generator or the generator's input (a rule file, a contract), then regenerated.
- A timeout is profiled (`python3 -I tools/profile.py FILE` from `formal/`) and its cause fixed. `formal/AGENTS.md` lists the elaboration traps that cause most of them.
- A proof that no longer holds because the Rust changed what it does may mean the statement no longer holds. Stop and report it: that is a finding, not a repair.

Write each repaired proof to the `formal-proofs` rules, so the next change costs less.

## 6. Finish with the real gate

```sh
cd formal && ./check-all.sh lean vectors > gate.log 2>&1; echo "exit $?"
cd lean_vm && python3 -I scripts/check-fresh
```

Then run `python3 -I formal/tools/pr-report.py` from the repository root and read its report: it lists statement changes, added budgets and leftovers. Describe in the pull request what broke, the root causes and how each was fixed, with the gate's result.
