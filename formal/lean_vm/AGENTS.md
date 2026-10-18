# lean_vm

Read [`README.md`](README.md) first. The repository's root `AGENTS.md` applies here too.

- `LeanVM/Spec/` is the trusted statement: it imports nothing from `LeanVM` outside it, and every change to it changes what is proved. Keep it a faithful transcription of the leanVM sources it cites (`verifier.py:N`, `*.rs:N`, `doc/leanvm` sections), at the commit it names.
- No `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `unsafe`, and no local overrides of the lakefile's options. Every warning is an error (`warningAsError`), deprecations included. Speed comes from proved `@[csimp]` lemmas (`LeanVM/Spec/Fast/`).
- `lake build` builds every module under `LeanVM/` (the lakefile's globs), and `LeanVM.lean` pins the two theorems' axioms. `lake test` builds every module under `tests/LeanVMTests/`.
- Differential tests compare with the Rust verifier, `scripts/fuzz-verifier.py` on `tests/fixtures/verifier`, and with the Rust aggregation, `guest-diff` on the cases `guest_diff` writes (the README says how). A protocol change in the Rust verifier fails CI until `Spec/Verifier.lean` and the proofs follow; regenerate the fixtures and the node vectors as the README says.
- Use `lake build <Module>` to check one module, not `lake env lean`.
- Builds are heavy: run them on a large machine, after `lake exe cache get`.
