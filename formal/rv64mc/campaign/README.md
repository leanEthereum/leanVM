# Start here: the `MainSpecT` campaign handoff

This folder lets an agent with no prior context continue the campaign. Read this file, then `PROVING.md` (how one function is proved total), `PARALLEL.md` (how the work is split across parallel workers and merged) and `REVIEW.md` (how each piece of work is checked before it is merged). Everything here is working material, not part of the proof: delete `formal/rv64mc/campaign/` before PR #878 leaves draft.

## The goal in one paragraph

`formal/rv64mc` compiles the leanVM verifier (`crates/verifier`, a `no_std` copy) to an RV64IM binary, lifts every function of the binary into Lean (`Rv64mc/Gen/`, generated, gitignored), and proves facts about the binary. PR #878 (branch `formal/rv64mc-safety`, draft, stacked on PR #822) adds **total correctness**: the end theorems `rv64_halts_of_main` (`Rv64mc/Final/EndT.lean`: on every input of fewer than `2^16` words the binary halts with exit code 0, 1 or 2, never trapping, faulting or looping) and `rv64_boolVerdict` (`Final/Headline.lean`) are proved **conditional on one hypothesis**, `main`'s total contract `MainSpecT` (`Rv64mc/Final/MainSpecT.lean`). The campaign proves `MainSpecT` bottom-up: a total contract (`HoldsT`, `Rv64mc/Core/HoldsT.lean`) for each of the 229 functions `main` reaches, each instantiated at the binary (a `Table` theorem) with its callees' instances, until `main`'s instance gives `MainSpecT`.

## Where it stands

- The ledger is `formal/rv64mc/notes/total-status.md`: a summary, the open hypotheses (the legend at the top), "Obligations on functions not yet total" (what a future caller's proof must discharge), "Owed by contracts already total" (functional facts left out of safety contracts), and one row per function (`| height | idx | function | instructions | class | total? | module | Table theorem | open hypotheses |`).
- At the handoff commit: **186 of 229 functions total, 11121 of 20878 instructions (53.3%)**; 43 functions (9757 instructions) left. Every `Table` theorem's open hypotheses are environment facts (words or tables in the binary's static data, `env`'s two facts about the allocator), listed in the legend.
- `python3 campaign/scripts/plan.py notes/total-status.md` (from `formal/rv64mc`, after the setup below) prints the 43 by track with what each waits on.
- **Not yet reviewed**: the last two waves (6f: WHIR and transcript side; 6g: layout side) were stopped mid-run and their implementer commits merged without their review rounds. Their modules build. Their defences (the implementer's account of decisions, evidence and what is left) are `defences/runW6f.md` and `defences/runW6g.md`. Reviewing them (`REVIEW.md`) is the first task of whoever owns those tracks: `git diff 0152cc78ad..<handoff commit> -- formal/rv64mc/Rv64mc` is the unreviewed code.
- **Unfinished files** are in `wip/` (outside the Lean library, so the build ignores them), each described in `wip/README.md`.
- After the 229 functions: state and prove `MainSpecT` from `main`'s `Table` instance (`Final/EndT.lean` and `Final/MainSpecT.lean` show what is needed), then discharge the environment facts in the legend (each a fact about the generated binary, by evaluation).

## Setup

1. Toolchain: elan with Lean `v4.36.0` (from `formal/rv64mc/lean-toolchain`); Python 3; Rust (for regenerating the lift). `formal/rv64mc/README.md` is the project's own documentation; read its "Trusted" and "Layout" sections.
2. Generate `Rv64mc/Gen/` once: `formal/rv64mc/README.md` says how (`scripts/regen.sh` builds the guest and lifts it, `scripts/regen.sh --check` verifies the binary against the committed `image.sha256`; `scripts/type-layouts.sh` writes the type layouts). `.lake/packages`: `lake update`, then `lake exe cache get` for Mathlib (same README). Never edit or delete `Rv64mc/Gen/` by hand afterwards, and never run `regen.sh` again during the campaign: every proof is against this exact lift.
3. Build: `cd formal/rv64mc && LEAN_ABORT_ON_PANIC=1 lake build Rv64mc` (CI sets `LEAN_ABORT_ON_PANIC=1` so that a Lean panic fails the build instead of continuing with a default term). Fetch Mathlib's cache first if Lake offers it. Lake 5 runs about 32 Lean processes at once and has no `-j`: give the build at least 32 GB, or build in import order a few modules at a time (`python3 campaign/scripts/topo.py . > campaign/topo.txt` writes the order).
4. `python3 campaign/scripts/callgraph.py . campaign/cg.json` writes the call graph from the lift (function index, instruction count, height above the leaves, loop back-edges, callees). `plan.py`, `frontier_now.py` read it. It is gitignored: never commit what a script writes.
5. Optional: the Lean language server through an MCP server (`lean-lsp-mcp`, `uvx lean-lsp-mcp`) makes each check incremental (see `PROVING.md`, "Iterating").

## The loop

1. Pick work from `plan.py`'s output, by track (`PARALLEL.md`). One worker per track, each in its own git worktree on its own branch from the current head of `formal/rv64mc-safety`.
2. The worker proves its functions in order (`PROVING.md`), one commit per function (its proof module, its `Table` instance, its row in `total-status.md`, any new obligation or open hypothesis), and writes a defence (`REVIEW.md`).
3. A reviewer that did not write the code reviews the diff and the defence (`REVIEW.md`); the worker fixes; repeat until no important finding is left (at most three rounds).
4. The coordinator merges the branch into `formal/rv64mc-safety` (`PARALLEL.md`, "Merging"), recounts the summary, builds the new modules, pushes, and starts the track's next batch from the new head.

## Rules that bind every change

- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide` or `implemented_by` in a committed `.lean` file under `Rv64mc/` (the library builds every file there: `lakefile.toml`'s `globs = ["Rv64mc.+"]`). Unfinished work goes in `campaign/wip/`.
- No existing statement changes: `Holds`, `HoldsT`, `TContract`, `Total`, `MainSpec*`, the end theorems, `EndStatement.lean`, existing specs and proofs. New proofs go in new modules; a second contract of a function sits beside the first (`…OwnT`, `…AlT`, `…SafeT`) with a proof relating them where one follows from the other.
- Every `Table` theorem has a `#guard_msgs in #print axioms` block pinning `[propext, Classical.choice, Quot.sound]` or fewer.
- No raised `maxHeartbeats` without a comment saying why and a measurement behind the value.
- Style (`formal/AGENTS.md`, the repository's `AGENTS.md`): a module docstring (what it proves, main definitions, main results); comments only where necessary; no measurements in comments; no em-dashes or en-dashes anywhere; Lean lines at most 120 columns (Markdown is never hard-wrapped); one symbol, one meaning.
- Commits: conventional messages (`feat(formal): …`, `docs(formal): …`), ending with a `Co-Authored-By:` trailer naming the model that wrote them. Merges into `formal/rv64mc-safety` are `--no-ff`. Do not push to `main`; do not rebase the PR branch (others have its commits).
- Keep the repository's public text neutral: no personal data, no unpublished security findings.

## Contents

| path | what |
| --- | --- |
| `README.md`, `PROVING.md`, `PARALLEL.md`, `REVIEW.md` | this guide |
| `scripts/lean-slot.sh` | runs a Lean command in one of a fixed number of host-wide slots under a memory cap (`PARALLEL.md`, "Resources") |
| `scripts/plan.py` | the remaining functions by track, with what each waits on |
| `scripts/callgraph.py` | writes `cg.json` from `Rv64mc/Gen/` |
| `scripts/frontier_now.py` | the functions whose callees are all total |
| `scripts/sites2.py <name>` | every call site of a function in the lifted templates, with the instructions before it (run from `formal/rv64mc`), to check a precondition at each |
| `scripts/sites.py` | an older, shorter variant of `sites2.py` |
| `scripts/topo.py` | the library's modules in import order |
| `scripts/resolve.py` | resolves the recurring merge conflicts in `README.md` and `notes/total-status.md` |
| `briefs/` | every wave's brief, the task text each worker got; `taskW6f.md` and `taskW6g.md` are the latest and the best templates (they name the old host's worktree paths and memory caps: substitute yours) |
| `defences/` | every wave's defence: decisions, evidence, what was left and why. The richest record of what was tried |
| `backlog.md` | open items outside the wave lists |
| `waves.md` | a snapshot of the call graph by height with each function's partial-proof class (A: proved partially at the binary, C: a spec only, D: nothing) |
| `skill/implement-review-lifecycle/` | the Claude Code skill and workflow script the waves ran under (optional: `REVIEW.md` describes the same process without it) |
| `wip/` | unfinished proof files and what each needs |
