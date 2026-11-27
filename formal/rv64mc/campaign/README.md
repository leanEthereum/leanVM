# The `MainSpecT` campaign: handoff kit

Working material for proving `main`'s total contract `MainSpecT` (`Rv64mc/Final/MainSpecT.lean`) bottom-up, moved here from a local scratch directory so the campaign can continue on another machine. It is not part of the proof: remove this directory before #878 leaves draft.

## State

- `notes/total-status.md` is the ledger: per function, its total module, `Table` theorem and open hypotheses; the summary at its top; the "Obligations" and "Owed by contracts already total" sections.
- At this commit: 183 of the 229 functions `main` reaches are total with a `Table` instance (10858 of 20878 instructions, 52.0%); every `Table` theorem's open hypotheses are environment facts about the image (the legend at the top of `total-status.md`).
- Waves 6f and 6g were merged while running: their implementer commits (6f up to fedf08d0b8, 6g up to 27a6d22d46) are in, but not their golf and review. Their branches are `formal/rv64mc-total-w6f` and `formal/rv64mc-total-w6g`; their defences so far are `defences/runW6f.md` and `defences/runW6g.md`. A later push of either branch merges on top.
- Left (46 functions, 10020 instructions), by height: `main` (17), `verify_execution`, `walk`, `build_layout`, `verify_bus_balance`, `tables`, `verify_keccak`, `verify_gkr_grand_products`, the `flushes_*` builders (187 to 191), `verify_stacked_opening` and its closures, `table_sumcheck`, `verify_layer`, `open`, `verify_whir`'s closure 74, `sumcheck`, `eq_kernel`, the two `multilinear_eval`s, `Flushes::bytecode`, `memory_cols`, `layout_limb`, `sumcheck_round_poly`, `induced_weight`, `StackWeight::evaluate`, `on_stack`, the `Form::sum` family (203, 204, 207, 211), `group_by_word`, `block_members`, `Bytecode::new` (215), `is_valid_encoding` (216), the `GenericShunt` 171 and two `E::sum` closures (23, 32). `python3 campaign/scripts/frontier_now.py notes/total-status.md` (from `formal/rv64mc`) prints those whose callees are all total.
- After the 229: assemble `MainSpecT` from `main`'s `Table` instance, and discharge the environment facts (each a fact about the generated image's static data).

## Setup

1. `formal/rv64mc/README.md`: generate `Rv64mc/Gen/` (`scripts/regen.sh`, `scripts/type-layouts.sh`; gitignored) and build (`lake build Rv64mc`, with `LEAN_ABORT_ON_PANIC=1` as CI sets it). Lake 5 runs about 32 Lean jobs and has no `-j`: a full build needs well over 16 GB. On a small host, build in import order eight modules at a time (`python3 campaign/scripts/topo.py . > campaign/topo.txt`).
2. `python3 campaign/scripts/callgraph.py . campaign/cg.json` writes the call graph (index, instructions, height, loops, callees) that `frontier_now.py` reads. `waves.md` is a snapshot of it by height with each function's partial-proof class.
3. `skill/implement-review-lifecycle/` is the Claude Code skill the waves ran under: copy it to `~/.claude/skills/` (or pass `skillDir`).

## A wave

1. A brief in `briefs/` (the latest, `taskW6f.md` and `taskW6g.md`, are the template): the worktree and base, lessons, the ordered list of functions (from `frontier_now.py`), what belongs to the other running wave, and the campaign context (conventions, what each contract must give its callers, the constraints).
2. Run it through the lifecycle: the Workflow tool with `scriptPath` = `skill/implement-review-lifecycle/scripts/lifecycle.workflow.js` and args like `{"task": "Read and do the task in <brief>", "workdir": <worktree>, "base": <PR head>, "runDir": <scratch dir>, "profile": "lean-proof", "implementPasses": 3, "owns": ["formal/rv64mc/Rv64mc/Proof/", "formal/rv64mc/Rv64mc/Table/", "formal/rv64mc/Rv64mc/Spec/", "formal/rv64mc/notes/", "formal/rv64mc/README.md"], "check": "cd formal/rv64mc && lake build <the new modules>", "pipeline": ["implement", "golf", "review-loop"], "maxRounds": 3, "context": <reviewer focus>}`. Two waves ran at a time, in two worktrees (WHIR and transcript side; layout and bus side), each 4 to 12 functions in about 5 hours.
3. Merge into `formal/rv64mc-safety`: `git merge --no-ff --no-commit <wave head>`, then `python3 campaign/scripts/resolve.py` for the recurring `README.md` and `total-status.md` conflicts. It asserts when both sides edit the legend line or the README's `Proof/` bullet: merge those by hand (the legend splits on ``; (?=`)``; keep both sides' new items). Recount the summary with the `awk` commands in `total-status.md`, build the new modules (`git diff --name-only --relative --diff-filter=A HEAD...MERGE_HEAD -- Rv64mc`), commit, push.

## Lessons

- A contract's `Post` and `Out` must give what its callers' loops need; reviews caught this in five waves (4a, 5a, 6a, 6c, 6e). Check each new `Post` against the caller's use, and each new `Pre` at every image call site (`scripts/sites2.py <name>` lists them): a `Pre` false at a call site makes the contract vacuous there.
- One executor run costs more than linearly in its calls: cut a body with many calls into parts of about twelve calls, each keeping only a frame invariant (`KInvT`). Hide large facts from the executor's arithmetic as `True → P` and seal callee pre and post as `@[irreducible]` definitions (`StateDerivedT`).
- Saved registers: `Proof/Runtime/SavedT.lean`. Vectors: `Proof/Runtime/VecReprT.lean`. Slices that may be empty or in the caller's frame: `Proof/Multilinear/OwnSliceT.lean`.
- `MainSpecT` asks only safety and termination, so a function with no partial proof needs only a safety contract; `Stop` is `AbortStop` (`a0 = 2`) for every function that may abort.
- `defences/` holds every wave's defence (decisions, evidence, what was left and why); `backlog.md` the open items outside the wave lists.
