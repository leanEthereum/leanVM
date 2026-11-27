# Parallel work: tracks, worktrees, merging

## Roles

- **Coordinator** (one): owns the branch `formal/rv64mc-safety` (PR #878). Starts workers, merges their branches, keeps `notes/total-status.md`'s summary right, pushes. Does not prove.
- **Worker** (one per track): proves the track's functions in order in its own worktree and branch, one commit per function, and writes the defence (`REVIEW.md`). Never pushes, never merges.
- **Reviewer** (fresh per review round): reviews a worker's diff and defence (`REVIEW.md`). Never edits.

An agent without the ability to spawn others plays all three in turn, one track at a time; the rest of this file still applies.

## Tracks

`python3 campaign/scripts/plan.py notes/total-status.md` prints them live; this is the plan at the handoff (43 functions, 9757 instructions). A worker takes its track's functions top to bottom, skipping one whose callees are not yet total (it says so) and coming back after the next merge.

| track | functions, in order | first steps |
| --- | --- | --- |
| **T1 layout** (12, 2429 instr) | `Form::sum` 203, 207, 211; `layout_limb` 209; `Flushes::bytecode` 195; `flushes_set` 189, `flushes_jump` 191, `flushes_arith` 188, `flushes_deref` 190, `flushes_keccak` 187; `tables` 175; `build_layout` 45 | **First, fix the contract gap** in `defences/runW6g.md` D4: the `Flushes` builders' posts must say each result's footprint lies at or above `NEXT` at entry, else `tables` (which allocates its `Vec<Table>` buffer between builder calls and copies every `Flushes` into it) is unprovable. Second contracts with that post for `pair`, `state_derived`, `state_step`, `counted`, `memory`, `memory_if` (re-proving the last parts, `fin` and `total`, of `StateDerivedT` and `CountedT`), then `bytecode` (`wip/`) against them. Also review wave 6g's unreviewed modules (`FlushesMoveT`, `MemoryT`, `MemoryIfT`, `SumArr3T`, `MemoryColsT`). |
| **T2 transcript, WHIR, opening** (7, 1501) | `sumcheck_round_poly` 107 (`wip/`); `sumcheck` 85; `StackWeight::evaluate` 99; `verify_stacked_opening`'s closure 88; `GluedWeight::evaluate` 89; `verify_whir`'s closure 74 (928 instructions, 15 loops); `verify_stacked_opening` 66 | **107 then 85 first: seven functions in T3 and T4 wait on `sumcheck`.** Review wave 6f's unreviewed modules (`git diff 0152cc78ad..<handoff> -- …` restricted to 6f's: the `ESum*T` closures, `InputDigestT`, `ScalerNewT`, `NovelEvalT`, `RingSwitchT`, `LanesOfT`, `InducedWeightT`, `ESumCopiedSafeT`). |
| **T3 bus** (10, 2347) | `eq_kernel` 137; `Form::evaluate` 146; `E::sum` 23; `Bytecode::evaluate` 161; `GenericShunt` 171; `ColumnClaim::on_stack` 130; `Vec::extend_desugared` 64; `table_sumcheck` 54; `verify_gkr_grand_products` 152; `verify_bus_balance` 48 | **137 first: five functions wait on it** (161, 48 here; 138, 139, 60 in T4). 54, 152, 48 wait on T2's 85. |
| **T4 multilinear, Keccak** (7, 1679) | `multilinear_eval::<E>` 90, `::<K>` 59; `GenericShunt` 172; `E::sum` 32; `verify_layer` 138; `open` 139; `verify_keccak` 60 | 90 first (T2's 74 and T3's 152, through 172, wait on it). 138, 139, 60 wait on T3's 137 and T2's 85. |
| **T5 bytecode** (4, 750) | `is_valid_encoding_of_a_leanisa_program` 216 (class A: keep its partial postcondition); `group_by_word` 218 (needs a `Vec<(u64, Vec<u16>)>` representation, 32-byte elements each holding a `Vec<u16>` header, per `defences/runW6c.md`); `block_members` 217; `Bytecode::new` 215 | independent of the others |
| **T6 top** (3, 1051) | `walk` 42 (762 instructions, 16 loops, calls 64, 54, 48, 60, 45, 59, 66); `verify_execution` 214; `main` 7 | last, sequential; then `MainSpecT` and the environment facts (`README.md`, "Where it stands") |

Cross-track waits: T3 and T4 need T2's 85 early, T4 needs T3's 137, T6 needs all. Run T1 to T5 at once from the start; the waiting functions come later in their tracks, by which time the merges have brought their callees in.

## Starting a worker

```bash
cd <repo checkout>
git fetch origin && git worktree add ../leanVM-<track> -b formal/rv64mc-total-<track>-<n> origin/formal/rv64mc-safety
# build outputs: copy .lake from a built worktree at the same commit to skip a full build
rsync -a <built worktree>/formal/rv64mc/.lake/ ../leanVM-<track>/formal/rv64mc/.lake/
# Rv64mc/Gen/ is gitignored: copy it too, from the worktree it was generated in
rsync -a <built worktree>/formal/rv64mc/Rv64mc/Gen/ ../leanVM-<track>/formal/rv64mc/Rv64mc/Gen/
cd ../leanVM-<track>/formal/rv64mc && lake build Rv64mc.Table.FormT6g   # should rebuild nothing
```

Give the worker a brief: `briefs/taskW6g.md` is the template. It states the worktree, branch and base commit; the lessons; the ordered function list with what belongs to the other tracks ("not yours: do not create their modules"); the reading list; the contract conventions (what `Pre`, `Post`, `Stop` must be, call-site checks, `Table` instances); the constraints (`README.md`, "Rules"); and "commit after each function; when one stalls past about 45 minutes of effort, record it as not done with its obstacle and move on". Tell it to read `PROVING.md` and `REVIEW.md`.

A batch is about 4 to 12 functions (one worker session, a few hours); then review, merge, and start the next batch from the new head. Smaller batches merge sooner and unblock other tracks sooner.

## Resources

- **Every Lean command goes through `campaign/scripts/lean-slot.sh`** (`campaign/scripts/lean-slot.sh [--timeout SECS] lake build …` or `… lake env lean <file>`, from `formal/rv64mc`): it runs at most `LEAN_SLOTS` Lean commands on the host at once (default 2, each under `MemoryMax=$LEAN_SLOT_MEM`, default 14G, with `LEAN_ABORT_ON_PANIC=1`), so the number of workers is not bounded by memory. Workers spend about half their time reasoning, so four workers on two slots keep both slots busy. Raise `LEAN_SLOTS` on a bigger host; set the same `LEAN_SLOT_DIR` for every worker.
- Each Lean process checking one of these proof files uses a few GB; Lake's full build about 32 at once. Size the number of parallel workers to memory: with the earlier 62 GB host, two workers capped at 16 GB each was the limit and workers waited for memory.
- One `lake build` per worktree at a time. Builds in different worktrees do not share outputs: seed each new worktree's `.lake` by `rsync` from a built one at the same commit.
- Never `lake clean`, never delete `.lake` or `Rv64mc/Gen`, never run `scripts/regen.sh` mid-campaign.
- A background wait on a process: wait on its PID, not `until ! pgrep -f <pattern>` (the loop's own command line matches the pattern and never ends).

## Merging (coordinator)

From the worktree on `formal/rv64mc-safety`, with no uncommitted changes:

```bash
git fetch <worker worktree or remote> <branch>
git merge --no-ff --no-commit FETCH_HEAD
python3 campaign/scripts/resolve.py       # the recurring conflicts in README.md and notes/total-status.md
grep -c '^<<<<<<<' README.md notes/total-status.md
```

- Run from `formal/rv64mc`; `resolve.py` finds the files itself. It handles the status rows and README lines that both sides extend. It stops with an `AssertionError` when both sides edited the same long line: the legend line at the top of `total-status.md` (split it on ``; (?=`)``, keep both sides' new items and ours' removals) or README's single `Proof/` bullet (insert one side's new segment before `` `Proof/Merkle/HashPairT` ``, and both sides' new `Table` names in the `Table/` list). Then check no row went backwards: every row that is `yes` on either side is `yes` in the result, with the longer module list when both extended it.
- Recount and edit the summary table at the top of `total-status.md` (its `awk` commands are in the paragraph below it):

```bash
awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md                   # total
awk -F'|' '$7 ~ /yes/ && $10 ~ /none/ {n++; s+=$5} END {print n, s}' notes/total-status.md   # no open hypothesis
awk -F'|' '$2 ~ /^ [0-9]+ $/ && $7 ~ /no/ {n++; s+=$5} END {print n, s}' notes/total-status.md # not total
```

- Build what the merge added, then commit and push:

```bash
M=$(git diff --name-only --relative --diff-filter=A HEAD...MERGE_HEAD -- Rv64mc | sed 's|\.lean$||; s|/|.|g')
LEAN_ABORT_ON_PANIC=1 lake build $M
git add -A . && git commit -m "Merge <track> batch <n>: <functions>" -m "Co-Authored-By: …"
git push origin formal/rv64mc-safety
```

- When a merged module is imported by another track's work, or a merge changes a contract another track uses, tell that track's worker to merge the new head into its branch (`git merge origin/formal/rv64mc-safety`) before going on.
- Every few merges, and before the end, run the full `LEAN_ABORT_ON_PANIC=1 lake build Rv64mc`.
