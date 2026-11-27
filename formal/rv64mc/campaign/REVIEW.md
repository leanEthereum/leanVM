# Implement, defend, review, fix

Every batch of work goes through the same loop before it is merged. It caught a real defect in most waves (a postcondition too weak for a caller five times, a precondition false at a call site four times, wrong claims in the notes), so do not skip it. The process needs no tooling: three roles, each a separate agent (or, without agents, a separate pass that rereads only what the role is given).

`skill/implement-review-lifecycle/` is the Claude Code skill and Workflow script that ran it automatically (`references/prompts.md` has the exact prompts, `references/review.md` the full checklist); this file is the same process in short.

## 1. Implement, and write the defence

The worker does the work (`PROVING.md`), commits per function, and writes `DEFENCE.md` in a directory outside the repository (a run directory; copy it to `campaign/defences/<run>.md` when the batch merges). Per decision:

- **What**: the change, with file and declaration.
- **Why**: the reason, and the alternative rejected.
- **Claims**: refutable statements, e.g. "no existing statement changed (`git diff <base> --stat` touches only new files, `README.md` and `notes/total-status.md`)", "`PreT` holds at all three call sites: at 191 step 74 `self = sp + 8`, a `Flushes::default()`; …", "`PostT`'s `foot` conjunct is what `tables` (175) needs at its `memcpy` loop".
- **Evidence**: the exact command and its result (`lake build …` -> `Build completed successfully (N jobs)`; the axioms output; a `sites2.py` excerpt).
- **Not done**: what was left, per function, with the obstacle.

The defence's header gives the base commit, the head commit and the commits in between. Its two most useful sections for the reviewer: which caller uses which conjunct of each new `Post`, and which call-site fact discharges each conjunct of each new `Pre`.

## 2. Review

A reviewer that did not write the code gets the task (the brief), the diff (`git diff <base>..<head>`) and the defence, and nothing else. It edits nothing and does not change the worktree's state (no `git stash`, `checkout`, `reset`; use `git show <rev>:<file>`). It:

1. Lists every claim in the defence.
2. Reads the diff hunk by hunk: is each hunk covered by a decision, and correct?
3. Checks each claim against the diff and reruns the cheap evidence (the build of the new modules, the greps, `sites2.py`). A claim it cannot check is unverified, not true.
4. For this campaign in particular:
   - **Vacuity**: every new `Pre` holds at every call site in the binary (`sites2.py`, the callers' templates). A `Pre` false at a site makes the contract useless there.
   - **Use**: every new `Post` and `Out` gives what each caller needs, inside its loops too; class-A contracts keep the partial postcondition.
   - **Trust**: no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`; axioms pinned on every `Table` theorem; `Table` theorems' hypotheses only environment facts, each in the legend; any raised `maxHeartbeats` justified.
   - **Loops**: each `Total.loop`'s measure really decreases.
   - **Ledger**: obligations struck only when the proof discharges them; obligations' callers match the call graph (`cg.json`): one wave recorded a caller that does not exist.
   - **Drift**: a claim the code does not bear out, a change the defence does not mention, evidence that does not reproduce, work beyond or short of the task without saying so.
5. Writes findings, each with an id (`R<round>-<n>`), a severity (`important`: wrong, unsound, weaker than claimed, unusable, or drift about soundness or statements; `nit`: the rest), a location, the issue, the evidence (a quoted hunk, a command and its output) and a suggested fix. Without evidence a finding is a nit at most. The review is **clean** when no `important` finding remains.

## 3. Fix, and re-review

The worker answers every finding: **fixed** (the commit and the build result), **rebutted** (why it is wrong, with evidence: a reviewer can be wrong too), or **deferred** (why, and what it would take). It appends "Amendments, round N" to the defence, never rewriting earlier claims. A new reviewer then checks each disposition against the new diff and reviews the new diff for new defects and drift. Stop when clean, or after three rounds: then list the open findings in the merge commit's message and in `notes/total-status.md` where they affect a contract.

A clean round that still has nits ends with one close-out pass: fix the cheap nits and correct the defence so that it describes the code as merged.

## Optional: golf

After the implementation and before the review, a separate pass may simplify the proofs (shared helpers, shorter scripts) without changing any statement, recording each change and why it preserves behaviour in the defence. It paid off modestly (6e: 328 lines removed); skip it when time is short.
