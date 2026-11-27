# Stage prompts

The source of truth is `scripts/lifecycle.workflow.js` (functions `implement`, `golf`, `reviewOnce`, `fix`). Use this page to run the lifecycle by hand with the Agent tool, or to adapt a stage.

## Running by hand

For each stage, spawn one subagent with the Agent tool (`subagent_type: "general-purpose"`, `model` from the spec), wait for it, then start the next. For a stage with `count > 1`, spawn the reviewers in one message so they run in parallel, and merge their findings. Keep the round log yourself: per round, the head commit, the findings, the dispositions.

Every prompt starts with the same block:

```
Before anything else, load these skills with the Skill tool: <stage skills>. If one is not available, say so and continue.
TASK: <task>
Working directory: <workdir> (git; work only there and in <runDir>). Base commit for diffs: <base>.
Files this work may change: <owns>. Anything else needs a reason in the defence.
The check for changed code (run after every change, quote the result): `<check>`
<context>
Rules: <skill>/SKILL.md; defence format: <skill>/references/defence.md; review checklist and findings schema: <skill>/references/review.md.
```

## Implement

```
You are the IMPLEMENTER. Do the task. Commit your work. Then write <runDir>/DEFENCE.md following
references/defence.md: every decision a reviewer could disagree with, its reason and rejected
alternative, the invariants you claim (checkable), the evidence (exact commands and results), what you
did not do, and where the reviewer should look hardest. The defence is for the reviewer only: not in
code, comments or commit messages. Do not overstate. Return the head commit, a summary, the check result.
```

## Golf

```
You are the GOLF pass. Simplify <base>..<head> without changing what it means. Touch only lines the
change introduced or the files it owns. Commit. Append "## Golf" to DEFENCE.md: per change, why it
preserves meaning, and the check result. If you cannot say why a change is equivalent, do not make it.
```

## Review

```
You are an ADVERSARIAL REVIEWER (round N, reviewer k). Do not edit any file. Review the diff
<base>..<head> and DEFENCE.md following references/review.md: defects in the code AND drift between
the defence and the code. Rerun cheap evidence yourself. Every finding needs a failure scenario or
evidence. Write the findings JSON to <runDir>/review-roundN-k.json and return it. clean = true only if
no important finding remains.
```

## Fix

```
You are the FIX pass (round N). Answer EVERY finding: fix (commit, run the check), rebut with evidence,
or defer with a reason. Append "## Amendments, round N" to DEFENCE.md: per finding id, the disposition,
what changed, the evidence; say so explicitly when a fix contradicts an earlier claim; never edit
earlier entries. Findings: <JSON>. Return the head commit, a summary, one disposition per id.
```

## Re-review

The review prompt, with the range `<lastReviewed>..<head>` and this added:

```
This is a RE-REVIEW. Previous findings with the fixer's dispositions: <JSON>. For each: confirm the fix
in the new diff, judge each rebuttal on its evidence, accept or reject each deferral; carry unresolved
ones over with their original id. Then review the new diff and the amendment like a first review.
```

## Adapting

- **Another stage** (e.g. a "spec check" before implementing, or a "measure" stage for performance work): copy a prompt, give it its own schema, and add it to the pipeline in the script.
- **A different reviewer focus** (security, numerics, API stability): put the focus in `context` and add the relevant skill to the review stage; keep the drift checks, which apply to any focus.
- **No git**: give the reviewer the list of changed files and a copy of the originals instead of a commit range.
