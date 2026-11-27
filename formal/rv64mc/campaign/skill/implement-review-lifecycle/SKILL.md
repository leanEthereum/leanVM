---
name: implement-review-lifecycle
description: "Run code or proof work through a configurable implement, golf, adversarial review, fix and re-review lifecycle with separate subagents and a chosen model per stage. The implementer writes a defence (its decisions, reasons, evidence and claimed invariants, as text for the reviewer, never in the code), and every reviewer hunts both for defects in the diff and for drift between the defence and the code. Ships profiles for Lean proof work, Lean statement or specification changes (two independent Fable reviewers, lean-spec-authoring), Lean build-speed work and general code, wiring in the lean4 prove, golf, refactor and review skills, adversarial-review and lean-spec-authoring. Use it whenever the user wants work implemented and then adversarially reviewed, asks for an implement/review/golf/fix loop, wants reviews by another model or several reviewers, wants a change defended to a reviewer, or says review cycle, fix and re-review until clean, or adversarial review, even without naming this skill."
---

# Implement / review lifecycle

A change is implemented by one subagent and attacked by others, in rounds, until a review comes back clean or the round budget runs out. Two things make the attack sharper than a plain code review:

- **The defence.** Every stage that changes code also writes, outside the code, what it decided and why: the approach, the alternatives it rejected, the invariants it claims to keep, the evidence (commands it ran, numbers it measured), and what it did not do. The reviewer gets the defence and the diff.
- **Drift.** The reviewer checks the defence against the code as hard as it checks the code: a claim the diff does not bear out, a change the defence does not mention, evidence that does not reproduce, a scope that grew. Drift is where confident-sounding work hides its mistakes, and a written claim is much easier to refute than an unstated one.

Separate subagents (and, where it helps, separate models) keep the reviewer from inheriting the implementer's blind spots: it sees only the task, the diff and the defence, never the implementer's reasoning.

## Quick start

1. **Pick a profile** from `references/profiles.md` (Lean proof work, Lean statement change, Lean build speed, general code), or write a spec (below). Tell the user the profile and the models in one line before starting.
2. **Fix the inputs**: the task text, the working directory (a git worktree, so every stage commits and reviewers diff by commit), the base commit, the files the work may touch, the build or test command for the changed files only, and a run directory for the artefacts outside the repository (e.g. the session scratchpad).
3. **Run it**:
   - With the Workflow tool: invoking this skill is the user's opt-in to running its workflow. Call `Workflow` with `scriptPath` set to this skill's `scripts/lifecycle.workflow.js` and `args` set to the spec (an object, not a JSON string). It runs every stage, loops review and fix, and returns the round log.
   - Without it: run the same stages yourself with the Agent tool, one subagent per stage, using the prompts in `references/prompts.md`, waiting for each stage before the next. Pass `model` per stage.
4. **Report** (see "Reporting" below): what changed, the final verdict, open findings, and how the defence held up.

## The stages

| stage | gets | produces | why it is separate |
|---|---|---|---|
| implement | task, constraints, spec skills | commits; `DEFENCE.md` round 0 | does the work and commits to its reasons in writing |
| golf (optional) | the diff | commits; a golf section in `DEFENCE.md` saying why each change preserves behaviour | simplifies with fresh eyes; must not change meaning |
| review | task, diff `base..head`, `DEFENCE.md` | findings (`references/review.md` schema) | independent; does not edit; hunts defects and drift |
| fix | findings, diff, defence | commits; a disposition per finding (fixed / rebutted with evidence / deferred with reason); an amendment to `DEFENCE.md` | answers every finding in writing |
| re-review | previous findings, dispositions, the diff since the last review, the amended defence | findings | checks each fix and rebuttal, and the new diff for new defects and drift |

The default pipeline is `implement -> golf -> review-loop`, where `review-loop` is review, then fix and re-review until clean or `maxRounds`. `["implement", "review-loop", "golf", "review-loop"]` reviews before golfing and then reviews the golf. A pipeline without `golf` is fine for small fixes.

**Clean** means no finding of severity `important` remains (open, or fixed but not confirmed). A clean round that still has findings (nits, or drift of any severity) ends with a **close-out**: one fix pass that corrects the defence and fixes the cheap nits, followed by one re-review only if it changed code. Without it, a run can end "clean" with a defence that no longer describes the code, which defeats the point of having one.

## Defining a lifecycle

A spec is a small object (also the Workflow `args`). Everything has a default; the profiles fill in the rest.

```json
{
  "task": "Prove `foo_le_bar` in Foo/Bar.lean without changing its statement.",
  "workdir": "/path/to/worktree",
  "base": "HEAD",
  "runDir": "/path/to/scratchpad/lifecycle-foo",
  "profile": "lean-proof",
  "owns": ["Foo/Bar.lean"],
  "check": "lake env lean Foo/Bar.lean",
  "pipeline": ["implement", "golf", "review-loop"],
  "maxRounds": 3,
  "stages": {
    "implement": { "model": "opus", "skills": ["lean4:prove", "writing-lean-proofs"] },
    "golf":      { "model": "opus", "skills": ["lean4:golf", "lean4:refactor"] },
    "review":    { "model": "opus", "count": 1, "skills": ["adversarial-review", "lean4:review"] },
    "fix":       { "model": "opus" },
    "rereview":  { "model": "opus", "count": 1 }
  },
  "context": "Anything every stage should know: repository rules, what not to touch."
}
```

- `model`: `opus`, `sonnet`, `haiku` or `fable`; omit to inherit the session's. Use a different model (or several reviewers) for reviews when independence matters most: statement changes, security-relevant code, anything trusted.
- `count` (review, rereview): reviewers run in parallel and their findings are merged; the round is clean only if every reviewer is.
- `skills`: names the subagent loads first with the Skill tool (or reads, when given as a path to a SKILL.md). Missing skills are skipped with a note, not fatal.
- `owns`: the files the work may touch; a change outside them is a scope finding unless the defence justifies it.
- What the user asked to keep (a signature, a name, a file's interface) stays exactly as it is, even when the change makes part of it redundant (an unused hypothesis becomes `_h`, not deleted); propose the further change in the report instead.
- `check`: the cheapest decisive build or test of the changed files. Every code-changing stage runs it and quotes its result in the defence; reviewers may rerun it.
- `effort` per stage is optional (`low` to `max`); set it only when the user asked for one.

## The defence

Its format is in `references/defence.md`. In short, per decision: **what** (the change, with file and declaration), **why** (the reason and the alternative rejected), **claims** (invariants it keeps: statements unchanged, behaviour preserved, nothing newly trusted, performance), **evidence** (the exact command and its result, or the measurement), and **not done** (what it left out and why). It lives in the run directory, not in the code, comments or commit messages, because its job is to be checked, not to ship.

Write claims so that they can be refuted: "the statement of `foo_le_bar` is byte-identical (`git diff base -- Foo/Bar.lean` touches only the proof)" is checkable; "kept everything consistent" is not.

## What the reviewer does

`references/review.md` has the checklist and the findings schema. The reviewer:

- reviews the diff, hunk by hunk, and looks elsewhere only to check one specific claim (a user of a deleted name, the statement of a cited lemma);
- tests every claim in the defence against the diff and, where cheap, by rerunning the quoted evidence;
- reports **defects** (wrong, unsound, weaker than claimed, slower, untested, unclear), **drift** (`claim-not-in-code`, `code-not-in-defence`, `evidence-does-not-reproduce`, `scope-drift`), and **process gaps** (the check not run, measurements missing);
- gives each finding a concrete failure scenario or evidence; speculative ones are nits;
- does not edit files, and does not change the working tree's state either (no `git stash`, `checkout` or `reset` there): to see the base, use `git show <base>:<file>` or a scratch copy in the run directory.

For Lean work it applies `adversarial-review` (vacuity, tautological specs, weakened statements, fidelity of transcribed artefacts) and, for statement changes, `lean-spec-authoring` (every hypothesis justified, old and new statements related by a proved equivalence or implication, non-vacuity witnesses).

## Fix and re-review

The fixer answers every finding: **fixed** (with the commit and the check result), **rebutted** (why the finding is wrong, with evidence: a reviewer can be wrong too, and a rebuttal with evidence is as good as a fix), or **deferred** (why, and what it would take). To run the old code (to show a new test fails on it), it uses a scratch copy or `git show <base>:<file>`, not a checkout in the working tree, so an interrupted pass cannot leave the old code in place. It then appends an "Amendments, round N" section to `DEFENCE.md`; it never rewrites earlier claims silently, so the history of what was claimed stays reviewable.

The re-reviewer confirms each fix in the new diff, judges each rebuttal on its evidence, and reviews the new diff (including for drift against the amendment). Findings it confirms fixed are closed; the rest carry over.

## Scope and cost

- Keep reviews on the diff; a whole-repository audit per round is slow and finds old problems the task did not cause.
- Each stage builds or tests only what it changed (`check`); run the full gate once at the end, outside the loop, and send its failures through one more fix and re-review round.
- Rounds stop at `maxRounds` even if findings remain: report them rather than looping forever.
- Review the task's change, not the review apparatus. Scripts, probes and mutation tests the implementer wrote are evidence for its claims; a weakness in them matters only if it makes a claim unsupported (`evidence-does-not-reproduce`), and hardening them against hostile inputs is out of scope unless the task asks for it. Once the change itself is approved, stop.
- If the harness refuses a write (some refuse report files from subagents), put that content in the final message instead; do not route around the refusal through the shell.

## Reporting

End with: the commits; the final verdict (clean, or the open findings by severity); a table of rounds (findings raised, fixed, rebutted, deferred); the drift found and whether the final defence matches the code; the evidence for the key claims; and the paths of `DEFENCE.md` and the review files in the run directory. State what was not verified.

## References

- `references/profiles.md`: ready specs (models, skills, rounds, reviewers) for Lean proofs, Lean statement changes, Lean build speed and general code, with when to pick each.
- `references/defence.md`: the defence template, a good and a weak example, and how golf and fix stages extend it.
- `references/review.md`: the reviewer's checklist (defects and drift), severities, the findings schema, and how re-review closes findings.
- `references/prompts.md`: the prompt for each stage, for running the lifecycle with the Agent tool or adapting the workflow.
- `scripts/lifecycle.workflow.js`: the Workflow script that runs a spec.
