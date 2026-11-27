---
name: formal-pr
description: Make a leanVM branch that touches formal/ ready for review: run the report tool and the right gates, check the axioms of every theorem the description names, sweep stale references, write the description and title, and review your own diff. Use when finishing formal/ work, before opening or marking ready a pull request, or when asked to write or check a formal/ PR description.
---

# Make a formal/ branch ready for review

A green build does not find a wrong statement or a false claim in the description. This is the pass that does, before a reviewer spends time on it. The rules are `CONTRIBUTING.md` ("Pull requests") and `formal/CONTRIBUTING.md`.

**Done means:** the gates for what changed pass and their results are in the description; every theorem the description names has the axioms it claims; no stale reference remains; the description has the repository's shape and claims only what a check shows; the title is a conventional commit; `formal-review` on your own diff leaves no important finding; no scratch file is in the branch.

## 1. Scope

`git diff --stat $(git merge-base origin/main HEAD)`. Every file belongs to the change. Plans, notes, logs, probes and scratch files come out (`git status` shows untracked ones; do not add them). A refactor or fix found on the way is its own pull request.

## 2. The report

From the repository root: `python3 -I formal/tools/pr-report.py`. Read each section. Remove leftovers it lists (debug commands, commented-out code, history words), justify or remove each new budget, and if it says the statement changed, make sure that was intended and agreed (`formal-statements`, section 5).

## 3. The gates for what changed

Commands are in `formal/AGENTS.md` ("Commands"). Build the changed modules first, then the gate:

- a few modules: `lake build <Module>` (or `python3 -I ../lake-build.py . <Module>` for heavy ones) in their project;
- a guest change: `scripts/regen-guest.sh --check` and `python3 -I scripts/check-fresh` from `formal/lean_vm`;
- before review: `./check-all.sh lean vectors` from `formal/`, or the projects you touched (`./check-all.sh lean_vm`, ...) and say which.

Run each as `cmd > log 2>&1; echo "exit $?"`: a pipe into `tail` hides a failure. Never quote `--dev` results as a check.

## 4. Axioms of what you claim

For each theorem the title or description names, run `#print axioms Name` in a temporary file outside the projects (or rely on the root file that pins it, and say so). A file without `sorry` can still depend on an admission in an import. Quote the result.

## 5. Stale references

For every declaration, file, module or path you deleted or renamed, search for it in `formal/` (Lean, `statement.tex`, `AGENTS.md`, `README.md`, notes), the skills and the root docs:

```sh
git grep -n 'OldName' -- formal .claude AGENTS.md CONTRIBUTING.md README.md
python3 -I tools/docnames.py          # from formal/: names the docs cite that no Lean file has
```

Also search the diff for status words (skeleton, still open, not yet proven), planning codes and history text, and rewrite them to describe what is there now.

## 6. The description

The shape is `CONTRIBUTING.md`'s: two or three sentences, then The problem, The idea, Example, For reviewers, Checks. For a change to `formal/Statement/`, the statement before and after in a `text` block and the proved relation between them. Name the agents used and how. List each check as its command and result. Claim only what a check or source shows; leave out what the diff shows; no measurements in the code (they go here or in the commit message). Draft it in a file outside the repository.

## 7. The title

A conventional commit with scope `formal`, as `feat(formal): ...` or `fix(formal): ...`. `pr-title.yml` accepts the standard types (`feat`, `fix`, `refactor`, `perf`, `test`, `docs`, `ci`, `chore`, ...), so a proof-only change is `feat` or `refactor`, not `proof`. A breaking change takes `!`; a protocol break `feat(protocol):` (root `AGENTS.md`, "Versions").

## 8. Review your own diff

Run `formal-review` on the branch, as a fresh agent if you can, given only the diff and the description. Fix each important finding, or say in the description why it stands. Then request review.
