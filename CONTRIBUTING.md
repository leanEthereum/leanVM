# Contributing to leanVM

leanVM is a minimal VM and recursive SNARK, with Lean 4 proofs of its soundness and of the schemes it aggregates. Most of its code, Rust and Lean, is written with AI agents. These rules are for every contributor, human or agent. The repository's working rules (layout, commands, what must change together) are in [`AGENTS.md`](AGENTS.md); the Lean proofs have their own rules in [`formal/CONTRIBUTING.md`](formal/CONTRIBUTING.md).

## The bar

- Read the source before you write. Every definition, value and rule you add has a source you read: a section of `doc/leanvm`, a paper, a Rust item, an upstream specification.
- If two sources disagree, or one is ambiguous, stop and say so. Do not pick one silently.
- Never claim a check passed unless you ran it and saw it pass. Quote the command and its result.
- Never invent a citation, a section number, a test vector or a known answer. A value the code under test computed is not a known answer for it.
- Keep a change small and on topic. A refactor, a rename or a fix found on the way is its own pull request.

A question costs minutes; a plausible guess that gets merged costs far more.

## AI agents

- The person who opens a pull request is responsible for every line of it, however it was written. Agent-written code meets the same bar as any other.
- That person vouches that each definition, statement and proof step means what it claims, and can justify each design decision without the agent. "The agent wrote it" does not answer "why is this line here".
- The description says which agents were used, and for what.
- Before requesting review, read the headline statements the change touches and the whole description, and check them against the diff.
- Keep plans, handoff notes, session logs and scratch files out of the contribution. The code and its docs describe what is there now; how it got there goes in the commit message.
- An agent's draft does not authorize posting a comment, opening or merging a pull request, or approving one. A person decides each.
- Agents read [`AGENTS.md`](AGENTS.md) and, for Lean work, [`formal/AGENTS.md`](formal/AGENTS.md), and use the repository's skills in [`.claude/skills/`](.claude/skills/). Each is a Markdown file any agent can read:
  - `formal-statements`: writing or changing a definition or theorem statement, or transcribing Rust or `doc/leanvm` into Lean.
  - `formal-proofs`: writing, refactoring or golfing a proof so the next contributor can repair it.
  - `formal-repair`: bringing proofs back after a change to the Rust, the guest, a parameter or a dependency.
  - `formal-review`: reviewing a `formal/` pull request or branch, your own included.
  - `formal-pr`: making a `formal/` branch ready for review.

## Pull requests

- The title is a conventional commit (`feat:`, `fix:`, `docs:`, `ci:`, `perf:`, ...), which `.github/workflows/pr-title.yml` checks. A breaking change takes `!`, a protocol break `feat(protocol):`, as the root `AGENTS.md` ("Versions") says. Scope Lean work `formal`, as in `feat(formal): ...`.
- What must change together with what (both prover trees, the three verifiers, `formal/`, the bindings) is in the root `AGENTS.md`, "What must change together". A pull request that misses one fails CI or breaks a verifier.
- The description starts with two or three sentences saying what changes and why, then these sections, each only where it has something to say:
  - **The problem**: what is wrong or missing.
  - **The idea**: how the change solves it, each new name explained.
  - **Example**: one small case, with real values.
  - **For reviewers**: the decisions to question and the cases a reviewer could miss.
  - **Checks**: one line per check, the command and its result.
- A change to a theorem or definition of `formal/Statement/` shows the statement before and after in a `text` block, and says how the new one relates to the old (equivalent, stronger, weaker).
- Claim only what a check or a source shows. Leave out what the diff already shows.
- No measurement (a time, a size, a speedup) in code, comments or docs. It goes in the commit message or the description.

## Defects found upstream

A defect in an upstream specification or library (Mathlib, ArkLib, CompPoly, VCVio, EthLib, Clean, a paper) is reported to its owner, with the file and line or section on both sides, not silently worked around. Check that it is still there at the upstream's head and that no issue already reports it. Record any divergence leanVM keeps until it is fixed.

A security issue, in leanVM or upstream, is never reported in a public issue or pull request. Report it privately to the maintainers (GitHub's private vulnerability reporting, if the repository enables it).

## Formal verification

`formal/` holds the Lean 4 proofs. Its trusted statement, `formal/Statement/`, and the reviewer's document, `formal/statement.tex`, are what a reviewer reads; a change to either changes what is proved. Read [`formal/CONTRIBUTING.md`](formal/CONTRIBUTING.md) before contributing there.
