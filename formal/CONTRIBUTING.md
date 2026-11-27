# Contributing to formal/

The quality bar for the Lean proofs, for people and agents alike. These are rules; the procedures that apply them are the skills in [`../.claude/skills/`](../.claude/skills/) (table at the end). Commands, the build and the recipes for a change to the Rust are in [`AGENTS.md`](AGENTS.md); the rules for the whole repository are in [`../CONTRIBUTING.md`](../CONTRIBUTING.md).

## What formal/ is for

A reviewer reads [`statement.tex`](statement.tex) and the trusted statement, `Statement/`, whose end statements are the fields of `Theorems` in `Statement/Theorems.lean`. Everything else is checked by the kernel, so a reviewer need not read it, but the next contributor must be able to repair it.

The statement is the deliverable. A proof is an implementation detail, and a maintenance cost: it breaks when the Rust, the guest or a dependency changes, and someone has to bring it back. Write proofs for that person.

## The trusted statement

Every change to `Statement/` changes what is proved, and the maintainers decide it: ask before you make one. A pull request that changes a definition or theorem statement there ships:

1. a proved relation between the old and the new statement, kept in a proof project's tests (as `lean_vm/tests/LeanVMTests/Statement/` does): an equivalence, or the implication that shows the new one is stronger, or, if it is weaker, why it must be;
2. a witness that each new hypothesis is satisfiable, at the deployed parameters;
3. `statement.tex` changed in step;
4. the statement before and after in the description, in a `text` block.

Definitions:

- State meaning, not mechanism. A definition names a concept that exists without the code that uses it; the constraint-shaped or loop-shaped form is a lemma about it.
- Know which source is authoritative. **Transcribed** content (the verifier, the ISA, hash inputs and domain separators, encodings, the guest's bytecode) follows the Rust and the guest: if the Lean and the Rust disagree, the Lean is wrong, or the disagreement is a finding. **Specified** content (models, games, security properties, the end statements) follows `doc/leanvm` and the papers: if the Rust disagrees, that is a finding about the Rust.
- Cite a source by name (a Rust item, a guest function, a `doc/leanvm` section) and its commit, never by line number.
- Never add a definition only to make a proof go through. It trades a proof gap for permanent API.

Hypotheses:

- Every hypothesis is forced by the mathematics (say which instance breaks without it) or is a real interface obligation the caller owes. Anything else is a defect.
- When a proof is hard, the statement does not move. None of these is an answer to a hard proof: strengthen a hypothesis; weaken a conclusion (`↔` to `→`, `=` to `≤`); specialise a variable or a parameter; add a side condition to dodge an edge case; redefine the object; move a check of the verifier into an assumption; restrict the stack sizes, rates or message lengths the statement covers; assume a hash injective where collision resistance is what holds. Prove it, refute it, or leave it out and say so.

Vacuity and tautology both compile, and no gate catches them:

- No degenerate definition: an `else True` branch, an empty relation, a bound that is not below one at the deployed parameters.
- No structure field of type `True`, no theorem concluding `True`, no `∃ x, ..., True`, no `variable` hypothesis that assumes or trivially entails the conclusion, and no public declaration whose conclusion collapses to `True`. Judge by meaning, not by spelling.
- The substitution test: if the object were replaced by another of the same shape (another verifier, another hash, another bound), would the statement still hold by the same proof? Then it restates rather than specifies.

Headline theorems are read by people who do not read Lean every day. Each field of `Theorems`, and each end statement it names, has a docstring of one line or a few saying what it means in words, with its hypotheses in words. No proof narration.

## Proofs the next agent can repair

- Design top-down, prove bottom-up: state the steps as named lemmas or `have h : stmt`, then fill them. A proof over about 50 lines sketches its argument in comments or is split.
- A recurring argument (an induction, an extensionality step, a cast, a normalization) is one lemma, in the module that owns the definition it is about. Do not copy a proof for the next function or instance: prove it once and instantiate it, or generate it, or decide it by reflection.
- Use a layer through its contract: its spec lemmas and normal forms (as `LeanVM/Protocol/Verifier/Phases.lean` gives the verifier's phases), not by unfolding its definitions. A proof that unfolds breaks when the definition changes shape.
- Automation is terminal, or follows an explicit shaping step. A terminal `simp` stays unsqueezed unless it is slow; a non-terminal one is `simp only [...]`, or `have h : P := by simp`, or `suffices P by simpa`. Avoid a large terminal `simpa` that hides the argument. An `erw`, or an `rfl` after `simp` or `rw`, means a lemma is missing. A heavy closer that needs hand-fed terms marks structure worth writing out.
- Nothing positional. A guest function, value, constant or statement is named by a stable name, never by an index, a position or a copied literal. The current mechanisms are `fn%`, `val%`, `pos%`, `guest_const%` and `lit%` (`formal/AGENTS.md`, "Changing the spec"); a parameter is its named definition.
- Load-bearing lemmas (cited by other files or needed to believe a result) are public, with a docstring. Proof helpers are `private` or outside the module's public section. Do not wrap one or two existing lemmas in a single-use helper.
- Golf only where readability is kept, and leave a working proof alone without a reason. A golf that hides the argument is a regression.
- One editing agent per file at a time.

## Budgets and build cost

- A proof that needs more than the default `maxHeartbeats` is slow for a reason. Profile it (`python3 -I tools/profile.py FILE`) and fix the cause.
- An override is scoped to one declaration (`set_option maxHeartbeats N in`) with a one-line comment saying why, never set on a file. `formal/AGENTS.md` says when not to raise one at all, and how to keep the elaborator off a heavy term.
- A kernel check of large data goes in a module of its own, importing only what it evaluates. `python3 -I tools/deps.py cone FILE` says what an edit of `FILE` rebuilds.
- A hand-written file stays under about 1500 lines. The report below lists longer ones; it is a reading aid, not a gate.

## Trust

The gates stay as they are, and are run by `check-all.sh` and `.github/workflows/lean.yml`:

- the escape scan (`tools/escape-scan.py`): no `sorry`, `admit`, `native_decide`, `+native`, `unsafe`, `implemented_by`, `@[extern]`, `#exit`, `axiom` declaration, or way to skip the kernel that `#print axioms` cannot see;
- the axiom footprint (`tools/axiom-footprint.sh`): every end theorem depends on at most Lean's three standard axioms;
- every warning is an error, deprecations included, and no lakefile sets an option that skips the kernel;
- the statement imports nothing of the proof projects (the CI step lists what it may import), and `import all` only of its generated data.

Beyond the gates:

- Trust a result by the kernel (`#print axioms`, the footprint), never by a grep alone: the escape scan complements the kernel, it does not replace it.
- Generated files are regenerated, never edited (`formal/AGENTS.md` lists them and their generators).
- A checker or certificate names the checker, the data it checks, and what stays trusted.
- The differential tests against the Rust (`fuzz-verifier.py`, `wire-diff.py`, `prover-diff.py`, `scheme-vectors`, `guest-diff`) are evidence that a transcription matches, not proof.
- Never regenerate an expected value from the code under test and call it a check: that is a change detector.
- A new check ships with a planted violation it catches. A check never seen failing proves nothing.
- A disagreement between the Lean and its source is a finding, reported. It is never resolved by weakening the property or by editing one side to match the other.

## Comments and documentation

- Module docstring: a title, what the module provides, and its source by name.
- Declaration docstring: one line or a few, what it returns or states, its hypotheses in words. Details (a step, an offset, a size, an edge case) go in a `--` comment above the line they describe.
- A definition that transcribes a step-by-step procedure marks each step of its source (the Rust function, the guest function or the `doc/leanvm` section) in a `--` comment above the line that computes it, and says where the Lean departs from the source's steps (a loop bound, a value computed once and reused) and why.
- No proof narration, no history (`used to`, `now`, `no longer`), no planning codes (milestones, waves, phases, task numbers), no session notes, no rejected alternatives. Rewrite a stale comment rather than adding one beside it. A goal state in a comment comes from Lean, never from memory.
- No commented-out declarations. No `#eval`, `#print`, `#check` or `#reduce` left in a library module, except the root files' pinned axiom checks and commands that are checks themselves (under `#guard_msgs`, or failing the build, as a firewall module's `#eval` does).

## Names

- Mathlib's conventions: types and propositions `UpperCamelCase`, other terms `lowerCamelCase`, theorems `snake_case`, the conclusion first and then `_of_` each hypothesis.
- A Rust item `foo_bar` is `fooBar` in Lean, so it can be found from the Rust.
- Name a declaration for what it states, never for a paper's numbering, an author, a milestone or a review round.

## Reviews and CI

- `.github/workflows/formal-report.yml` runs `tools/pr-report.py` on every pull request that touches `formal/`, the skills or the contributor docs, and shows what changed in the statement, budgets and suppressions, leftovers, long files and declarations, prose and unsafe Unicode, as a job summary and warnings. It never fails on a finding. Run it before you push: `python3 -I formal/tools/pr-report.py`.
- `.github/workflows/formal-review.yml` is an AI review on demand: a maintainer comments `/formal-review` (optionally followed by what to look at) on a pull request, and it posts its findings as a comment. It never approves or requests changes.
- People approve.

| task | skill |
| --- | --- |
| write or change a definition or statement; transcribe Rust or `doc/leanvm` | `formal-statements` |
| write, refactor or golf a proof | `formal-proofs` |
| bring proofs back after a change to the Rust, the guest or a dependency | `formal-repair` |
| review a pull request or branch | `formal-review` |
| make a branch ready for review | `formal-pr` |

For proof mechanics (search, tactics, error triage), the `lean4` plugin's skills apply: `lean4:prove`, `lean4:golf`, `lean4:refactor`, `lean4:review`.
