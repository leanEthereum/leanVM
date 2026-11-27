---
name: formal-statements
description: Write or change a Lean definition or theorem statement in leanVM's formal/, above all in the trusted statement formal/Statement/, or transcribe Rust, the guest or doc/leanvm into Lean. Use when asked to state, specify, define, transcribe, formalize or change what is proved, to add or drop a hypothesis, to change an end theorem in Statement/Theorems.lean, or when a proof seems to need a statement change. Covers source authority, hypothesis discipline, vacuity and tautology checks, and the statement-change protocol.
---

# Write a statement

The statement is the deliverable; the proof is replaceable. A wrong statement makes every proof of it worthless, and no build finds it. So the order is fixed: write the statement, convince yourself it means what it should, then prove it. **If the proof is hard, the statement does not move.**

Work as the specialist the statement needs: a cryptographer or proof-system engineer for security statements and the verifier, a zkVM and compiler engineer for the ISA, the executor and the guest. The rules are `formal/CONTRIBUTING.md` ("The trusted statement"). Proof mechanics are elsewhere (`formal-proofs`, `lean4:prove`).

**Done means:** every new or changed declaration has a source you cite by name, each hypothesis is justified, a witness shows the hypotheses satisfiable, the substitution test fails, and, for a change to `formal/Statement/`, the four items of the statement-change protocol below are in the pull request.

## 1. Classify before you read a source

The order in which you read sources decides what you can still notice. Decide first which kind of content you are writing:

- **Transcribed**: the verifier (`Statement/Verifier/` follows `crates/verifier/src`), the ISA, the executor, hash inputs and domain separators, the wire encoding, the guest's bytecode, protocol parameters. The Rust (or the guest, `guests/lean_ethereum.py`) is authoritative: read it first, and copy it, do not paraphrase. A deviation is allowed only when you can name the property that licenses it. Read [`references/transcription.md`](references/transcription.md) before you start.
- **Specified**: models, games, security properties, error bounds, the end statements. `doc/leanvm` and the papers are authoritative. Form your expectation from them and from your own reasoning, write the Lean, then read the Rust and compare. If you read the Rust first, say so in the description: the statement's independence is compromised.

A rough test: the hypotheses of a soundness theorem are usually transcribed, its conclusion specified.

If two sources disagree, stop and report it. A suspected Rust bug is a finding for the description and the maintainers, never an edit to either side.

## 2. Definitions

- Name a concept that exists without the code that consumes it. State the semantic form (what is computed, what holds) and prove the operational form (constraints, a loop, a table) equal to it as a lemma.
- Prefer the shortest form a domain expert recognises. A definition that needs a paragraph to justify its shape is usually two definitions.
- Prefer structural recursion, `map` and folds to `Id.run do` with mutable variables: a theorem about a `do` loop restates its elaborated body, and any edit to the loop breaks it.
- No `!` accessor or `panic!` that hides a failure behind a default, unless the source has the same default. No junk value (`x / 0 = 0`, an out-of-range index) standing in for a case the source rejects.
- Never add a definition only to make a proof go through.
- Cite the source by name and commit in the module docstring; step comments for transcribed procedures (`formal/CONTRIBUTING.md`, "Comments and documentation").

## 3. Hypotheses

Every hypothesis is forced by the mathematics (name the instance that breaks without it) or a real interface obligation of the caller. When a proof is hard, the forbidden moves are: strengthen a hypothesis; weaken the conclusion (`↔` to `→`, `=` to `≤`); specialise a variable or parameter (one rate, one stack size, one message length); add a side condition to dodge an edge case; redefine the object; move a check of the verifier into an assumption; assume a hash injective where only collision resistance holds.

What to do instead, in order: prove it; refute it (a counterexample is a result); leave it out and say so in the description. If a hypothesis must be added, the description names it, says why it cannot be avoided, and what a caller that cannot discharge it loses.

## 4. Check it means something

Both vacuity and tautology compile. Run the checks in [`references/vacuity.md`](references/vacuity.md) on every statement with a hypothesis:

1. Build a witness for the hypotheses together, at the deployed parameters, and keep it as a guard theorem in the project's `tests/`.
2. Probe: state the theorem as an `example` and try `trivial`, `simp`, `decide`, `aesop`, `exact?`. A proof found without the main hypotheses means the statement is weaker than it looks.
3. Find unused hypotheses (`lean_minimal_hypotheses` if the lean-lsp tools are available, else delete each and rebuild).
4. The substitution test: replace the object by another of the same shape. If the same proof still works, the statement restates rather than specifies.
5. An error bound is below one at the deployed parameters; a predicate that must reject something has a rejected case in the tests.
6. No `True` field or conclusion, no `∃ x, ..., True`, no `else True`, no empty relation, no `variable` hypothesis that entails the conclusion.

Before you start a proof, freeze the statement: save `#check @Name` and, for a definition, `#print Name`. After the proof, compare. Only proof bodies may differ.

## 5. Changing formal/Statement/

Every change there changes what is proved. Ask the maintainers first. The pull request then carries:

1. a proved relation between old and new, kept in a proof project's tests (as `lean_vm/tests/LeanVMTests/Statement/`): an equivalence, or the implication showing the new statement stronger, or why it must be weaker;
2. a witness for each new hypothesis;
3. `formal/statement.tex` in step (`python3 -I tools/docnames.py`, from `formal/`, lists the names it cites that no Lean file has: read its hits, some are not Lean names);
4. the statement before and after, in a `text` block, in the description.

`Statement/` holds definitions and end statements only; a proof belongs to the proof projects unless a definition needs it. Its imports are restricted (CI checks them; `formal/AGENTS.md`, "Statement").

## 6. Readable headline theorems

The fields of `Theorems` (`Statement/Theorems.lean`) and the end statements they name are read by people who do not read Lean daily. Each has a docstring of a line or a few: what it means in words, its hypotheses in words, the file that defines it. No proof narration, no history.

## Checklist

- [ ] Classified as transcribed or specified, and read in that order; the description says if not.
- [ ] Every source cited by name and commit; no line numbers.
- [ ] Every hypothesis justified; none added and no conclusion weakened for a proof's sake.
- [ ] A witness for the hypotheses, kept in tests; the probe and the substitution test run.
- [ ] Load-bearing lemmas public with a docstring; proof helpers private.
- [ ] Disagreements with a source reported as findings, not absorbed.
- [ ] For `Statement/`: the four protocol items, and the frozen `#check`/`#print` unchanged by proof work.
