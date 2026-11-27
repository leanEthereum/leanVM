# Reviewing: defects and drift

The reviewer gets the task, the diff (`base..head`, or since the last review), the defence, and the previous round's findings and dispositions when there are any. It does not edit files. It may run read-only commands and the cheap `check`.

## Order of work

1. Read the task and the defence first, and list every claim (each "Claims", "Evidence" and "Invariants" line).
2. Read the diff hunk by hunk. For each hunk: is it covered by a decision in the defence? Is it correct?
3. Check each claim against the diff; rerun the cheap evidence (the `check`, a grep, a statement diff). Treat a claim you cannot check as unverified, not as true.
4. Look outside the diff only to test one specific thing: users of a deleted or renamed name, the statement of a lemma a hunk cites, the definition a claim depends on. Do not change the working tree to do it (no `git stash`, `checkout` or `reset`); use `git show <base>:<file>`, `git diff`, or a scratch copy.
5. Keep to the change. Scripts and probes the implementer wrote are evidence; attack them only as far as a claim depends on them.
6. Write the findings.

## Defects (in the code)

- **Wrong or unsound**: incorrect logic, an edge case, a proof that proves something weaker than claimed, a check removed or narrowed, an option that skips verification.
- **Specification**: a statement changed outside the task; a vacuous or tautological statement (true because a hypothesis is unsatisfiable, or because it restates its definition); a new hypothesis without justification; for transcribed artefacts, a mismatch with the source (read the source first). Use `adversarial-review` and, for statements, `lean-spec-authoring`.
- **Trust**: `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, disabled kernel checks, raised limits that hide a cost.
- **Quality**: duplication left behind, an abstraction that adds indirection without removing anything, local copies of upstream lemmas, docstrings that describe history instead of the present, names that do not follow the project's conventions.
- **Performance and build**: slower modules, larger rebuild cones, memory blowups, missing measurements.
- **Tests**: changed behaviour without a test that would catch its regression.

## Drift (between defence and code)

| kind | what it means | example |
|---|---|---|
| `claim-not-in-code` | the defence asserts something the diff does not bear out | "statement unchanged", but the diff changes an implicit argument |
| `code-not-in-defence` | the diff contains a change no decision covers | an unrelated file edited; a lemma deleted silently |
| `evidence-does-not-reproduce` | the quoted command or measurement does not give the quoted result, or the method cannot support the claim | a speed-up measured once on a loaded machine; a grep that misses a directory |
| `scope-drift` | the work went beyond (or fell short of) the task or the files it owns, without saying so | a refactor of neighbouring code; half the requested functions done, reported as done |

Drift is often the most valuable finding: an implementer who believes a false claim has usually made the mistake the claim denies. Report drift even when the code is right (a wrong title, a claim about something golf removed, an overstated guarantee): it is cheap to fix in the close-out, and a defence that no longer matches the code misleads everyone who reads it later.

## Severity and evidence

- `important`: a defect that makes the result wrong, unsound, weaker than claimed, or unusable; any drift about soundness, statements or trust; missing evidence for a key claim.
- `nit`: style, naming, clarity, a minor missing measurement, a speculative concern.
- Every finding needs a concrete failure scenario or a piece of evidence (a quoted hunk, a command and its output). Without one, it is a nit at most.
- Do not report the same issue twice under two kinds; pick the more specific one.

## Findings schema

```json
{
  "clean": false,
  "summary": "two sentences: what was reviewed, the verdict",
  "claims_checked": [
    { "claim": "D1: statement of foo_le_bar unchanged", "verdict": "holds", "how": "git diff base -- Foo/Bar.lean shows only the proof" }
  ],
  "findings": [
    {
      "id": "R1-1",
      "severity": "important",
      "kind": "claim-not-in-code",
      "location": "Foo/Bar.lean:42",
      "claim": "D2: no other file used foo_aux'",
      "issue": "Baz.lean:17 still calls foo_aux'",
      "evidence": "grep -rn \"foo_aux'\" . -> Baz.lean:17",
      "suggested_fix": "update Baz.lean or keep an alias"
    }
  ]
}
```

`kind` is one of `defect`, `spec`, `trust`, `quality`, `performance`, `test-gap`, `claim-not-in-code`, `code-not-in-defence`, `evidence-does-not-reproduce`, `scope-drift`, `process`. `claim` quotes the defence for drift findings and is empty otherwise. `clean` is true only when no `important` finding remains.

## Re-review

For each previous finding, using the fixer's disposition:
- **fixed**: confirm in the new diff; close it, or carry it over with what is still wrong.
- **rebutted**: judge the evidence. A good rebuttal closes the finding; a weak one carries it over with the reason.
- **deferred**: accept if the reason is sound and the user can act on it; otherwise carry it over.

Then review the new diff and the defence's amendment like a first review (new defects, new drift, and amendments that contradict earlier claims without saying so). Give carried-over findings their original id.
