# The defence

A defence is the implementer's case to the reviewer: what it did, why, what it claims stays true, and the evidence. It lives in the run directory as `DEFENCE.md`, never in code, comments or commit messages. Commit messages still say what and why for the project's readers; the defence goes further, because its job is to be attacked.

Why it helps: an implementer that has to write "the statement is byte-identical" will check that it is, and a reviewer handed that sentence can refute it in one command. Unstated assumptions survive reviews; stated ones mostly do not.

## Template

```markdown
# Defence: <task in one line>

Base: <commit>. Head: <commit>. Check: `<command>` -> <result, e.g. "0 errors, 12.3 s">.

## Decisions

### D1. <the change, with file and declaration names>
- **Why**: <the reason; what it fixes or enables>.
- **Rejected**: <the alternative considered and why not>.
- **Claims**: <each invariant this change keeps, written so it can be checked>.
- **Evidence**: <the exact command and its output, or the measurement with its method>.

### D2. ...

## Invariants of the whole change
- <e.g. "No theorem statement changed: `git diff <base> -- '*.lean' | grep '^[-+]theorem'` is empty except D3's private lemma.">
- <e.g. "No sorry/axiom/native_decide added: `git diff <base> | grep -E '^\+.*(sorry|axiom|native_decide)'` is empty.">

## Not done
- <what was left out, why, and what it would take>.

## Known risks
- <where the reviewer should look hardest, in the implementer's own opinion>.
```

Keep it short: one entry per decision a reviewer could disagree with, not per line changed. Mechanical edits (renames at use sites, import lines) can share one entry.

## A weak and a strong entry

Weak (unfalsifiable, no evidence):

> **D2.** Cleaned up the helper lemmas and made things more consistent. Everything still builds.

Strong:

> **D2. Replace `foo_aux`, `foo_aux'` and `foo_aux₂` (Foo/Bar.lean) by one `foo_aux (n : ℕ)`.**
> - **Why**: the three differed only in a literal (1, 2, 4); every caller passes a literal.
> - **Rejected**: a `simp` set over the three: still three lemmas to maintain.
> - **Claims**: `foo_aux` is private; no other file named the old ones; the three callers' proofs are otherwise unchanged.
> - **Evidence**: `grep -rn "foo_aux" --include=*.lean .` lists only Foo/Bar.lean; `lake env lean Foo/Bar.lean` -> no errors (8.1 s, was 8.4 s).

## How later stages extend it

- **Golf** appends `## Golf` with one entry per change, each saying why it preserves meaning (same statement, a lemma used is equivalent, the tactic closes the same goal) and the check result. A golf entry that cannot say why the change is equivalent should not be made. If golf removes or renames something an earlier entry names, the golf entry says which earlier claims it supersedes ("supersedes D3: `foo_aux'` no longer exists"), so the defence stays true as a whole.
- **Fix** appends `## Amendments, round N`: for each finding, the disposition (fixed / rebutted / deferred), what changed, and the evidence. If a fix contradicts an earlier claim, say so explicitly ("D2's claim that no other file used `foo_aux'` was wrong: Baz.lean did; fixed there too"). Never edit an earlier entry in place: the reviewer needs to see what was claimed when. The close-out pass at the end of a clean round does the same for drift findings: it records each correction as an amendment ("D1's title said old-implies-new; the code proves new-implies-old").

## What a reviewer looks for in it

Every claim is checked against the diff and, where cheap, rerun. The drift categories (`claim-not-in-code`, `code-not-in-defence`, `evidence-does-not-reproduce`, `scope-drift`) are in `review.md`. A defence that is accurate about a bad change is better than a vague one about a good change: the first gets a precise finding and a quick fix.
