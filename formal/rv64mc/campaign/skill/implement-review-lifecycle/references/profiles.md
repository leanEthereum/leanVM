# Profiles

A profile is a spec with the stages filled in. Name it in `profile` and override any field. Pick by what is at stake: who reads the result, and what a missed mistake would cost.

| profile | use for | reviewers | rounds |
|---|---|---|---|
| `lean-proof` | proofs, refactors, golfing, new lemmas; no statement a user relies on changes | 1 Opus | 3 |
| `lean-statement` | any change to a definition or theorem statement others rely on (a specification, a trusted file, an API) | 2 independent Fable reviewers per round | 4 |
| `lean-build-speed` | making Lean builds or proofs faster without changing what is proved | 1 Opus | 2 |
| `generic-code` | code in any language | 1 reviewer on a different model than the implementer | 3 |

Skill names below are the ones Claude Code lists (plugin skills as `plugin:skill`). If a skill is not installed, the stage proceeds without it and says so.

## lean-proof

Proof-only work: the statements stay, the proofs get written, shortened or reorganised.

```json
{
  "profile": "lean-proof",
  "pipeline": ["implement", "golf", "review-loop"],
  "maxRounds": 3,
  "stages": {
    "implement": { "model": "opus", "skills": ["lean4:prove", "lean4:refactor", "writing-lean-proofs"] },
    "golf":      { "model": "opus", "skills": ["lean4:golf", "lean4:refactor"] },
    "review":    { "model": "opus", "count": 1, "skills": ["adversarial-review", "lean4:review"] },
    "fix":       { "model": "opus", "skills": ["lean4:prove"] },
    "rereview":  { "model": "opus", "count": 1, "skills": ["adversarial-review"] }
  },
  "context": "No statement changes: every non-private declaration keeps its type. No sorry, axiom, native_decide, implemented_by; no raised maxHeartbeats/maxRecDepth unless the defence justifies it. Prefer upstream (Mathlib or the project's pinned libraries) lemmas over local copies."
}
```

The golf stage follows `lean4:golf`'s policy (directness before length; no naked semicolons; no heavier automation for a one-line win) and must state in the defence why each change preserves the proof's meaning.

## lean-statement

For changes to what is proved: a specification file, a theorem statement, a trusted definition. The statement is the product, so the review is the most expensive part.

```json
{
  "profile": "lean-statement",
  "pipeline": ["implement", "review-loop", "golf", "review-loop"],
  "maxRounds": 4,
  "stages": {
    "implement": { "model": "opus", "skills": ["lean-spec-authoring", "lean4:prove"] },
    "golf":      { "model": "opus", "skills": ["lean4:golf"] },
    "review":    { "model": "fable", "count": 2, "skills": ["adversarial-review", "lean-spec-authoring"] },
    "fix":       { "model": "opus", "skills": ["lean-spec-authoring"] },
    "rereview":  { "model": "fable", "count": 2, "skills": ["adversarial-review", "lean-spec-authoring"] }
  },
  "context": "Every statement change comes with: a proved relation between the old and new statement (equivalence, or the direction that shows the change is a strengthening), restated old definitions in a test file, a non-vacuity witness for every new hypothesis, and the human-readable documents kept in step. Transcribed constants are checked against their source (read the source first, then the Lean)."
}
```

Two reviewers on a model other than the implementer's see different things; the round is clean only if both are. The second `review-loop` reviews the golf, which can quietly change a statement's elaborated form.

## lean-build-speed

For build-time work: same guarantees, cheaper checking.

```json
{
  "profile": "lean-build-speed",
  "pipeline": ["implement", "review-loop", "golf"],
  "maxRounds": 2,
  "stages": {
    "implement": { "model": "opus", "skills": ["lean4-build-speed", "maintaining-lean-projects"] },
    "golf":      { "model": "opus", "skills": ["lean4:golf"] },
    "review":    { "model": "opus", "count": 1, "skills": ["adversarial-review", "lean4-build-speed"] },
    "fix":       { "model": "opus", "skills": ["lean4-build-speed"] },
    "rereview":  { "model": "opus", "count": 1 }
  },
  "context": "Same guarantees: statements and axioms unchanged, nothing newly trusted (no native_decide), the kernel still checks everything. Every speed claim in the defence is a before/after pair measured interleaved on the same machine (CPU seconds and peak memory), with the command; extrapolations are labelled."
}
```

The reviewer treats an unmeasured or non-interleaved speed claim as drift (`evidence-does-not-reproduce`), and anything that could make the build report "proved" for something weaker as an important defect.

## generic-code

```json
{
  "profile": "generic-code",
  "pipeline": ["implement", "review-loop"],
  "maxRounds": 3,
  "stages": {
    "implement": { "model": "sonnet" },
    "review":    { "model": "opus", "count": 1 },
    "fix":       { "model": "sonnet" },
    "rereview":  { "model": "opus", "count": 1 }
  },
  "context": "Run the project's tests for the changed code (`check`) and quote the result. No unrelated refactors."
}
```

Add `"golf"` to the pipeline when the user wants the result tightened, and a second reviewer for security-relevant or user-facing changes.

## Choosing models

- **Independence over strength** for reviews: a reviewer on the same model as the implementer shares more of its blind spots. When it matters, use a different model or two reviewers.
- **The strongest model where a miss is costly**: statements, specifications, anything trusted.
- **A cheaper model where the work is mechanical** (golf on clear patterns, generic fixes), but keep reviews on a capable model.
- Do not set `effort` unless the user asked for a level.
