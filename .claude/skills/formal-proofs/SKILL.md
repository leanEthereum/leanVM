---
name: formal-proofs
description: Write, refactor or golf Lean proofs in leanVM's formal/ so the next agent can read and repair them. Use when proving a lemma or theorem in formal/, splitting or cleaning up a long proof, golfing, fixing a slow or heartbeat-hungry proof, or deciding where a helper lemma belongs. Covers proof structure, the extraction ladder, automation discipline, stable names instead of positions, budgets, docstrings and golfing policy. Proof mechanics (search, tactics, error triage) are the lean4 plugin's.
---

# Write a proof the next agent can repair

Proofs in `formal/` break whenever the Rust, the guest or a dependency changes, and the next agent repairs them without your context. Write for that agent: the argument visible, each step stated, nothing that depends on a position or an accident of elaboration. The rules are `formal/CONTRIBUTING.md` ("Proofs the next agent can repair", "Budgets and build cost"). For search, tactics and error triage use the `lean4` plugin's skills (`lean4:prove`, `lean4:golf`, `lean4:refactor`) or their equivalents.

**The statement does not move.** A proof never changes the statement it proves. If it seems to need to, stop and use `formal-statements`.

**Done means:** the module builds with the real build (`lake build <Module>`, or `python3 -I ../lake-build.py . <Module>` from the project for a heavy one), with no new warning; every theorem the change names has the expected axioms (`#print axioms` in a temporary file, or the project's root file); the frozen statement is unchanged; and the proof reads as its argument: named steps, no unexplained heavy closer, no positional reference, no copied proof.

## Procedure

1. **Read the contract.** Before proving anything about a definition, find the lemmas its module exports (spec lemmas, normal forms, `@[simp]` sets). Use them; do not unfold the definition. If the lemma you need is missing, add it to the module that owns the definition.
2. **Sketch top-down.** Write the proof as named steps (`have h : stmt := by sorry`, or lemmas stated with `sorry`) on a branch, check the skeleton compiles, then fill the steps bottom-up. `sorry` never lands (the escape scan fails it).
3. **Extract along the ladder** when a step grows or repeats:
   1. an inline `have` with its statement written out;
   2. a lemma in the same file, `private` if no other file needs it;
   3. a lemma in the module that owns the definition it is about, public with a docstring, when a second file needs it;
   4. a generic lemma in the project's `To<Library>/` directory (as `lean_vm/LeanVM/ToMathlib/`), stated as the upstream library would state it, when it is about Mathlib, ArkLib, CompPoly, VCVio or Clean objects alone.

   Do not wrap one or two existing lemmas in a single-use helper; do not create helpers with many parameters to save a few lines.
4. **Prove once.** A proof you are about to copy for the next function, instance or table row is a lemma or a generator rule waiting to be written: one theorem plus generated instances, or a decision procedure by reflection (`decide +kernel` on a checker proved sound). `formal/AGENTS.md` describes the generators.
5. **Name, never point.** A guest function, value, constant or statement is named by a stable name (`fn%`, `val%`, `pos%`, `guest_const%`, `lit%`: `formal/AGENTS.md`, "Changing the spec"), never by an index, a drop count or a copied literal. A protocol parameter is its named definition. If no stable name exists for what you need, add one through the mechanism rather than writing the number.
6. **Discipline the automation.** Terminal automation, or automation after an explicit shaping step. A non-terminal `simp` is `simp only [...]`, or `have h : P := by simp`, or `suffices P by simpa`. Leave a stable terminal `simp` unsqueezed. A large terminal `simpa` or a heavy closer (`grind`, `aesop`, `omega` over a large context) that needs hand-fed terms hides structure worth writing out. `erw`, or `rfl` after `simp`/`rw`, means a missing lemma.
7. **Keep the cost down.** If a declaration is slow, profile before anything else: `python3 -I tools/profile.py FILE` from `formal/`. Fix the cause (`formal/AGENTS.md` lists the usual ones: the elaborator evaluating a heavy term, tactics reading a large context). An override is `set_option maxHeartbeats N in` on that declaration, with a one-line reason; never on a file, and never `maxRecDepth` for an evaluation the elaborator should not do. Heavy kernel checks go in modules of their own.
8. **Document.** Load-bearing lemmas get a one-to-few-line docstring saying what they state; proof helpers are `private`. In a proof over about 50 lines, a `--` comment above each non-obvious step says what it establishes. No narration of how the proof was found, no history, no goal states you did not copy from Lean.

## Golfing

Golf for readability first, length second. Keep `have` names that say what they hold and statements that show the argument. A golf that hides the argument behind one closer is a regression, and so is one that makes the proof slower to elaborate. Do not golf or "clean up" a working proof you were not asked to touch. Stop when the suggestions stop being clear wins.

## Rationalizations to reject

| thought | answer |
| --- | --- |
| "It compiles, so it is fine." | The next agent has to repair it. Can they find the argument? |
| "A bigger heartbeat budget is quicker." | Every override is a slow proof that will get slower. Profile it. |
| "I will copy this proof for the next function." | Then there will be N copies to repair. Write the lemma or the generator rule. |
| "Unfolding is easier than finding the lemma." | The unfolding breaks when the definition changes shape. Use or add the contract lemma. |
| "The index is stable enough." | Positions shift with every guest edit. Use the stable name. |
| "I will restructure it into lemmas after it works." | You will not. Sketch the steps first. |
| "Shorter is better." | Clearer is better. |

## References

- [`references/patterns.md`](references/patterns.md): before and after, for the patterns above.
- `formal/AGENTS.md`: the build, `--dev`, the elaboration traps, the generators.
