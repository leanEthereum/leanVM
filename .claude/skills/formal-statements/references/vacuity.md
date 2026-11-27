# Vacuity and tautology: the checks

Both compile, pass every gate and survive a skim. Run these before you call a statement done; each is cheap.

## A witness for the hypotheses

Build one concrete value that satisfies all the hypotheses at once, at the deployed parameters, as a term Lean accepts:

```lean
-- the statement
theorem foo (x : K) (h₁ : P x) (h₂ : Q x) : R x := ...
-- the witness, kept in the project's tests
example : P c ∧ Q c := by decide
```

If you cannot build one, the statement is vacuous or its satisfiability is a real question: say which. Keep the witness as a guard theorem in the project's `tests/` (`lean_vm/tests/LeanVMTests/` for `lean_vm`), with a docstring naming the definition it guards. It fails when someone tightens the definition past what the deployed instance satisfies; a comment does not.

Where vacuity comes from:

- **Hidden exclusions.** A hypothesis that conjoins conditions another definition makes exclusive (two opcode flags, two phases of the verifier). Enumerate the admissible cases first.
- **Assuming what is asserted.** A hypothesis that restates a check the verifier performs. The verifier's checks belong in the verifier, not in the theorem's assumptions.
- **Success or resource conditions that swallow the claim.** "Whenever the prover succeeds", "within the limits": legitimate, but exhibit an input that meets them, at the deployed stack sizes and rates.
- **Contradictory numeric side conditions**, often several definitions apart: `omega` settles them.
- **Characteristic 2.** In `K = GF(2^64)` and its extension `E`, `x + x = 0`, `2 = 0` and `-x = x`. A hypothesis carried over from prime-field reasoning (`(2 : K) ≠ 0`, `x ≠ -x`) is unsatisfiable here.
- **Over-strong hypotheses generally.** Try to exhibit an admissible input the hypotheses exclude. If one exists, the theorem is not vacuous, but it is weaker than it reads.

## The probe

State the theorem as an `example` in a temporary file outside the projects' sources, run with `lake env lean FILE` from the project after building it (a module of the project is checked with `lake build`; a probe that no lakefile builds is the exception), and try each closer alone:

```lean
example (x : K) (h₁ : P x) (h₂ : Q x) : R x := by trivial
example (x : K) (h₁ : P x) (h₂ : Q x) : R x := by simp
example (x : K) (h₁ : P x) (h₂ : Q x) : R x := by decide
example (x : K) (h₁ : P x) (h₂ : Q x) : R x := by aesop
example (x : K) (h₁ : P x) (h₂ : Q x) : R x := by exact?
```

Read every proof found. One that ignores the main hypotheses means the statement is too weak or a definition is degenerate. Then find unused hypotheses: `lean_minimal_hypotheses` (lean-lsp tools) or delete each in turn. The unused-variable linter only finds a hypothesis that is never mentioned, not one mentioned but not needed.

## The substitution test

Replace the object the statement is about by another of the same shape: another verifier, another hash, another error bound, another program. If the statement still holds by the same proof, it restates its definitions rather than specifying them.

Symptoms:

- The specification is built only from the object's own vocabulary (its accessors, its constraint builders).
- An `↔` whose sides are definitionally equal (`Iff.rfl` proves it). That is a bridge lemma, proof help, not a specification.
- The proof is `rfl`, `simp [Spec]` or `unfold Spec; tauto`. Not proof of a tautology, but read what it did.
- Nothing but a change to the definition could falsify it.
- A correspondence defined as "whatever the Rust computes": it cannot disagree with the Rust, so it says nothing about it.

The repair: state the semantic form as the specification and derive the mechanical form as a lemma, never the reverse.

## Bounds and rejections

- An error bound must be below one at the deployed parameters (`Statement/LeanVmVerifier.lean`'s constants). Prove or evaluate that, and keep it in the tests.
- A predicate that must reject some inputs has a rejected case in the tests, so a definition that accepts everything fails.

## Degenerate forms

Reject on sight, judged by meaning, not spelling:

- a structure field of type `True`, a theorem concluding `True`, `∃ x, ..., True`;
- an `else True` branch, a relation no value satisfies, a definition every value satisfies;
- a `variable` hypothesis that assumes or trivially entails the conclusion;
- a public declaration whose conclusion collapses to `True` once its definitions unfold.

## Freeze, then diff

Before proof work, save the elaborated statement of every declaration you will prove:

```lean
#check @LeanVM.someTheorem
#print LeanVM.SomeDefinition
```

Run them in a temporary file outside the projects, save the output, and run them again after the proof. Only proof bodies may differ. A difference is a statement change: go back to the protocol in `SKILL.md`, section 5.
