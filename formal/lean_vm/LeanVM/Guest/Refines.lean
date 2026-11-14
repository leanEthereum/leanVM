/-
  LeanVM.Guest.Refines

  A verifier program refining another: the same program with failures inserted.
-/

module

public import LeanVM.Protocol.RunWithHash

/-!
# Refining programs

`Refines P' P`: the program `P'` is `P` with failures inserted, step for step. Running a refining
program is running the program, where it does not fail (`run_refines`, `runProof_refines`). No
guest data: the protocol's compiled verifier (`Protocol/Compile/Rom/Ideal.lean`) and the guest's
zero-challenge refusal (`LimitsNZ.lean`) both read it.
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`P'` refines `P`**: it is `P` with failures inserted. -/
inductive Refines {α : Type} : VerifierProgram α → VerifierProgram α → Prop
  | fail (P : VerifierProgram α) : Refines .fail P
  | ret (a : α) : Refines (.ret a) (.ret a)
  | read {k k' : E → VerifierProgram α} : (∀ x, Refines (k' x) (k x)) → Refines (.read k') (.read k)
  | sample {k k' : E → VerifierProgram α} : (∀ x, Refines (k' x) (k x)) → Refines (.sample k')
      (.sample k)
  | grind {b : ℕ} {k k' : VerifierProgram α} : Refines k' k → Refines (.grind b k') (.grind b k)
  | commit {h w : ℕ} {k k' : VerifierProgram α} : Refines k' k → Refines (.commit h w k')
      (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k k' : List (List K) → VerifierProgram α} :
      (∀ r, Refines (k' r) (k r)) → Refines (.query i ps k') (.query i ps k)

namespace Refines

variable {α β : Type}

theorem refl : ∀ P : VerifierProgram α, Refines P P
  | .ret a => .ret a
  | .fail => .fail _
  | .read k => .read fun x ↦ refl (k x)
  | .sample k => .sample fun x ↦ refl (k x)
  | .grind _ k => .grind (refl k)
  | .commit _ _ k => .commit (refl k)
  | .query _ _ k => .query fun r ↦ refl (k r)

theorem bind {P' P : VerifierProgram α} (h : Refines P' P) {f' f : α → VerifierProgram β}
    (hf : ∀ a, Refines (f' a) (f a)) : Refines (P'.bind f') (P.bind f) := by
  induction h with
  | fail P => exact .fail _
  | ret a => exact hf a
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- A `require` before a refining program refines the program. -/
theorem require_bind {c : Prop} [Decidable c] {k' k : VerifierProgram α} (h : Refines k' k) :
    Refines ((VerifierProgram.require c).bind fun _ ↦ k') k := by
  unfold VerifierProgram.require
  split
  · exact h
  · exact .fail _

end Refines

section Run

variable {H : Bytes → Id Digest} {F : KeccakState → Id KeccakState}

/-- **Running a refining program is running the program**, where it does not fail. -/
theorem run_refines {α : Type} {P' P : VerifierProgram α} (h : Refines P' P) :
    ∀ (s : VerifierProgramState) (r : α × VerifierProgramState), Id.run (Compile.runWithHash H F P'
        s) = some r →
      Id.run (Compile.runWithHash H F P s) = some r := by
  induction h with
  | fail P =>
    intro s r hr
    simp [Compile.runWithHash] at hr
  | ret a => intro s r hr; exact hr
  | read _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    split at hr
    · exact ih _ _ _ hr
    · simp at hr
  | sample _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    exact ih _ _ _ hr
  | grind _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    split at hr
    · simp only [Id.run_bind] at hr ⊢
      split at hr
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ _ hr
      · simp at hr
    · simp at hr
  | commit _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    split at hr
    · exact ih _ _ hr
    · simp at hr
  | @query i ps k k' _ ih =>
    intro s r hr
    obtain ⟨root, height, width, phase, rest, rows, hroot, hos, ho, hr⟩ :=
      (Compile.runWithHash_query_eq_some_iff H F i ps k' s r).mp hr
    exact (Compile.runWithHash_query_eq_some_iff H F i ps k s r).mpr
      ⟨root, height, width, phase, rest, rows, hroot, hos, ho, ih _ _ _ hr⟩

/-- **A refining program accepts only what the program accepts.** -/
theorem runProof_refines {P' P : VerifierProgram Bool} (h : Refines P' P) (seed : KeccakState) (π
    : Proof)
    (hacc : Id.run (runProofWithHash H F P' seed π) = true) : Id.run (runProofWithHash H F P seed π) = true := by
  unfold runProofWithHash at hacc ⊢
  simp only [Id.run_bind] at hacc ⊢
  cases hr : Id.run (Compile.runWithHash H F P' ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩) with
  | none => rw [hr] at hacc; exact absurd hacc (by simp)
  | some r =>
    rw [run_refines (H := H) (F := F) h _ _ hr]
    rw [hr] at hacc
    exact hacc

end Run

end
end LeanVM.Guest.Limits
