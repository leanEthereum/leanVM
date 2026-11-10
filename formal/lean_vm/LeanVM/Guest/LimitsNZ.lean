/-
  LeanVM.Guest.LimitsNZ

  The zero-challenge refusal restricts the Spec's deferring verifier: a child's proof the verifier refusing
  a zero challenge accepts, the Spec's accepts.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.Limits
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash

/-!
# The zero-challenge refusal is a restriction

`Refines P' P`: the program `P'` is `P` with failures inserted, step for step. Running a refining
program is running the program, where it does not fail (`run_refines`, `runProof_refines`). The
deferring program refusing a zero fold, tail or level batching challenge refines the deferring
program (`deferredProgramNZ_refines`), so `AcceptableChild`'s refusal gives every child's acceptance by the
Spec's deferring verifier (`verifyDeferred_of_nz`): it only removes runs, those with a zero
challenge where the guest divides.
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

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
    cases hs : s.stream with
    | nil => simp [hs] at hr
    | cons x xs =>
      simp only [hs] at hr ⊢
      exact ih _ _ _ hr
  | sample _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    exact ih _ _ _ hr
  | grind _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    cases hs : s.stream with
    | nil => simp [hs] at hr
    | cons x xs =>
      simp only [hs, Id.run_bind] at hr ⊢
      split at hr
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ _ hr
      · simp at hr
  | commit _ ih =>
    intro s r hr
    unfold Compile.runWithHash at hr ⊢
    rcases hs : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · simp [hs] at hr
    · simp [hs] at hr
    · simp only [hs, Id.run_bind] at hr ⊢
      cases hd : digestFromHalves (x0, x1) with
      | none => simp [hd] at hr
      | some root =>
        simp only [hd] at hr ⊢
        exact ih _ _ hr
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
  cases hr : Id.run (Compile.runWithHash H F P' ⟨⟨seed, []⟩, π.stream, π.openings, []⟩) with
  | none => rw [hr] at hacc; exact absurd hacc (by simp)
  | some r =>
    rw [run_refines (H := H) (F := F) h _ _ hr]
    rw [hr] at hacc
    exact hacc

end Run

/-! ## The deferring program refusing a zero challenge -/

theorem foldRoundsNZ_refines (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    Refines (foldRoundsNZ b n s lf) (foldRoundsT b n s lf)
  | 0, s, lf => Refines.refl _
  | n + 1, s, lf => by
    unfold foldRoundsNZ foldRoundsT
    refine Refines.bind (Refines.refl _) fun _ ↦ ?_
    refine Refines.bind (Refines.refl _) fun c ↦ ?_
    refine Refines.require_bind ?_
    refine Refines.bind (Refines.refl _) fun quad ↦ ?_
    exact foldRoundsNZ_refines b n _ _

theorem tailRoundsNZ_refines : ∀ (n : ℕ) (t : E) (quad : List E),
    Refines (tailRoundsNZ n t quad) (tailRoundsT n t quad)
  | 0, t, quad => Refines.refl _
  | n + 1, t, quad => by
    unfold tailRoundsNZ tailRoundsT
    refine Refines.bind (Refines.refl _) fun c ↦ ?_
    refine Refines.require_bind ?_
    split
    · exact Refines.refl _
    · refine Refines.bind (Refines.refl _) fun quad ↦ ?_
      exact Refines.bind (tailRoundsNZ_refines n _ _) fun p ↦ Refines.refl _

/-- The first program of a bind: the same, or a refining one. -/
local macro "refines_head" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | exact foldRoundsNZ_refines _ _ _ _
  | exact tailRoundsNZ_refines _ _ _)

/-- One step of a refinement proof between two programs written alike. -/
local macro "refines_step" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | apply Refines.require_bind
  | (refine Refines.bind ?h fun _ ↦ ?k; case h => refines_head)
  | split
  | dsimp only
  | exact Refines.refl _)

theorem whirLevelsNZ_refines (logN laneFolds : ℕ) (eb : List E → E) (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirStateT),
      Refines (whirLevelsNZ logN laneFolds eb index levels s)
        (whirLevelsT logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact Refines.refl _
  | cons level rest ih =>
    intro index s
    unfold whirLevelsNZ whirLevelsT
    apply Refines.bind (foldRoundsNZ_refines _ _ _ _)
    intro p
    obtain ⟨s', lf⟩ := p
    dsimp only
    cases rest with
    | nil =>
      dsimp only
      repeat refines_step
    | cons next rest' =>
      dsimp only
      repeat (first | exact ih _ _ | refines_step)

theorem verifyWhirNZ_refines (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    Refines (verifyWhirNZ logN logInvRate target eb) (verifyWhirT logN logInvRate target eb) := by
  unfold verifyWhirNZ verifyWhirT
  repeat (first | exact whirLevelsNZ_refines _ _ _ _ _ _ | refines_step)

theorem verifyStackedOpeningNZ_refines (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    Refines (verifyStackedOpeningNZ stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  unfold verifyStackedOpeningNZ verifyStackedOpening
  simp only [verifyWhir_eq_target]
  repeat (first | exact verifyWhirNZ_refines _ _ _ _ | refines_step)

theorem deferredProgramNZ_refines (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    Refines (deferredProgramNZ c bytecode publicInput) (deferringVerifierProgram c bytecode publicInput) := by
  unfold deferredProgramNZ
  rw [deferredProgram_eq]
  refine Refines.bind ?_ fun _ ↦ Refines.refl _
  unfold verifyExecutionNZ verifyExecutionClaims
  repeat (first | exact verifyStackedOpeningNZ_refines _ _ _ | refines_step)

/-- **The zero-challenge refusal only restricts**: the deferring verifier refusing a zero challenge
accepts only proofs the Spec's deferring verifier accepts. -/
theorem verifyDeferred_of_nz {bytecode : List K} {iv publicInput : Digest} {c : BytecodeClaim}
    {π : Proof} (h : verifyDeferredNZ bytecode iv publicInput c π = true) :
    verifyDeferred bytecode iv publicInput c π = true := by
  unfold verifyDeferredNZ at h
  rw [verifyDeferred_eq_withHash]
  unfold verifyDeferredWithHash
  exact runProof_refines (deferredProgramNZ_refines c bytecode publicInput) _ π h

end
end LeanVM.Guest.Limits
