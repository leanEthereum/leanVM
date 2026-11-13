/-
  LeanVM.Guest.Child.NZRun

  The guest's refusing programs (`Limits.verifyExecutionNZ`) are the verifier's programs
  (`verifyExecution`) with, after some challenges, a check that the challenge is not zero.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Phases
public import LeanVM.Guest.Child.Fresh
public import LeanVM.Protocol.WithHash

/-!
# Refusing a zero challenge

`NZ p' p`: `p'` is `p` with, after some challenges, a check that the challenge is not zero; at a
nonzero challenge the two continue alike. The guest's program refusing a zero fold, tail or level
batching challenge is such a `p'` of the verifier's program (`nz_verifyExecution`,
`nz_deferredProgram`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Guest.Completeness

@[expose] public section

/-- **`p'` is `p` refusing zero challenges**: step for step, the continuations after a nonzero
challenge related. -/
inductive NZ {α : Type} : VerifierProgram α → VerifierProgram α → Prop
  | ret (a : α) : NZ (.ret a) (.ret a)
  | fail : NZ .fail .fail
  | read {k k' : E → VerifierProgram α} : (∀ x, NZ (k' x) (k x)) → NZ (.read k') (.read k)
  | sample {k k' : E → VerifierProgram α} : (∀ c, c ≠ 0 → NZ (k' c) (k c)) → NZ (.sample k')
      (.sample k)
  | grind {b : ℕ} {k k' : VerifierProgram α} : NZ k' k → NZ (.grind b k') (.grind b k)
  | commit {h w : ℕ} {k k' : VerifierProgram α} : NZ k' k → NZ (.commit h w k') (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k k' : List (List K) → VerifierProgram α} :
      (∀ r, NZ (k' r) (k r)) → NZ (.query i ps k') (.query i ps k)

namespace NZ

variable {α β : Type}

theorem refl : ∀ p : VerifierProgram α, NZ p p
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ refl (k x)
  | .sample k => .sample fun c _ ↦ refl (k c)
  | .grind _ k => .grind (refl k)
  | .commit _ _ k => .commit (refl k)
  | .query _ _ k => .query fun r ↦ refl (k r)

theorem bind {p' p : VerifierProgram α} (h : NZ p' p) {f' f : α → VerifierProgram β} (hf : ∀ a, NZ
    (f' a) (f a)) :
    NZ (p'.bind f') (p.bind f) := by
  induction h with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- A challenge, then programs related at every nonzero challenge. -/
theorem sample_bind {f' f : E → VerifierProgram β} (hf : ∀ c, c ≠ 0 → NZ (f' c) (f c)) :
    NZ (VerifierProgram.sampleChallenge.bind f') (VerifierProgram.sampleChallenge.bind f) :=
  .sample hf

/-- A check that holds, then related programs. -/
theorem require_bind_of {c : Prop} [Decidable c] (hc : c) {k' k : VerifierProgram α} (h : NZ k' k) :
    NZ ((VerifierProgram.require c).bind fun _ ↦ k') k := by
  unfold VerifierProgram.require
  simp only [hc, ↓reduceIte]
  exact h

end NZ

/-! ## The programs -/

theorem nz_foldRound (s : WhirState) : NZ (Limits.foldRoundNZ s) (foldRound s) := by
  unfold Limits.foldRoundNZ foldRound
  iterate 5 refine NZ.bind (NZ.refl _) fun _ ↦ ?_
  refine NZ.sample_bind fun c hc ↦ ?_
  exact NZ.require_bind_of hc (NZ.refl _)

theorem nz_foldRounds : ∀ (n : ℕ) (s : WhirState),
    NZ (Limits.foldRoundsNZ n s) (foldRounds n s)
  | 0, s => NZ.refl _
  | n + 1, s => by
    unfold Limits.foldRoundsNZ foldRounds
    exact NZ.bind (nz_foldRound s) fun _ ↦ NZ.bind (nz_foldRounds n _) fun _ ↦ NZ.refl _

theorem nz_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    NZ (Limits.sumcheckNZ claim count eqs) (sumcheck claim count eqs)
  | [], claim => NZ.refl _
  | e :: eqs, claim => by
    unfold Limits.sumcheckNZ sumcheck
    refine NZ.bind (NZ.refl _) fun m ↦ ?_
    refine NZ.sample_bind fun c hc ↦ ?_
    exact NZ.require_bind_of hc (NZ.bind (nz_sumcheck count eqs _) fun _ ↦ NZ.refl _)

/-- The first program of a bind: the same, or one refusing zero challenges. -/
local macro "nz_head" : tactic => `(tactic| first
  | with_reducible exact NZ.refl _
  | exact nz_foldRounds _ _
  | exact nz_sumcheck _ _ _)

/-- One step between two programs written alike. -/
local macro "nz_step" : tactic => `(tactic| first
  | with_reducible exact NZ.refl _
  | (refine NZ.sample_bind fun _ hc ↦ NZ.require_bind_of hc ?_)
  | (refine NZ.bind ?h fun _ ↦ ?k; case h => nz_head)
  | split
  | dsimp only)

theorem nz_whirLevels (logN laneFolds : ℕ) (eb : List E → E) (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirState),
      NZ (Limits.whirLevelsNZ logN laneFolds eb index levels s)
        (whirLevels logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact NZ.refl _
  | cons level rest ih =>
    intro index s
    unfold Limits.whirLevelsNZ whirLevels
    apply NZ.bind (nz_foldRounds _ _)
    intro p
    obtain ⟨s', lf⟩ := p
    dsimp only
    cases rest with
    | nil =>
      dsimp only
      repeat nz_step
    | cons next rest' =>
      dsimp only
      repeat (first | exact ih _ _ | nz_step)

theorem nz_verifyWhir (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    NZ (Limits.verifyWhirNZ logN logInvRate target eb)
      (verifyWhir logN logInvRate target eb) := by
  unfold Limits.verifyWhirNZ verifyWhir
  repeat (first | exact nz_whirLevels _ _ _ _ _ _ | nz_step)

theorem nz_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    NZ (Limits.verifyStackedOpeningNZ stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  rw [verifyStackedOpening_nf]
  unfold Limits.verifyStackedOpeningNZ
  repeat (first | exact nz_verifyWhir _ _ _ _ | nz_step)

/-- **The guest's refusing verifier refuses zero challenges of the verifier.** -/
theorem nz_verifyExecution (bv : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) :
    NZ (Limits.verifyExecutionNZ bv bytecode publicInput)
      (verifyExecution bv bytecode publicInput) := by
  unfold Limits.verifyExecutionNZ verifyExecution
  repeat (first | with_reducible exact nz_verifyStackedOpening _ _ _ | nz_step)

theorem nz_deferredProgram (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    NZ (Limits.deferredProgramNZ c bytecode publicInput)
      (deferringVerifierProgram c bytecode publicInput) :=
  NZ.bind (nz_verifyExecution _ _ _) fun _ ↦ NZ.refl _

end
end LeanVM.Guest.Child
