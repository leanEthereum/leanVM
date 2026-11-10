/-
  LeanVM.Guest.Child.Combiner

  The statement's verifier refusing a zero where the guest divides (`verifierRefusingZero`,
  `Statement/LeanVmGuestCompleteness.lean`) refines the leanVM verifier: it is the verifier with
  failures inserted, so what it accepts the verifier accepts, by the same run.
-/

module

public import LeanVM.Guest.LimitsNZ
public import Statement.LeanVmGuestCompleteness

/-!
# The refusing verifier refines the verifier

`whirLevelsRefusingZeroCombiner` is `whirLevels` with one `require` after each level's queries,
and the three programs above it differ from theirs only in the callee: each refines its original
(`Limits.Refines`, failures inserted step for step; `whirLevelsRefusingZeroCombiner_refines` up to
`verifyExecutionRefusingZeroCombiner_refines`), and so does refusing every zero challenge
(`refines_refusingZeroChallenge`). So the statement's refusing verifier accepts only proofs the
leanVM verifier accepts, by the same run (`Limits.run_refines`): `leanVmVerifier_of_refusingZero`.
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Completeness

@[expose] public section

variable {α : Type}

/-- Refinement is transitive. -/
theorem Refines.trans {P'' P' P : VerifierProgram α} (h1 : Refines P'' P') (h2 : Refines P' P) :
    Refines P'' P := by
  induction h1 generalizing P with
  | fail _ => exact .fail _
  | ret a => exact h2
  | read _ ih => cases h2 with
    | read h => exact .read fun x ↦ ih x (h x)
  | sample _ ih => cases h2 with
    | sample h => exact .sample fun x ↦ ih x (h x)
  | grind _ ih => cases h2 with
    | grind h => exact .grind (ih h)
  | commit _ ih => cases h2 with
    | commit h => exact .commit (ih h)
  | query _ ih => cases h2 with
    | query h => exact .query fun r ↦ ih r (h r)

/-- **Refusing every zero challenge only inserts failures.** -/
theorem refines_refusingZeroChallenge : ∀ P : VerifierProgram α,
    Refines P.refusingZeroChallenge P
  | .ret a => .ret a
  | .fail => .fail _
  | .read k => .read fun x ↦ refines_refusingZeroChallenge (k x)
  | .sample k => .sample fun c ↦ by
      show Refines (if c = 0 then VerifierProgram.fail else (k c).refusingZeroChallenge) (k c)
      split
      · exact .fail _
      · exact refines_refusingZeroChallenge (k c)
  | .grind _ k => .grind (refines_refusingZeroChallenge k)
  | .commit _ _ k => .commit (refines_refusingZeroChallenge k)
  | .query _ _ k => .query fun r ↦ refines_refusingZeroChallenge (k r)

/-- One step of a refinement proof between two programs written alike. -/
local macro "refines_step" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | (refine Refines.bind ?h fun _ ↦ ?k; case h => with_reducible exact Refines.refl _)
  | apply Refines.require_bind
  | split
  | dsimp only
  | exact Refines.refl _)

theorem whirLevelsRefusingZeroCombiner_refines (logN laneFolds : ℕ) (eb : List E → E)
    (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirState),
      Refines (whirLevelsRefusingZeroCombiner logN laneFolds eb index levels s)
        (whirLevels logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact Refines.refl _
  | cons level rest ih =>
    intro index s
    unfold whirLevelsRefusingZeroCombiner whirLevels
    apply Refines.bind (Refines.refl _)
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

theorem verifyWhirRefusingZeroCombiner_refines (logN logInvRate : ℕ) (target : E)
    (eb : List E → E) :
    Refines (verifyWhirRefusingZeroCombiner logN logInvRate target eb)
      (verifyWhir logN logInvRate target eb) := by
  unfold verifyWhirRefusingZeroCombiner verifyWhir
  repeat (first | exact whirLevelsRefusingZeroCombiner_refines _ _ _ _ _ _ | refines_step)

theorem verifyStackedOpeningRefusingZeroCombiner_refines (stackLog logInvRate : ℕ)
    (claims : List StackClaim) :
    Refines (verifyStackedOpeningRefusingZeroCombiner stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  unfold verifyStackedOpeningRefusingZeroCombiner verifyStackedOpening
  repeat (first | exact verifyWhirRefusingZeroCombiner_refines _ _ _ _ | refines_step)

theorem verifyExecutionRefusingZeroCombiner_refines
    (bv : List K → List E → E → VerifierProgram Unit) (bytecode : List K) (publicInput : Digest) :
    Refines (verifyExecutionRefusingZeroCombiner bv bytecode publicInput)
      (verifyExecution bv bytecode publicInput) := by
  unfold verifyExecutionRefusingZeroCombiner verifyExecution
  repeat (first | exact verifyStackedOpeningRefusingZeroCombiner_refines _ _ _ | refines_step)

/-- The program `verifierRefusingZero` runs. -/
def refusingZeroProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool :=
  (do
    verifyExecutionRefusingZeroCombiner computedBytecodeValue bytecode publicInput
    return true : VerifierProgram Bool).refusingZeroChallenge

/-- **The refusing program refines the leanVM verifier program.** -/
theorem refusingZeroProgram_refines (bytecode : List K) (publicInput : Digest) :
    Refines (refusingZeroProgram bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) :=
  (refines_refusingZeroChallenge _).trans
    (Refines.bind (verifyExecutionRefusingZeroCombiner_refines _ _ _) fun _ ↦ Refines.refl _)

/-- The refusing program reads first. -/
theorem refusingZeroProgram_read (bytecode : List K) (publicInput : Digest) :
    ∃ k, refusingZeroProgram bytecode publicInput = VerifierProgram.read k :=
  ⟨_, rfl⟩

/-- **What the statement's refusing verifier accepts, the leanVM verifier accepts**, by the same
run (`run_refines`): over any permutation, the seed being the same. -/
theorem leanVmVerifier_of_refusingZero {π : KeccakState → Id KeccakState}
    {program : LeanIsaProgram} {input : PublicInput} {proof : Proof}
    (h : verifierRefusingZero (m := Id) π program input proof = true) :
    leanVmVerifier (m := Id) π program input proof = true := by
  unfold verifierRefusingZero at h
  unfold leanVmVerifier verifyWith
  simp only [bind] at h ⊢
  rw [runProof_eq_withHash] at h ⊢
  exact runProof_refines (refusingZeroProgram_refines _ _) _ proof h

end
end LeanVM.Guest.Limits
