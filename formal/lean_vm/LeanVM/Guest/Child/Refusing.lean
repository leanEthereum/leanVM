/-
  LeanVM.Guest.Child.Refusing

  The statement's verifier refusing a zero challenge (`verifierRefusingZero`,
  `Statement/LeanVmGuestCompleteness.lean`) refines the leanVM verifier, and against a winning
  strategy it fails with probability at most `|E|⁻¹` per sample.
-/

module

public import LeanVM.Guest.LimitsNZ
public import Statement.LeanVmGuestCompleteness
public import LeanVM.Protocol.Compile.Rom.IdealCalc
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Protocol.Compile.Cost

/-!
# The refusing verifier

Refusing every zero challenge only inserts failures (`refines_refusingZeroChallenge`), so the
statement's refusing verifier accepts only proofs the leanVM verifier accepts, by the same run
(`Limits.run_refines`): `leanVmVerifier_of_refusingZero`. Against challenges uniform and
independent it fails at most `|E|⁻¹` more often per sample than the verifier
(`failFrom_refusingZeroProgram_le`).
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Completeness

@[expose] public section

variable {α : Type}

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

/-- The program `verifierRefusingZero` runs. -/
def refusingZeroProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool :=
  (do
    verifyExecution computedBytecodeValue bytecode publicInput
    return true : VerifierProgram Bool).refusingZeroChallenge

/-- **The refusing program refines the leanVM verifier program.** -/
theorem refusingZeroProgram_refines (bytecode : List K) (publicInput : Digest) :
    Refines (refusingZeroProgram bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) :=
  refines_refusingZeroChallenge _

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

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.Completeness Strategy
open scoped ENNReal

@[expose] public section

variable {S : Strategy}

/-- A refining program costs at most what the refined one costs. -/
theorem costs_of_refines {α : Type} {height : ℕ} {P' P : VerifierProgram α}
    (h : Limits.Refines P' P) :
    ∀ {n : ℕ} {Q : α → Prop}, VerifierProgram.Costs height P n Q →
      VerifierProgram.Costs height P' n Q := by
  induction h with
  | fail P => intro n Q _; trivial
  | ret a => intro n Q hc; exact hc
  | read _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | sample _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | grind _ ih => intro n Q hc; exact ⟨hc.1, ih hc.2⟩
  | commit _ ih => intro n Q hc; exact ⟨hc.1, hc.2.1, ih hc.2.2⟩
  | query _ ih => intro n Q hc; exact ⟨hc.1, fun r ↦ ih r (hc.2 r)⟩

/-- **The statement's refusing verifier, against a winning strategy**, fails with probability at
most `|E|⁻¹` per sample (a quarter of the cost). -/
theorem failFrom_refusingZeroProgram_le {bytecode : List K} {publicInput : Digest} {height n : ℕ}
    (hacc : S.AcceptsFrom (leanVmVerifierProgram bytecode publicInput) [])
    (hgs : GrindThenSample (leanVmVerifierProgram bytecode publicInput))
    (hP : (leanVmVerifierProgram bytecode publicInput).CostLE height n) :
    S.failFrom (Limits.refusingZeroProgram bytecode publicInput) [] none ≤
      (n / 4 : ℕ) * epsE := by
  have h1 := failFrom_refusingZero_le (S := S) _ n hP [] none
  have h3 : S.failFrom (leanVmVerifierProgram bytecode publicInput) [] none = 0 :=
    failFrom_eq_zero _ _ _ hacc hgs (Or.inl rfl)
  unfold Limits.refusingZeroProgram
  refine h1.trans ?_
  simp only [h3, reduceCtorEq, ↓reduceIte, add_zero, zero_add, le_refl]

end
end LeanVM.Guest.Child
