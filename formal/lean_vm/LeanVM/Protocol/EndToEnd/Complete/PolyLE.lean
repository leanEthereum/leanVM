/-
  LeanVM.Protocol.EndToEnd.Complete.PolyLE

  Polynomial functions of bounded degree, coefficient lists' values, and a sumcheck round's check
  as its mode reads it: what the soundness of the Keccak reduction reads of the sumcheck rounds.
-/

module

public import Statement.Verifier.Lib
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Polynomial functions and a round's check

The part of the archived `EndToEnd/Complete/Sumcheck.lean` (tag `formal-bus-archive`) that the
soundness proofs read: `PolyLE d f` (a polynomial function of degree at most `d`, closed under
sums and products), `polyEval` at `0`, at `1` and as a sum, and `RoundSplit`, the check of a
sumcheck round as its mode reads it. The honest prover's rounds (`coeffsOf`, `wire`, `hSumcheck`)
are the completeness side's.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Polynomial

@[expose] public section

/-! ## Polynomial functions of bounded degree -/

/-- `f` is a polynomial function of degree at most `d`. -/
def PolyLE (d : ℕ) (f : E → E) : Prop :=
  ∃ P : E[X], P.natDegree ≤ d ∧ ∀ x, f x = P.eval x

namespace PolyLE

variable {d d' : ℕ} {f g : E → E}

/-- A constant is a polynomial of every degree. -/
theorem const (d : ℕ) (a : E) : PolyLE d fun _ ↦ a :=
  ⟨C a, by simp, fun x ↦ by simp⟩

/-- The identity has degree one. -/
theorem id : PolyLE 1 fun x ↦ x :=
  ⟨X, natDegree_X_le, fun x ↦ by simp⟩

/-- An affine function has degree one. -/
theorem affine (a b : E) : PolyLE 1 fun x ↦ a + b * x :=
  ⟨C a + C b * X, natDegree_add_le_of_degree_le (by simp)
    ((natDegree_C_mul_le _ _).trans natDegree_X_le), fun x ↦ by simp⟩

/-- A larger degree bound. -/
theorem mono (h : PolyLE d f) (hd : d ≤ d') : PolyLE d' f := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP.trans hd, hf⟩

/-- A function equal to a polynomial function is one. -/
theorem congr (h : PolyLE d f) (hfg : ∀ x, f x = g x) : PolyLE d g := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP, fun x ↦ (hfg x).symm.trans (hf x)⟩

/-- Sums. -/
theorem add (hf : PolyLE d f) (hg : PolyLE d g) : PolyLE d fun x ↦ f x + g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P + Q, natDegree_add_le_of_degree_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- Products add degrees. -/
theorem mul (hf : PolyLE d f) (hg : PolyLE d' g) : PolyLE (d + d') fun x ↦ f x * g x := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hgQ⟩ := hg
  exact ⟨P * Q, natDegree_mul_le_of_le hP hQ, fun x ↦ by simp [hfP, hgQ]⟩

/-- A constant multiple. -/
theorem const_mul (hf : PolyLE d f) (a : E) : PolyLE d fun x ↦ a * f x :=
  ((mul (const 0 a) hf).mono (by omega)).congr fun _ ↦ rfl

/-- Finite sums. -/
theorem sum {ι : Type} (s : Finset ι) {F : ι → E → E} (h : ∀ i ∈ s, PolyLE d (F i)) :
    PolyLE d fun x ↦ ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const d 0).congr fun x ↦ by simp
  | insert a s ha ih =>
    refine (add (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi]))).congr fun x ↦ ?_
    rw [Finset.sum_insert ha]

end PolyLE

/-! ## Coefficient lists -/

/-- `polyEval` is the sum of the coefficients times the powers. -/
theorem polyEval_eq_sum : ∀ (l : List E) (x : E),
    polyEval l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i
  | [], x => by simp [polyEval]
  | c :: l, x => by
    have h : polyEval (c :: l) x = polyEval l x * x + c := rfl
    rw [h, polyEval_eq_sum l x, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ ↦ by
        rw [List.getD_cons_succ, pow_succ]; ring
    · rw [List.getD_cons_zero, pow_zero, mul_one]

/-- The value of a coefficient list at `0` is its first coefficient. -/
theorem polyEval_zero_cons (c : E) (l : List E) : polyEval (c :: l) 0 = c := by
  show polyEval l 0 * 0 + c = c
  simp

/-- The value of a coefficient list at `1` is the sum of its coefficients. -/
theorem polyEval_one : ∀ l : List E, polyEval l 1 = l.sum
  | [] => rfl
  | c :: l => by
    show polyEval l 1 * 1 + c = _
    rw [mul_one, polyEval_one l, List.sum_cons, add_comm]

/-! ## One round on the wire -/

/-- The round's check, as the mode reads it: `c(0) + c(1) = claim` in plain mode,
`(1 + r)·c(0) + r·c(1) = claim` in equality mode. -/
def RoundSplit (mode : Option E) (claim v0 v1 : E) : Prop :=
  match mode with
  | none => v0 + v1 = claim
  | some r => (1 + r) * v0 + r * v1 = claim

end
end LeanVM.Protocol.EndToEnd.Complete
