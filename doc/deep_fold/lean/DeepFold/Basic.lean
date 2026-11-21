/-
The DEEP fold lemma, algebraic heart (single lane, one point): the polynomial `Δ` of
Definition 4.5 of the paper and Lemma 4.6(c).

The paper works in characteristic two, where the determinant below is its
`Δ = (a₂ + a₃) P₁ + (a₁ + a₃) P₂ + (a₁ + a₂) P₃`. Everything here is proved over an arbitrary
field, with the signs of the determinant; `Delta_char_two` gives the paper's form.
-/
import Mathlib

open Polynomial

namespace DeepFold

variable {K : Type*} [Field K]

/-- The affine combiner `a_c(X) = α + β X` of a challenge `c = (α, β)`. -/
noncomputable def aff (c : K × K) : K[X] := C c.1 + C c.2 * X

@[simp] theorem aff_eval (c : K × K) (z : K) : (aff c).eval z = c.1 + c.2 * z := by
  simp [aff]

theorem aff_natDegree_le (c : K × K) : (aff c).natDegree ≤ 1 := by
  unfold aff
  compute_degree

theorem aff_sub (c c' : K × K) : aff c - aff c' = C (c.1 - c'.1) + C (c.2 - c'.2) * X := by
  simp only [aff, C_sub]
  ring

theorem aff_injective : Function.Injective (aff : K × K → K[X]) := by
  intro c c' h
  have h0 := congrArg (eval 0) h
  have h1 := congrArg (eval 1) h
  simp only [aff_eval, mul_zero, add_zero, mul_one] at h0 h1
  refine Prod.ext h0 ?_
  rw [h0] at h1
  exact add_left_cancel h1

/-- A candidate: a challenge `c = (α, β)` and a polynomial `P` (a codeword close to the fold
`f₁ + a_c f₀`; closeness is not used in this file). -/
abbrev Cand (K : Type*) [Field K] := (K × K) × K[X]

/-- `(c, P)` is consistent with the answer `(a, b)` at the point `z`: `P(z) = b + (α + β z) a`.
In the paper `a = y^F` and `b = y^G`. -/
def Cons (e : Cand K) (z a b : K) : Prop := e.2.eval z = b + (e.1.1 + e.1.2 * z) * a

/-- The determinant polynomial of three candidates, expanded along its first column. -/
noncomputable def Delta (e₁ e₂ e₃ : Cand K) : K[X] :=
  e₁.2 * (aff e₃.1 - aff e₂.1) + e₂.2 * (aff e₁.1 - aff e₃.1) + e₃.2 * (aff e₂.1 - aff e₁.1)

/-- `Delta` is the 3 by 3 determinant with rows `(P_i, 1, α_i + β_i X)`. -/
theorem Delta_eq_det (e₁ e₂ e₃ : Cand K) :
    Delta e₁ e₂ e₃ =
      Matrix.det !![e₁.2, 1, aff e₁.1; e₂.2, 1, aff e₂.1; e₃.2, 1, aff e₃.1] := by
  rw [Matrix.det_fin_three]
  simp [Delta]
  ring

/-- In characteristic two `Delta` is the `Δ` of Definition 4.5 of the paper. -/
theorem Delta_char_two [CharP K 2] (e₁ e₂ e₃ : Cand K) :
    Delta e₁ e₂ e₃ =
      (aff e₂.1 + aff e₃.1) * e₁.2 + (aff e₁.1 + aff e₃.1) * e₂.2 + (aff e₁.1 + aff e₂.1) * e₃.2 := by
  simp only [Delta, CharTwo.sub_eq_add]
  ring

/-- Lemma 4.6(c) of the paper: three candidates consistent with one answer at `z` have
`Delta(z) = 0`. No hypothesis on the challenges. -/
theorem Delta_eval_eq_zero {e₁ e₂ e₃ : Cand K} {z a b : K}
    (h₁ : Cons e₁ z a b) (h₂ : Cons e₂ z a b) (h₃ : Cons e₃ z a b) :
    (Delta e₁ e₂ e₃).eval z = 0 := by
  unfold Cons at h₁ h₂ h₃
  simp only [Delta, eval_add, eval_mul, eval_sub, aff_eval, h₁, h₂, h₃]
  ring

/-- `Delta` has degree at most `d + 1` when the three polynomials have degree at most `d`. -/
theorem Delta_natDegree_le {e₁ e₂ e₃ : Cand K} {d : ℕ}
    (h₁ : e₁.2.natDegree ≤ d) (h₂ : e₂.2.natDegree ≤ d) (h₃ : e₃.2.natDegree ≤ d) :
    (Delta e₁ e₂ e₃).natDegree ≤ d + 1 := by
  have haff : ∀ c c' : K × K, (aff c - aff c').natDegree ≤ 1 := fun c c' =>
    natDegree_sub_le_of_le (aff_natDegree_le c) (aff_natDegree_le c')
  unfold Delta
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · exact natDegree_mul_le_of_le h₁ (haff _ _)
  · exact natDegree_mul_le_of_le h₂ (haff _ _)
  · exact natDegree_mul_le_of_le h₃ (haff _ _)

/-- `Delta` is unchanged by a cyclic rotation of its arguments. -/
theorem Delta_rotate (e₁ e₂ e₃ : Cand K) : Delta e₂ e₃ e₁ = Delta e₁ e₂ e₃ := by
  unfold Delta
  ring

/-- `Delta` changes sign under a swap of its first two arguments. -/
theorem Delta_swap (e₁ e₂ e₃ : Cand K) : Delta e₂ e₁ e₃ = -Delta e₁ e₂ e₃ := by
  unfold Delta
  ring

end DeepFold
