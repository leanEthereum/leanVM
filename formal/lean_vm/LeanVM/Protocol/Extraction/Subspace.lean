module

public import LeanVM.Protocol.Extraction.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination

/-!
# The subspace polynomials of the statement (proofs)

For the statement's `subspacePoly i a = W_i(a) = ∏_{v<2^i} (a + x_v)` and
`normSubspacePoly i a = Ŵ_i(a) = W_i(a)/W_i(x^i)`:

* `subspacePoly_add`: `W_i` is additive (Lemma `lem:subspace` (ii) of leanVM's Annex D), from the
  polynomial identities `W_i(X + a) = W_i(X) + W_i(a)` and `W_{i+1} = W_i·(W_i + W_i(x^i))`,
  proved jointly by induction;
* `subspacePoly_basis_ne_zero`: `W_i(x^i) ≠ 0` for `i < 64`, so `Ŵ_i(x^i) = 1`;
* `normSubspacePoly_of_lt`: `Ŵ_i` vanishes on `U_i = {x_v | v < 2^i}`.

Adapted from leanerVM `lean_vm/LeanVM/Protocol/Whir/Subspace.lean` (branch `mumbai`, `935b9d40`),
restated for the statement's `subspacePoly`/`normSubspacePoly`.
-/

namespace LeanVM.Extraction.Subspace

open LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Words Polynomial

public section

attribute [local simp] LeanVM.Extraction.Words.ofBits_zero

/-- `W_i(X) = ∏_{v<2^i} (X + x_v)` as a polynomial. -/
@[expose] noncomputable def vanishing (i : ℕ) : K[X] := ∏ v ∈ Finset.range (2 ^ i), (X + C (K.ofBits v))

@[simp] theorem eval_vanishing (i : ℕ) (a : K) : (vanishing i).eval a = subspacePoly i a := by
  simp [vanishing, subspacePoly, eval_prod]

theorem vanishing_zero : vanishing 0 = X := by simp [vanishing]

private theorem vanishing_succ_split (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i).comp (X + C (K.ofBits (2 ^ i))) := by
  rw [vanishing, pow_succ, mul_two, Finset.prod_range_add, vanishing, prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  rw [ofBits_two_pow_add (Finset.mem_range.mp hv)]
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

private theorem char_two_cross (A B c : K[X]) :
    (A + B) * (A + B + c) = A * (A + c) + B * (B + c) := by
  linear_combination (A * B) * (CharTwo.two_eq_zero : (2 : K[X]) = 0)

private theorem vanishing_comp_add_and_succ (i : ℕ) :
    (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (subspacePoly i a)) ∧
      vanishing (i + 1) =
        vanishing i * (vanishing i + C (subspacePoly i (K.ofBits (2 ^ i)))) := by
  have step : ∀ i, (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (subspacePoly i a)) →
      vanishing (i + 1) = vanishing i * (vanishing i + C (subspacePoly i (K.ofBits (2 ^ i)))) := by
    intro i h
    rw [vanishing_succ_split, h]
  induction i with
  | zero =>
    refine ⟨fun a ↦ ?_, step 0 fun a ↦ ?_⟩ <;>
    · simp [vanishing_zero, subspacePoly]
  | succ i ih =>
    have hadd : ∀ a : K,
        (vanishing (i + 1)).comp (X + C a) = vanishing (i + 1) + C (subspacePoly (i + 1) a) := by
      intro a
      rw [← eval_vanishing (i + 1) a, ih.2, mul_comp, add_comp, C_comp, ih.1 a, eval_mul,
        eval_add, eval_C, eval_vanishing, C_mul, C_add]
      exact char_two_cross _ _ _
    exact ⟨hadd, step _ hadd⟩

/-- `W_i` is additive. -/
theorem subspacePoly_add (i : ℕ) (a b : K) :
    subspacePoly i (a + b) = subspacePoly i a + subspacePoly i b := by
  have h := congrArg (eval a) ((vanishing_comp_add_and_succ i).1 b)
  rw [eval_comp, eval_add, eval_X, eval_C, eval_add, eval_C, eval_vanishing,
    eval_vanishing] at h
  exact h

/-- `W_i(x^i) ≠ 0` for `i < 64`. -/
theorem subspacePoly_basis_ne_zero {i : ℕ} (hi : i < 64) :
    subspacePoly i (K.ofBits (2 ^ i)) ≠ 0 := by
  rw [subspacePoly]
  refine Finset.prod_ne_zero_iff.mpr fun v hv ↦ ?_
  have hv' := Finset.mem_range.mp hv
  rw [← ofBits_two_pow_add hv']
  have hlt : 2 ^ i + v < 2 ^ 64 := by
    have : 2 ^ (i + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ] at this
    omega
  rw [Ne, ofBits_eq_zero_iff hlt]
  have := Nat.two_pow_pos i
  omega

/-- `Ŵ_i` is additive. -/
theorem normSubspacePoly_add (i : ℕ) (a b : K) :
    normSubspacePoly i (a + b) = normSubspacePoly i a + normSubspacePoly i b := by
  rw [normSubspacePoly, normSubspacePoly, normSubspacePoly, subspacePoly_add, add_mul]

/-- `Ŵ_i(x^i) = 1` for `i < 64`. -/
theorem normSubspacePoly_basis {i : ℕ} (hi : i < 64) : normSubspacePoly i (K.ofBits (2 ^ i)) = 1 :=
  mul_inv_cancel₀ (subspacePoly_basis_ne_zero hi)

/-- `Ŵ_i` vanishes on `U_i`. -/
theorem normSubspacePoly_of_lt {i v : ℕ} (hv : v < 2 ^ i) : normSubspacePoly i (K.ofBits v) = 0 := by
  rw [normSubspacePoly, subspacePoly, Finset.prod_eq_zero (Finset.mem_range.mpr hv)
    (CharTwo.add_self_eq_zero (K.ofBits v)), zero_mul]

/-- `Ŵ_i(a + x^i) = Ŵ_i(a) + 1` for `i < 64`. -/
theorem normSubspacePoly_add_basis {i : ℕ} (hi : i < 64) (a : K) :
    normSubspacePoly i (a + K.ofBits (2 ^ i)) = normSubspacePoly i a + 1 := by
  rw [normSubspacePoly_add, normSubspacePoly_basis hi]

end
end LeanVM.Extraction.Subspace
