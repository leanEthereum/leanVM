/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerTrivariate

  `L[X, Y, Z]` as nested polynomials `L[X][Y][Z]`: the algebra equivalence, its coefficients,
  evaluation along a line, and the `Z`-derivative. Candidate for ArkLib.
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic

/-!
# Trivariate polynomials as nested polynomials

`trivEquiv L : MvPolynomial (Fin 3) L ≃ₐ[L] L[X][Y][Z]` sends the variables `0, 1, 2` (`X, Y, Z`)
to `C (C X)`, `C X` and `X`: `Z` is the outer variable, `Y` the middle one, `X` the inner one.

* `coeff_trivEquiv`: `((Q.coeff m₂).coeff m₁).coeff m₀ = coeff m Q`;
* `trivEval x y z`: substituting `x, y, z ∈ L[X]`, and `trivEval_trivEquiv`:
  `trivEval x y z (trivEquiv Q) = Q(x, y, z)`;
* `trivEquiv_pderiv`: the `Z`-derivative is the outer derivative.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Polynomial

@[expose] public section

variable (L : Type*) [Field L]

/-- `L[X]` as `MvPolynomial (Fin 1) L`. -/
noncomputable def triv1 : MvPolynomial (Fin 1) L ≃ₐ[L] L[X] :=
  (MvPolynomial.finSuccEquiv L 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv L (Fin 0)))

/-- `L[Y, X]` (variables `0, 1`) as `L[X][Y]`. -/
noncomputable def triv2 : MvPolynomial (Fin 2) L ≃ₐ[L] L[X][X] :=
  (MvPolynomial.finSuccEquiv L 1).trans (Polynomial.mapAlgEquiv (triv1 L))

/-- **`L[X, Y, Z]` as `L[X][Y][Z]`.** -/
noncomputable def trivEquiv : MvPolynomial (Fin 3) L ≃ₐ[L] L[X][X][X] :=
  (MvPolynomial.renameEquiv L (Equiv.swap 0 2)).trans
    ((MvPolynomial.finSuccEquiv L 2).trans (Polynomial.mapAlgEquiv (triv2 L)))

variable {L}

@[simp] theorem triv1_X : triv1 L (MvPolynomial.X 0) = X := by
  rw [triv1, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero, coe_mapAlgEquiv, map_X]

@[simp] theorem trivEquiv_X_two : trivEquiv L (MvPolynomial.X 2) = X := by
  rw [trivEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.swap_apply_right, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero,
    coe_mapAlgEquiv, map_X]

@[simp] theorem triv2_X_zero : triv2 L (MvPolynomial.X 0) = X := by
  rw [triv2, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero, coe_mapAlgEquiv, map_X]

@[simp] theorem triv2_X_one : triv2 L (MvPolynomial.X 1) = C X := by
  rw [triv2, AlgEquiv.trans_apply, show (1 : Fin 2) = Fin.succ 0 from rfl,
    MvPolynomial.finSuccEquiv_X_succ, coe_mapAlgEquiv, map_C]
  exact congrArg C triv1_X

@[simp] theorem trivEquiv_X_one : trivEquiv L (MvPolynomial.X 1) = C X := by
  have h : (Equiv.swap (0 : Fin 3) 2) 1 = Fin.succ 0 := by decide
  rw [trivEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h,
    AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_succ, coe_mapAlgEquiv, map_C]
  exact congrArg C triv2_X_zero

@[simp] theorem trivEquiv_X_zero : trivEquiv L (MvPolynomial.X 0) = C (C X) := by
  have h : (Equiv.swap (0 : Fin 3) 2) 0 = Fin.succ 1 := by decide
  rw [trivEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h,
    AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_succ, coe_mapAlgEquiv, map_C]
  exact congrArg C triv2_X_one

@[simp] theorem trivEquiv_C (c : L) : trivEquiv L (MvPolynomial.C c) = C (C (C c)) := by
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl

/-- The image of a monomial. -/
theorem trivEquiv_monomial (m : Fin 3 →₀ ℕ) (c : L) :
    trivEquiv L (MvPolynomial.monomial m c) =
      C (C (C c * X ^ m 0) * X ^ m 1) * X ^ m 2 := by
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    Fin.prod_univ_three, map_mul, map_mul, map_pow, map_pow, map_pow, trivEquiv_C,
    trivEquiv_X_zero, trivEquiv_X_one, trivEquiv_X_two]
  simp only [C_mul, C_pow]
  ring

/-- **The coefficients of the nested form.** -/
theorem coeff_trivEquiv (Q : MvPolynomial (Fin 3) L) (m : Fin 3 →₀ ℕ) :
    (((trivEquiv L Q).coeff (m 2)).coeff (m 1)).coeff (m 0) = Q.coeff m := by
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [trivEquiv_monomial, MvPolynomial.coeff_monomial, coeff_C_mul_X_pow,
      apply_ite (fun p : L[X][X] ↦ p.coeff (m 1)), coeff_C_mul_X_pow, coeff_zero,
      apply_ite (fun p : L[X] ↦ p.coeff (m 0)), apply_ite (fun p : L[X] ↦ p.coeff (m 0)),
      coeff_C_mul_X_pow]
    have hiff : n = m ↔ (m 2 = n 2 ∧ m 1 = n 1 ∧ m 0 = n 0) :=
      ⟨fun h ↦ by subst h; simp, fun ⟨a, b, c⟩ ↦ by ext i; fin_cases i <;> simp [a, b, c]⟩
    by_cases h : n = m
    · obtain ⟨a, b, c'⟩ := hiff.mp h
      simp [a, b, c', h]
    · have := mt hiff.mpr h
      split_ifs <;> simp_all
  | add p q hp hq => simp [coeff_add, hp, hq]

/-- Substituting `x, y, z ∈ L[X]` for the inner, middle and outer variables. -/
noncomputable def trivEval (x y z : L[X]) : L[X][X][X] →+* L[X] :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom C x) y) z

/-- **Evaluation through the nested form**: `trivEval x y z (trivEquiv Q) = Q(x, y, z)`. -/
theorem trivEval_trivEquiv (x y z : L[X]) (Q : MvPolynomial (Fin 3) L) :
    trivEval x y z (trivEquiv L Q) = MvPolynomial.aeval ![x, y, z] Q := by
  have : (trivEval x y z).comp (trivEquiv L).toRingHom =
      (MvPolynomial.aeval (R := L) ![x, y, z]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [trivEval]
    · fin_cases i <;> simp [trivEval]
  exact congrArg (fun φ : MvPolynomial (Fin 3) L →+* L[X] ↦ φ Q) this

/-- **The `Z`-derivative** is the outer derivative of the nested form. -/
theorem trivEquiv_pderiv (Q : MvPolynomial (Fin 3) L) :
    trivEquiv L (MvPolynomial.pderiv 2 Q) = derivative (trivEquiv L Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul,
      derivative_mul]
    fin_cases i <;> simp [MvPolynomial.pderiv_X] <;> ring

end

end LeanVM.Protocol.Whir.AffineCombiner
