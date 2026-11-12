/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerInterpolation

  [CYWZ26, preprint], Lemma 4.2: an interpolating polynomial `Q(X, Y, Z)` that vanishes along
  every affine line and candidate of high agreement. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerCore
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerParams
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Interpolation along affine lines

[CYWZ26, preprint], Lemma 4.2, with the interpolation inequality of Annex B, `def:epsaff` (ii).
Fix words `f g : ι → L` on the points `pt x`, integers `1 ≤ d`, `1 ≤ m`, `A`, `D`, and
`M = bigM d A m D`. If `equations n d A m D < unknowns d A m D`, there is a nonzero
`Q ∈ L[X, Y, Z]` (`MvPolynomial (Fin 3) L`, variables `0, 1, 2`) whose monomials `X^i Y^t Z^j`
have `t + j ≤ D`, `j ≤ M` and `i + t + d j < m A`, such that for every line `a + b X` and every `P`
of degree at most `d` agreeing with `f + (a + b x) g` on at least `A` points,
`Q(X, a + b X, P(X)) = 0` (`exists_interpolant`).

The unknowns are the coefficients `c_{i,t,j}`, `j ≤ M`, `i < m A - D - d j`, `t ≤ D - j`
(`idxSet`, of size `unknowns`). For a point `x` with values `f_x, g_x`, write
`Q(X, Y, Z) = Σ_{r, s} E_{x, r, s}(Y) (X - x)^r (Z - f_x - Y g_x)^s`; the constraints say that
`E_{x, r, s} = 0` for `r + s < m` (`eqSet`, `D - s + 1` coefficients each, `equations` in all,
since `deg E_{x, r, s} ≤ D - s` and `E_{x, r, s} = 0` for `s > M`). Then `(X - x)^m` divides
`Q(X, a + b X, P(X))` at every agreement point `x`, since `X - x` divides
`P - f_x - (a + b X) g_x` there (`dvd_evalSum_of_ePoly`), and a nonzero `Q(X, a + bX, P(X))` has
degree below `m A`.

The proof is univariate: `E_{x, r, s}` is written out (`ePoly`), and the identity above is the
binomial expansion of `X^i = ((X - x) + x)^i` and `P^j = ((P - w) + w)^j`
(`evalSum_eq_sum_ePoly`).
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {L : Type*} [Field L]

/-! ## Index sets -/

/-- The unknowns `(j, (i, t))`: `j ≤ M`, `i < m A - D - d j`, `t ≤ D - j`. -/
def idxSet (d A m D : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range (bigM d A m D + 1)).sigma fun j ↦ range (m * A - D - d * j) ×ˢ range (D - j + 1)

/-- The constraints `(s, (r, k))` at one point: `s ≤ min(m - 1, M)`, `r < m - s`, `k ≤ D - s`. -/
def eqSet (d A m D : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range (min (m - 1) (bigM d A m D) + 1)).sigma fun s ↦ range (m - s) ×ˢ range (D - s + 1)

theorem card_idxSet (d A m D : ℕ) : (idxSet d A m D).card = unknowns d A m D := by
  simp [idxSet, unknowns, card_sigma, card_product]

theorem card_eqSet (d A m D : ℕ) :
    (eqSet d A m D).card = ∑ s ∈ range (min (m - 1) (bigM d A m D) + 1), (m - s) * (D - s + 1) := by
  simp [eqSet, card_sigma, card_product]

theorem mem_idxSet {d A m D : ℕ} {e : Σ _ : ℕ, ℕ × ℕ} (he : e ∈ idxSet d A m D) :
    e.1 ≤ bigM d A m D ∧ e.2.1 + d * e.1 < m * A - D ∧ e.2.2 + e.1 ≤ D := by
  simp only [idxSet, mem_sigma, mem_range, mem_product] at he
  refine ⟨by omega, by omega, ?_⟩
  have : e.1 ≤ D := (Nat.lt_succ_iff.mp he.1).trans (min_le_left _ _)
  omega

/-! ## The polynomials `E_{x, r, s}` -/

/-- The term of the unknown `e = (j, (i, t))` in `E_{x, r, s}(Y)`:
`C(i, r) x^(i - r) C(j, s) Y^t (f_x + Y g_x)^(j - s)`. -/
noncomputable def eTerm (x fx gx : L) (s r : ℕ) (e : Σ _ : ℕ, ℕ × ℕ) : L[X] :=
  C ((e.2.1.choose r : L) * x ^ (e.2.1 - r) * (e.1.choose s : L)) * X ^ e.2.2 *
    (C fx + X * C gx) ^ (e.1 - s)

/-- `E_{x, r, s}(Y) = Σ_e c_e · eTerm`. -/
noncomputable def ePoly {d A m D : ℕ} (c : idxSet d A m D → L) (x fx gx : L) (s r : ℕ) : L[X] :=
  ∑ e : idxSet d A m D, C (c e) * eTerm x fx gx s r e

theorem natDegree_eTerm_le {d A m D : ℕ} (x fx gx : L) (s r : ℕ) {e : Σ _ : ℕ, ℕ × ℕ}
    (he : e ∈ idxSet d A m D) : (eTerm x fx gx s r e).natDegree ≤ D - s := by
  obtain ⟨-, -, hD⟩ := mem_idxSet he
  by_cases hs : s ≤ e.1
  · unfold eTerm
    refine (natDegree_mul_le).trans ?_
    have h1 : (C fx + X * C gx : L[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_mul_le).trans (by simp)))
    have h2 := (natDegree_pow_le (p := (C fx + X * C gx : L[X])) (n := e.1 - s)).trans
      (Nat.mul_le_mul_left _ h1)
    have h3 : (C ((e.2.1.choose r : L) * x ^ (e.2.1 - r) * (e.1.choose s : L)) *
        X ^ e.2.2 : L[X]).natDegree ≤ e.2.2 := (natDegree_C_mul_le _ _).trans (by simp)
    omega
  · have : (e.1.choose s : L) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp [eTerm, this]

theorem natDegree_ePoly_le {d A m D : ℕ} (c : idxSet d A m D → L) (x fx gx : L) (s r : ℕ) :
    (ePoly c x fx gx s r).natDegree ≤ D - s :=
  natDegree_sum_le_of_forall_le _ _ fun e _ ↦
    (natDegree_C_mul_le _ _).trans (natDegree_eTerm_le x fx gx s r e.2)

/-- `E_{x, r, s} = 0` when `s > M`: every unknown has `j ≤ M < s`. -/
theorem ePoly_eq_zero_of_lt {d A m D : ℕ} (c : idxSet d A m D → L) (x fx gx : L) {s : ℕ}
    (r : ℕ) (hs : bigM d A m D < s) : ePoly c x fx gx s r = 0 := by
  refine sum_eq_zero fun e _ ↦ ?_
  have : (e.1.1.choose s : L) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by have := (mem_idxSet e.2).1; omega), Nat.cast_zero]
  simp [eTerm, this]

/-! ## The binomial regrouping -/

/-- `Q(X, ℓ, P) = Σ_e c_e X^i ℓ^t P^j`. -/
noncomputable def evalSum {d A m D : ℕ} (c : idxSet d A m D → L) (ℓ P : L[X]) : L[X] :=
  ∑ e : idxSet d A m D, C (c e) * X ^ e.1.2.1 * ℓ ^ e.1.2.2 * P ^ e.1.1

/-- Extending a binomial sum `Σ_{r ≤ i}` to `Σ_{r < R}`, `i < R`. -/
private theorem add_pow_extend (a b : L[X]) (i R : ℕ) (hR : i < R) :
    (a + b) ^ i = ∑ r ∈ range R, a ^ r * b ^ (i - r) * (i.choose r : L[X]) := by
  rw [add_pow]
  refine sum_subset (fun r hr ↦ mem_range.mpr ((mem_range.mp hr).trans_le hR)) fun r _ hr ↦ ?_
  rw [Nat.choose_eq_zero_of_lt (by simpa using hr), Nat.cast_zero, mul_zero]

/-- **The regrouping**: `Q(X, ℓ, P) = Σ_{s ≤ M} Σ_{r < m A} E_{x, r, s}(ℓ) (X - x)^r (P - w)^s`,
with `w = f_x + ℓ g_x`. -/
theorem evalSum_eq_sum_ePoly {d A m D : ℕ} (c : idxSet d A m D → L) (x fx gx : L) (ℓ P : L[X]) :
    evalSum c ℓ P = ∑ s ∈ range (bigM d A m D + 1), ∑ r ∈ range (m * A),
      (ePoly c x fx gx s r).comp ℓ * (X - C x) ^ r * (P - (C fx + ℓ * C gx)) ^ s := by
  set w := C fx + ℓ * C gx
  have hterm (e : idxSet d A m D) : C (c e) * X ^ e.1.2.1 * ℓ ^ e.1.2.2 * P ^ e.1.1 =
      ∑ s ∈ range (bigM d A m D + 1), ∑ r ∈ range (m * A),
        C (c e) * (eTerm x fx gx s r e.1).comp ℓ * (X - C x) ^ r * (P - w) ^ s := by
    obtain ⟨hj, hi, -⟩ := mem_idxSet e.2
    have hX : (X : L[X]) ^ e.1.2.1 = ((X - C x) + C x) ^ e.1.2.1 := by rw [sub_add_cancel]
    have hP : P ^ e.1.1 = ((P - w) + w) ^ e.1.1 := by rw [sub_add_cancel]
    rw [hX, hP, add_pow_extend _ _ _ (m * A) (by omega),
      add_pow_extend _ _ _ (bigM d A m D + 1) (by omega)]
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun s _ ↦ sum_congr rfl fun r _ ↦ ?_
    simp only [eTerm, w, mul_comp, C_comp, X_comp, pow_comp, add_comp, map_mul, map_pow,
      map_natCast, natCast_comp]
    ring
  rw [evalSum, sum_congr rfl fun e _ ↦ hterm e, sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← sum_mul, ← sum_mul]
  congr 2
  simp only [ePoly, Polynomial.sum_comp, mul_comp, C_comp]

/-- **Vanishing to order `m`**: if `E_{x, r, s} = 0` for `r + s < m` and `P(x) = f_x + ℓ(x) g_x`,
then `(X - x)^m` divides `Q(X, ℓ, P)`. -/
theorem dvd_evalSum_of_ePoly {d A m D : ℕ} (c : idxSet d A m D → L) (x fx gx : L) (ℓ P : L[X])
    (hE : ∀ s r, r + s < m → ePoly c x fx gx s r = 0)
    (hx : P.eval x = fx + ℓ.eval x * gx) : (X - C x) ^ m ∣ evalSum c ℓ P := by
  rw [evalSum_eq_sum_ePoly c x fx gx]
  refine dvd_sum fun s _ ↦ dvd_sum fun r _ ↦ ?_
  by_cases hrs : r + s < m
  · rw [hE s r hrs]; simp
  · have hroot : X - C x ∣ P - (C fx + ℓ * C gx) := by
      rw [dvd_iff_isRoot]
      simp [hx]
    have : (X - C x) ^ m ∣ (X - C x) ^ r * (P - (C fx + ℓ * C gx)) ^ s :=
      (pow_dvd_pow _ (not_lt.mp hrs)).trans (by
        rw [pow_add]; exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hroot s))
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right this _

/-- The degree of `Q(X, ℓ, P)` is below `m A` when `deg ℓ ≤ 1` and `deg P ≤ d`. -/
theorem natDegree_evalSum_lt {d A m D : ℕ} (hmA : 0 < m * A) (c : idxSet d A m D → L)
    (ℓ P : L[X]) (hℓ : ℓ.natDegree ≤ 1) (hP : P.natDegree ≤ d) :
    (evalSum c ℓ P).natDegree < m * A := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := m * A - 1) fun e _ ↦ ?_)
    (by omega)
  obtain ⟨-, hi, hD⟩ := mem_idxSet e.2
  refine (natDegree_mul_le).trans ?_
  have h1 := (natDegree_mul_le (p := C (c e) * X ^ e.1.2.1) (q := ℓ ^ e.1.2.2))
  have h2 : (C (c e) * X ^ e.1.2.1 : L[X]).natDegree ≤ e.1.2.1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have h3 := (natDegree_pow_le (p := ℓ) (n := e.1.2.2)).trans (Nat.mul_le_mul_left _ hℓ)
  have h4 := (natDegree_pow_le (p := P) (n := e.1.1)).trans (Nat.mul_le_mul_left _ hP)
  have : e.1.2.1 + e.1.2.2 + d * e.1.1 ≤ m * A - 1 := by
    have : e.1.1 ≤ D := by omega
    rw [mul_comm d] at hi ⊢
    omega
  rw [mul_comm e.1.1 d] at h4
  omega

/-! ## The linear system -/

variable {F : Type*} [Field F] [Algebra F L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constraint map: the coefficient of `Y^k` in `E_{x, r, s}` at every point and every
`(s, (r, k)) ∈ eqSet`. -/
noncomputable def constraintMap (dom : ι ↪ F) (f g : ι → L) (d A m D : ℕ) :
    (idxSet d A m D → L) →ₗ[L] (ι × eqSet d A m D → L) where
  toFun c q := (ePoly c (pt dom q.1) (f q.1) (g q.1) q.2.1.1 q.2.1.2.1).coeff q.2.1.2.2
  map_add' c c' := by
    funext q
    simp [ePoly, add_mul, sum_add_distrib, finsetSum_coeff]
  map_smul' a c := by
    funext q
    simp [ePoly, mul_assoc, mul_sum, finsetSum_coeff]

omit [Fintype ι] [DecidableEq ι] in
/-- **Lemma 4.2, the polynomial identity**: a solution of the constraints vanishes along every
line `ℓ` of degree at most `1` and every candidate of degree at most `d` agreeing with
`f + ℓ g` on at least `A` points. -/
theorem evalSum_eq_zero (dom : ι ↪ F) (f g : ι → L) {d A m D : ℕ} (hm : 1 ≤ m)
    (c : idxSet d A m D → L) (hc : constraintMap dom f g d A m D c = 0) (ℓ P : L[X])
    (hℓ : ℓ.natDegree ≤ 1) (hP : P.natDegree ≤ d)
    (S : Finset ι) (hS : A ≤ S.card) (hagree : ∀ x ∈ S, P.eval (pt dom x) = f x + ℓ.eval (pt dom x) * g x) :
    evalSum c ℓ P = 0 := by
  classical
  -- At every point, `E_{x, r, s} = 0` for `r + s < m`.
  have hE : ∀ x, ∀ s r, r + s < m → ePoly c (pt dom x) (f x) (g x) s r = 0 := by
    intro x s r hrs
    by_cases hsM : s ≤ bigM d A m D
    · refine Polynomial.ext fun k ↦ ?_
      rw [coeff_zero]
      by_cases hk : k ≤ D - s
      · have hq : (⟨s, (r, k)⟩ : Σ _ : ℕ, ℕ × ℕ) ∈ eqSet d A m D := by
          simp only [eqSet, mem_sigma, mem_range, mem_product]
          refine ⟨?_, by omega, by omega⟩
          have : s ≤ m - 1 := by omega
          exact Nat.lt_succ_of_le (le_min this hsM)
        exact congrFun hc (x, ⟨_, hq⟩)
      · exact coeff_eq_zero_of_natDegree_lt ((natDegree_ePoly_le c _ _ _ s r).trans_lt
          (by omega))
    · exact ePoly_eq_zero_of_lt c _ _ _ r (by omega)
  by_contra hne
  have hdvd : ∏ x ∈ S, (X - C (pt dom x)) ^ m ∣ evalSum c ℓ P := by
    refine Finset.prod_dvd_of_coprime ?_ fun x hx ↦
      dvd_evalSum_of_ePoly c _ _ _ ℓ P (hE x) (hagree x hx)
    intro x _ y _ hxy
    exact ((pairwise_coprime_X_sub_C (pt_injective dom)) hxy).pow
  have hdeg := natDegree_le_of_dvd hdvd hne
  rw [natDegree_prod _ _ fun x _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)] at hdeg
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, sum_const, smul_eq_mul] at hdeg
  have hmA : 0 < m * A ∨ A = 0 := by
    rcases Nat.eq_zero_or_pos A with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.mul_pos (by omega) h)
  rcases hmA with hmA | hA0
  · have := natDegree_evalSum_lt hmA c ℓ P hℓ hP
    have : m * A ≤ S.card * m := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hS
    omega
  · -- `A = 0`: no unknowns, since `m A - D - d j = 0`.
    apply hne
    refine sum_eq_zero fun e _ ↦ ?_
    have := (mem_idxSet e.2).2.1
    have h0 : m * A - D = 0 := by simp [hA0]
    omega

omit [DecidableEq ι] in
/-- **Lemma 4.2, existence**: if the interpolation inequality holds, the constraint map has a
nonzero solution. -/
theorem exists_ne_zero_constraint (dom : ι ↪ F) (f g : ι → L) {d A m D : ℕ}
    (hineq : equations (Fintype.card ι) d A m D < unknowns d A m D) :
    ∃ c : idxSet d A m D → L, c ≠ 0 ∧ constraintMap dom f g d A m D c = 0 := by
  have hrank : Module.finrank L (ι × eqSet d A m D → L) <
      Module.finrank L (idxSet d A m D → L) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_idxSet, card_eqSet]
    exact hineq
  obtain ⟨c, hc, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := constraintMap dom f g d A m D) hrank)
  exact ⟨c, hne, hc⟩

/-! ## The interpolating polynomial -/

/-- The exponent `X^i Y^t Z^j` of the unknown `(j, (i, t))`. -/
noncomputable def expo (e : Σ _ : ℕ, ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 e.2.1 + Finsupp.single 1 e.2.2 + Finsupp.single 2 e.1

@[simp] theorem expo_zero (e : Σ _ : ℕ, ℕ × ℕ) : expo e 0 = e.2.1 := by simp [expo]
@[simp] theorem expo_one (e : Σ _ : ℕ, ℕ × ℕ) : expo e 1 = e.2.2 := by simp [expo]
@[simp] theorem expo_two (e : Σ _ : ℕ, ℕ × ℕ) : expo e 2 = e.1 := by simp [expo]

theorem expo_injective : Function.Injective expo := by
  intro e e' h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp only [expo_zero, expo_one, expo_two] at h0 h1 h2
  obtain ⟨j, i, t⟩ := e
  obtain ⟨j', i', t'⟩ := e'
  simp only at h0 h1 h2
  subst h0 h1 h2
  rfl

/-- The polynomial `Q = Σ_e c_e X^i Y^t Z^j`. -/
noncomputable def interpolant {d A m D : ℕ} (c : idxSet d A m D → L) : MvPolynomial (Fin 3) L :=
  ∑ e : idxSet d A m D, MvPolynomial.monomial (expo e.1) (c e)

theorem coeff_interpolant {d A m D : ℕ} (c : idxSet d A m D → L) (e : idxSet d A m D) :
    (interpolant c).coeff (expo e.1) = c e := by
  classical
  rw [interpolant, MvPolynomial.coeff_sum]
  rw [sum_eq_single e (fun e' _ hne ↦ by
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exact absurd (Subtype.ext (expo_injective h)) hne
      · rfl) (by simp)]
  simp

theorem interpolant_ne_zero {d A m D : ℕ} {c : idxSet d A m D → L} (hc : c ≠ 0) :
    interpolant c ≠ 0 := by
  intro h
  apply hc
  funext e
  rw [← coeff_interpolant c e, h]
  simp

theorem aeval_interpolant {d A m D : ℕ} (c : idxSet d A m D → L) (ℓ P : L[X]) :
    MvPolynomial.aeval ![X, ℓ, P] (interpolant c) = evalSum c ℓ P := by
  rw [interpolant, map_sum, evalSum]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [MvPolynomial.aeval_monomial, expo, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_add_index' (by simp) (by simp [pow_add]), Finsupp.prod_single_index (by simp),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  simp only [Polynomial.algebraMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Algebra.algebraMap_self,
    RingHom.id_apply]
  ring

theorem support_interpolant {d A m D : ℕ} (c : idxSet d A m D → L) :
    ∀ s ∈ (interpolant c).support,
      s 1 + s 2 ≤ D ∧ s 2 ≤ bigM d A m D ∧ s 0 + s 1 + d * s 2 < m * A := by
  classical
  intro s hs
  obtain ⟨e, -, he⟩ := mem_biUnion.mp (MvPolynomial.support_sum hs)
  have hse : s = expo e.1 := by
    by_contra hne
    refine (MvPolynomial.mem_support_iff.mp he) ?_
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact absurd h.symm hne
    · rfl
  subst hse
  obtain ⟨hj, hi, hD⟩ := mem_idxSet e.2
  simp only [expo_zero, expo_one, expo_two]
  refine ⟨by omega, hj, ?_⟩
  have : e.1.2.2 ≤ D := by omega
  omega

omit [DecidableEq ι] in
/-- **[CYWZ26, Lemma 4.2]**: if `1 ≤ m` and the interpolation inequality holds, a nonzero
`Q ∈ L[X, Y, Z]` with monomials `X^i Y^t Z^j`, `t + j ≤ D`, `j ≤ M`, `i + t + d j < m A`, vanishes
at `(X, ℓ, P)` for every `ℓ` of degree at most `1` and every `P` of degree at most `d` agreeing with
`f + ℓ g` on at least `A` points. -/
theorem exists_interpolant (dom : ι ↪ F) (f g : ι → L) {d A m D : ℕ} (hm : 1 ≤ m)
    (hineq : equations (Fintype.card ι) d A m D < unknowns d A m D) :
    ∃ Q : MvPolynomial (Fin 3) L, Q ≠ 0 ∧
      (∀ s ∈ Q.support, s 1 + s 2 ≤ D ∧ s 2 ≤ bigM d A m D ∧ s 0 + s 1 + d * s 2 < m * A) ∧
      ∀ ℓ P : L[X], ℓ.natDegree ≤ 1 → P.natDegree ≤ d → ∀ S : Finset ι, A ≤ S.card →
        (∀ x ∈ S, P.eval (pt dom x) = f x + ℓ.eval (pt dom x) * g x) →
        MvPolynomial.aeval ![X, ℓ, P] Q = 0 := by
  obtain ⟨c, hc, hker⟩ := exists_ne_zero_constraint dom f g hineq
  refine ⟨interpolant c, interpolant_ne_zero hc, support_interpolant c,
    fun ℓ P hℓ hP S hS hagree ↦ ?_⟩
  rw [aeval_interpolant]
  exact evalSum_eq_zero dom f g hm c hker ℓ P hℓ hP S hS hagree

end
end LeanVM.Protocol.Whir.AffineCombiner
