/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerChart

  The Taylor chart of a factor `R(X, Y, Z)` at the transcendental center `T₀`: the shifted
  polynomial `R(T₀ + W, Y + V W, Z + U)` over `L(T₀)[Y, V, Z]`, its coefficient degrees, and its
  specializations. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerHensel
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The chart of a factor

[CWYZ26], Claim 4.9, in the coordinates of its proof: for `R ∈ L[X, Y, Z]`, the center
is the indeterminate `T₀` of `K₀ = L(T₀)`, and the chart ring is `K₀[Y, V, Z]` (`ChartRing L`,
variables `0, 1, 2`). The shifted polynomial `chartRs R = R(T₀ + W, Y + V W, Z + U)` lies in
`ChartRing[W][U]`, with `U` outer; `chartA R a b` is its coefficient of `W^a U^b`.

* `goodDeg_chartRs`: if every monomial `X^i Y^t Z^j` of `R` has `t + j ≤ h`, a nonzero
  `A_{a,b}` has `deg A_{a,b} + b ≤ h` (degrees in `Y, V, Z`), so the hypotheses of
  `totalDegree_numerators_le` hold with `d = h`.
* `map_chartRs`: at a point `y`, `chartRs R` specializes to `R(T₀ + W, y₀ + y₁ W, y₂ + U)`.
* `coeff_aeval_add_X`: the coefficients of `U⁰` and `U¹` in `R(c₀, c₁, c₂ + U)` are `R(c)` and
  `∂_Z R(c)`, so the separant `A_{0,1}` is `∂_Z R(T₀, Y, Z)`.
* `chartA_zero_one_eq_zero`: if the hypersurface `A_{0,0} = R(T₀, Y, Z)` vanishes identically,
  so does the separant.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {L : Type*} [Field L]

/-- The chart ring `L(T₀)[Y, V, Z]`. -/
abbrev ChartRing (L : Type*) [Field L] := MvPolynomial (Fin 3) (RatFunc L)

/-- The substitution `X ↦ T₀ + W`, `Y ↦ Y + V W`, `Z ↦ Z + U`. -/
noncomputable def chartSubst : Fin 3 → Polynomial (Polynomial (ChartRing L)) :=
  ![C (C (MvPolynomial.C RatFunc.X) + X), C (C (MvPolynomial.X 0) + C (MvPolynomial.X 1) * X),
    C (C (MvPolynomial.X 2)) + X]

/-- **The shifted polynomial** `R(T₀ + W, Y + V W, Z + U)`. -/
noncomputable def chartRs (R : MvPolynomial (Fin 3) L) : Polynomial (Polynomial (ChartRing L)) :=
  MvPolynomial.aeval chartSubst R

/-- The coefficient `A_{a,b}` of `W^a U^b`. -/
noncomputable def chartA (R : MvPolynomial (Fin 3) L) (a b : ℕ) : ChartRing L :=
  ((chartRs R).coeff b).coeff a

/-! ## A ring hom through `aeval` -/

/-- A ring hom compatible with the structure maps from `L` commutes with `aeval`. -/
theorem map_aeval_of_comm {S S' : Type*} [CommRing S] [CommRing S'] [Algebra L S]
    [Algebra L S'] (φ : S →+* S') (hφ : ∀ c : L, φ (algebraMap L S c) = algebraMap L S' c)
    {σ : Type*} (f : σ → S) (R : MvPolynomial σ L) :
    φ (MvPolynomial.aeval f R) = MvPolynomial.aeval (fun i ↦ φ (f i)) R := by
  induction R using MvPolynomial.induction_on with
  | C c => simp [hφ]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- `map_aeval_of_comm` with the image of the substitution given. -/
theorem map_aeval_eq {S S' : Type*} [CommRing S] [CommRing S'] [Algebra L S] [Algebra L S']
    (φ : S →+* S') (hφ : ∀ c : L, φ (algebraMap L S c) = algebraMap L S' c) {σ : Type*}
    (f : σ → S) (g : σ → S') (hfg : ∀ i, φ (f i) = g i) (R : MvPolynomial σ L) :
    φ (MvPolynomial.aeval f R) = MvPolynomial.aeval g R := by
  rw [map_aeval_of_comm φ hφ, show (fun i ↦ φ (f i)) = g from funext hfg]

/-! ## Degrees -/

section Degrees

/-- Every coefficient of `p ∈ ChartRing[W]` has degree at most `w`. -/
def InnerDeg (p : Polynomial (ChartRing L)) (w : ℕ) : Prop := ∀ a, (p.coeff a).totalDegree ≤ w

/-- A nonzero coefficient `A_{a,b}` of `Φ` has `deg A_{a,b} + b ≤ w`. -/
def GoodDeg (Φ : Polynomial (Polynomial (ChartRing L))) (w : ℕ) : Prop :=
  ∀ a b, (Φ.coeff b).coeff a ≠ 0 → ((Φ.coeff b).coeff a).totalDegree + b ≤ w

/-- The degree of a nonzero sum, plus `b`, from its nonzero terms. -/
theorem totalDegree_sum_add_le {ι σ R : Type*} [CommRing R] (s : Finset ι)
    (f : ι → MvPolynomial σ R) {b w : ℕ} (hne : ∑ i ∈ s, f i ≠ 0)
    (hf : ∀ i ∈ s, f i ≠ 0 → (f i).totalDegree + b ≤ w) :
    (∑ i ∈ s, f i).totalDegree + b ≤ w := by
  obtain ⟨i₀, hi₀, h₀⟩ := exists_ne_zero_of_sum_ne_zero hne
  have hbw : b ≤ w := le_trans (Nat.le_add_left _ _) (hf i₀ hi₀ h₀)
  have : (∑ i ∈ s, f i).totalDegree ≤ w - b := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi ↦ ?_)
    by_cases hz : f i = 0
    · rw [hz, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
    · have := hf i hi hz; omega
  omega

theorem InnerDeg.add {p q : Polynomial (ChartRing L)} {w : ℕ} (hp : InnerDeg p w)
    (hq : InnerDeg q w) : InnerDeg (p + q) w := fun a ↦ by
  rw [coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hp a) (hq a))

theorem innerDeg_C {x : ChartRing L} {w : ℕ} (hx : x.totalDegree ≤ w) : InnerDeg (C x) w :=
  fun a ↦ by
    rw [coeff_C]; split_ifs
    · exact hx
    · simp

theorem innerDeg_C_mul_X {x : ChartRing L} {w : ℕ} (hx : x.totalDegree ≤ w) :
    InnerDeg (C x * X) w := fun a ↦ by
  rw [coeff_C_mul_X]; split_ifs
  · exact hx
  · simp

theorem innerDeg_X : InnerDeg (X : Polynomial (ChartRing L)) 0 := fun a ↦ by
  rw [coeff_X]; split_ifs <;> simp

theorem GoodDeg.mono {Φ : Polynomial (Polynomial (ChartRing L))} {w w' : ℕ} (h : GoodDeg Φ w)
    (hw : w ≤ w') : GoodDeg Φ w' := fun a b hne ↦ (h a b hne).trans hw

theorem GoodDeg.add {Φ Ψ : Polynomial (Polynomial (ChartRing L))} {w : ℕ} (hΦ : GoodDeg Φ w)
    (hΨ : GoodDeg Ψ w) : GoodDeg (Φ + Ψ) w := by
  intro a b hne
  rw [coeff_add, coeff_add] at hne ⊢
  by_cases h1 : (Φ.coeff b).coeff a = 0
  · rw [h1, zero_add] at hne ⊢; exact hΨ a b hne
  by_cases h2 : (Ψ.coeff b).coeff a = 0
  · rw [h2, add_zero] at hne ⊢; exact hΦ a b hne
  have e1 := hΦ a b h1
  have e2 := hΨ a b h2
  have e3 := MvPolynomial.totalDegree_add ((Φ.coeff b).coeff a) ((Ψ.coeff b).coeff a)
  omega

theorem goodDeg_C {p : Polynomial (ChartRing L)} {w : ℕ} (hp : InnerDeg p w) :
    GoodDeg (C p) w := by
  intro a b hne
  rw [coeff_C] at hne ⊢
  split_ifs at hne ⊢ with hb
  · subst hb; simpa using hp a
  · simp at hne

theorem goodDeg_X : GoodDeg (X : Polynomial (Polynomial (ChartRing L))) 1 := by
  intro a b hne
  rw [coeff_X] at hne ⊢
  split_ifs at hne ⊢ with hb
  · subst hb
    rw [coeff_one] at hne ⊢
    split_ifs at hne ⊢ <;> simp_all
  · simp at hne

theorem GoodDeg.mul {Φ Ψ : Polynomial (Polynomial (ChartRing L))} {w₁ w₂ : ℕ}
    (hΦ : GoodDeg Φ w₁) (hΨ : GoodDeg Ψ w₂) : GoodDeg (Φ * Ψ) (w₁ + w₂) := by
  intro a b hne
  rw [coeff_mul, finsetSum_coeff] at hne ⊢
  refine totalDegree_sum_add_le _ _ hne fun x hx hxne ↦ ?_
  have hx := mem_antidiagonal.mp hx
  rw [coeff_mul] at hxne ⊢
  have : b = x.1 + x.2 := hx.symm
  rw [this]
  refine totalDegree_sum_add_le _ _ hxne fun y _ hyne ↦ ?_
  have h1 := hΦ y.1 x.1 (left_ne_zero_of_mul hyne)
  have h2 := hΨ y.2 x.2 (right_ne_zero_of_mul hyne)
  have := MvPolynomial.totalDegree_mul ((Φ.coeff x.1).coeff y.1) ((Ψ.coeff x.2).coeff y.2)
  omega

theorem goodDeg_one : GoodDeg (1 : Polynomial (Polynomial (ChartRing L))) 0 :=
  goodDeg_C (innerDeg_C (by simp))

theorem GoodDeg.pow {Φ : Polynomial (Polynomial (ChartRing L))} {w : ℕ} (hΦ : GoodDeg Φ w)
    (n : ℕ) : GoodDeg (Φ ^ n) (n * w) := by
  induction n with
  | zero => simpa using goodDeg_one
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul hΦ

theorem goodDeg_chartSubst_zero : GoodDeg (chartSubst (L := L) 0) 0 :=
  goodDeg_C ((innerDeg_C (by simp)).add (by simpa using innerDeg_X))

theorem goodDeg_chartSubst_one : GoodDeg (chartSubst (L := L) 1) 1 :=
  goodDeg_C ((innerDeg_C (by simp)).add (innerDeg_C_mul_X (by simp)))

theorem goodDeg_chartSubst_two : GoodDeg (chartSubst (L := L) 2) 1 :=
  (goodDeg_C (innerDeg_C (by simp))).add goodDeg_X

/-- **Coefficient degrees of the chart**: if every monomial `X^i Y^t Z^j` of `R` has
`t + j ≤ h`, then `deg A_{a,b} + b ≤ h` for every nonzero `A_{a,b}`. -/
theorem goodDeg_chartRs (R : MvPolynomial (Fin 3) L) {h : ℕ}
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) : GoodDeg (chartRs R) h := by
  classical
  rw [chartRs, R.as_sum, map_sum]
  intro a b hne
  rw [finsetSum_coeff, finsetSum_coeff] at hne ⊢
  refine totalDegree_sum_add_le _ _ hne fun m hm hmne ↦ ?_
  have hterm : GoodDeg (MvPolynomial.aeval (chartSubst (L := L)) (MvPolynomial.monomial m (R.coeff m)))
      (m 1 + m 2) := by
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Fin.prod_univ_three]
    have hc : GoodDeg (algebraMap L (Polynomial (Polynomial (ChartRing L))) (R.coeff m)) 0 := by
      rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_apply]
      exact goodDeg_C (innerDeg_C (by simp))
    have := ((hc.mul (goodDeg_chartSubst_zero.pow (m 0))).mul
      (goodDeg_chartSubst_one.pow (m 1))).mul (goodDeg_chartSubst_two.pow (m 2))
    simpa [mul_assoc] using this
  exact (hterm.mono (hR m hm)) a b hmne

/-- The outer degree of the chart is at most `h`. -/
theorem natDegree_chartRs_le (R : MvPolynomial (Fin 3) L) {h : ℕ}
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) : (chartRs R).natDegree ≤ h := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun b hb ↦ ?_
  ext a : 1
  by_contra hne
  have := goodDeg_chartRs R hR a b hne
  have hbh : b ≤ h := by omega
  exact absurd hb (not_lt.mpr (by exact_mod_cast hbh))

/-- The Hensel hypotheses: `deg A_{a,b} + b ≤ h` for `b ≤ h`. -/
theorem chartA_totalDegree_le (R : MvPolynomial (Fin 3) L) {h : ℕ}
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (a b : ℕ) (hb : b ≤ h) :
    (chartA R a b).totalDegree + b ≤ h := by
  by_cases hz : chartA R a b = 0
  · rw [hz, MvPolynomial.totalDegree_zero]; omega
  · exact goodDeg_chartRs R hR a b hz

end Degrees

/-! ## Specialization -/

section Specialization

variable {K' : Type*} [Field K'] [Algebra (RatFunc L) K'] [Algebra L K']
  [IsScalarTower L (RatFunc L) K']

/-- **The chart at a point** `y`: `R(T₀ + W, y₀ + y₁ W, y₂ + U)`. -/
theorem map_chartRs (R : MvPolynomial (Fin 3) L) (y : Fin 3 → K') :
    (chartRs R).map (mapRingHom (MvPolynomial.aeval y).toRingHom) =
      MvPolynomial.aeval ![C (C (algebraMap (RatFunc L) K' RatFunc.X) + X),
        C (C (y 0) + C (y 1) * X), C (C (y 2)) + X] R := by
  rw [chartRs, ← coe_mapRingHom]
  refine map_aeval_eq (S := (ChartRing L)[X][X]) (S' := K'[X][X])
    (mapRingHom (mapRingHom (MvPolynomial.aeval (R := RatFunc L) y).toRingHom)) (fun c ↦ ?_) _ _
    (fun i ↦ ?_) R
  · simp [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_apply,
      IsScalarTower.algebraMap_apply L (RatFunc L) K']
  · fin_cases i <;> simp [chartSubst]

/-- **The coefficients of `R(c₀, c₁, c₂ + U)`**: `U⁰` gives `R(c)`, `U¹` gives `∂_Z R(c)`. -/
theorem coeff_aeval_add_X {S : Type*} [CommRing S] [Algebra L S] (R : MvPolynomial (Fin 3) L)
    (c : Fin 3 → S) :
    (MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R).coeff 0 = MvPolynomial.aeval c R ∧
      (MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R).coeff 1 =
        MvPolynomial.aeval c (MvPolynomial.pderiv 2 R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply, coeff_C]
  | add p q hp hq => simp [hp.1, hp.2, hq.1, hq.2]
  | mul_X p i hp =>
    refine ⟨?_, ?_⟩
    · rw [map_mul, MvPolynomial.aeval_X, mul_coeff_zero, hp.1, map_mul, MvPolynomial.aeval_X]
      fin_cases i <;> simp
    · rw [map_mul, MvPolynomial.aeval_X, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self]
      rw [hp.1, hp.2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        MvPolynomial.aeval_X]
      fin_cases i <;> simp [MvPolynomial.pderiv_X, coeff_C, coeff_X] <;> ring

/-- At a point, the separant `A_{0,1}` is `∂_Z R(T₀, y₀, y₂)` and `A_{0,0}` is `R(T₀, y₀, y₂)`. -/
theorem aeval_chartA_zero (R : MvPolynomial (Fin 3) L) (y : Fin 3 → K') :
    MvPolynomial.aeval y (chartA R 0 0) =
        MvPolynomial.aeval ![algebraMap (RatFunc L) K' RatFunc.X, y 0, y 2] R ∧
      MvPolynomial.aeval y (chartA R 0 1) =
        MvPolynomial.aeval ![algebraMap (RatFunc L) K' RatFunc.X, y 0, y 2]
          (MvPolynomial.pderiv 2 R) := by
  set c : Fin 3 → K' := ![algebraMap (RatFunc L) K' RatFunc.X, y 0, y 2]
  -- Setting `W = 0` in the chart at `y` leaves `R(T₀, y₀, y₂ + U)`.
  have hW : ((chartRs R).map (mapRingHom (MvPolynomial.aeval y).toRingHom)).map
      (evalRingHom 0) = MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R := by
    rw [map_chartRs, ← coe_mapRingHom]
    refine map_aeval_eq (S := K'[X][X]) (S' := K'[X]) (mapRingHom (evalRingHom (0 : K')))
      (fun a ↦ ?_) _ _ (fun i ↦ ?_) R
    · simp [Polynomial.algebraMap_apply]
    · fin_cases i <;> simp [c]
  have hcoeff (b : ℕ) : (((chartRs R).map (mapRingHom (MvPolynomial.aeval y).toRingHom)).map
      (evalRingHom 0)).coeff b = MvPolynomial.aeval y (chartA R 0 b) := by
    simp [chartA, coeff_map, ← coeff_zero_eq_eval_zero]
  have hc := coeff_aeval_add_X R c
  rw [← hW, hcoeff, hcoeff] at hc
  exact hc

/-- If the hypersurface `A_{0,0} = R(T₀, Y, Z)` vanishes identically, so does the separant. -/
theorem chartA_zero_one_eq_zero (R : MvPolynomial (Fin 3) L) (h : chartA R 0 0 = 0) :
    chartA R 0 1 = 0 := by
  set c : Fin 3 → ChartRing L :=
    ![MvPolynomial.C RatFunc.X, MvPolynomial.X 0, MvPolynomial.X 2]
  -- `R(T₀, Y, Z + U)`, the chart at `W = 0`.
  have hW : (chartRs R).map (evalRingHom 0) = MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R := by
    rw [chartRs, ← coe_mapRingHom]
    refine map_aeval_eq (S := (ChartRing L)[X][X]) (S' := (ChartRing L)[X])
      (mapRingHom (evalRingHom (0 : ChartRing L))) (fun a ↦ ?_) _ _ (fun i ↦ ?_) R
    · simp [Polynomial.algebraMap_apply]
    · fin_cases i <;> simp [chartSubst, c]
  have hcoeff (b : ℕ) : ((chartRs R).map (evalRingHom 0)).coeff b = chartA R 0 b := by
    simp [chartA, coeff_map, ← coeff_zero_eq_eval_zero]
  have hc := coeff_aeval_add_X R c
  rw [← hW, hcoeff, hcoeff] at hc
  -- `Z ↦ Z + U` sends `R(T₀, Y, Z)` to `R(T₀, Y, Z + U)`.
  let σU : ChartRing L →+* Polynomial (ChartRing L) := (MvPolynomial.aeval
    ![C (MvPolynomial.X 0), C (MvPolynomial.X 1), C (MvPolynomial.X 2) + X]).toRingHom
  have hσ : σU (MvPolynomial.aeval c R) = MvPolynomial.aeval ![C (c 0), C (c 1), C (c 2) + X] R := by
    refine map_aeval_eq (S := ChartRing L) (S' := (ChartRing L)[X]) σU (fun a ↦ ?_) _ _
      (fun i ↦ ?_) R
    · simp [σU, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_apply]
    · fin_cases i <;> simp [σU, c]
  rw [← hW, ← hc.1, h, map_zero] at hσ
  rw [← hcoeff, ← hσ, coeff_zero]

end Specialization

end
end LeanVM.Protocol.Whir.AffineCombiner
