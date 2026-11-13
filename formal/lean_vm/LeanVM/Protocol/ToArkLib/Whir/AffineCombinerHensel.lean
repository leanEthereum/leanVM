/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerHensel

  Hensel lifting with cleared denominators ([CWYZ26], Lemma 3.11): ArkLib's universal
  numerators are the Taylor coefficients of every simple root, and have degree at most
  `1 + (2n - 1)(h - 1)`. Candidate for ArkLib.
-/

module

public import ArkLib.Data.Polynomial.UniversalHenselNumerator
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Tactic

/-!
# Hensel numerators

Let `Rs : A[W][U]` be a polynomial in a root increment `U` (outer variable) with coefficients in
`A[W]`, `W` a parameter increment, and write `A_{a,b}` for the coefficient of `W^a U^b` and
`s = A_{0,1}` for the separant. ArkLib's `Polynomial.UniversalHenselNumerator.numerators Rs s d`
(`N_n`) is the recurrence `N_n = -Σ_{a ≤ n, b ≤ d} A_{a,b} s^(2a+b-2) [w^(n-a)] (Σ_{1 ≤ i < n} N_i w^i)^b`.
It is [CWYZ26], Lemma 3.11, after the substitution `W = s² w`, `U = s ε(w)`, which
clears every denominator: a root `E(W) = Σ e_i W^i` of `Rs(W, E(W)) = 0` gives
`ε(w) = E(s² w)/s`, `ε_i = e_i s^(2i-1)`.

* `eq_numerators_of_root` (correctness, over a field): if `s ≠ 0`, `deg_U Rs ≤ d`, `1 ≤ d`,
  `ε(0) = 0` and `Rs(s² w, s ε(w)) = 0`, then `ε_n = N_n` for every `n ≥ 1`.
* `totalDegree_numerators_le` (degrees, coefficients in `MvPolynomial σ K`): if
  `deg A_{a,b} + b ≤ h` for `b ≤ d`, `deg s ≤ h - 1`, `d ≤ h` and `1 ≤ h`, then
  `deg N_n ≤ 1 + (2n - 1)(h - 1)`, the bound of Lemma 3.11.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial Polynomial.UniversalHenselNumerator

@[expose] public section

/-! ## Correctness -/

section Correctness

variable {K : Type*} [Field K]

/-- Scaling the variable scales the coefficients: `(p (c X))_a = c^a p_a`. -/
theorem coeff_comp_C_mul_X (p : K[X]) (c : K) (a : ℕ) :
    (p.comp (C c * X)).coeff a = c ^ a * p.coeff a := by
  rw [comp, eval₂_eq_sum_range, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split
  · ring
  · rw [coeff_eq_zero_of_natDegree_lt (by simp_all), mul_zero]

/-- Two polynomials without constant term that agree below `n` have equal `b`-th powers below
`n + b - 1`. -/
theorem coeff_pow_eq_of_agree {ε π : K[X]} (hε : ε.coeff 0 = 0) (hπ : π.coeff 0 = 0) {n : ℕ}
    (hagree : ∀ i < n, ε.coeff i = π.coeff i) {b m : ℕ} (hb : 1 ≤ b) (hm : m + 1 < n + b) :
    (ε ^ b).coeff m = (π ^ b).coeff m := by
  have hX : X ∣ ε := X_dvd_iff.mpr hε
  have hX' : X ∣ π := X_dvd_iff.mpr hπ
  have hdiff : X ^ n ∣ ε - π := X_pow_dvd_iff.mpr fun i hi ↦ by
    rw [coeff_sub, hagree i hi, sub_self]
  have hgeom : X ^ (b - 1) ∣ ∑ i ∈ range b, ε ^ i * π ^ (b - 1 - i) := dvd_sum fun i hi ↦ by
    have hi := mem_range.mp hi
    have hsplit : (X : K[X]) ^ (b - 1) = X ^ i * X ^ (b - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hX i) (pow_dvd_pow_of_dvd hX' _)
  have hdvd : X ^ (n + (b - 1)) ∣ ε ^ b - π ^ b := by
    have := mul_dvd_mul hgeom hdiff
    rwa [← pow_add, add_comm (b - 1), geom_sum₂_mul] at this
  have := (X_pow_dvd_iff.mp hdvd) m (by omega)
  rwa [coeff_sub, sub_eq_zero] at this

/-- The coefficients of `Rs(s² w, s ε(w))`. -/
theorem coeff_eval_scaled (Rs : Polynomial K[X]) (s : K) {d : ℕ} (hd : Rs.natDegree ≤ d)
    (ε : K[X]) (n : ℕ) :
    ((Rs.map (compRingHom (C (s ^ 2) * X))).eval (C s * ε)).coeff n =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (d + 1),
        (Rs.coeff b).coeff a * s ^ (2 * a + b) * (ε ^ b).coeff (n - a) := by
  rw [eval_eq_sum_range' (n := d + 1) (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hd)),
    finsetSum_coeff, sum_comm]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [coeff_map, coe_compRingHom, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [coeff_comp_C_mul_X, mul_pow, ← C_pow, coeff_C_mul]
  ring

/-- **Correctness of the Hensel numerators** ([CWYZ26, Lemma 3.11], uniqueness): if
`s = A_{0,1} ≠ 0` and `ε` without constant term satisfies `Rs(s² w, s ε(w)) = 0`, then
`ε_n = N_n` for every `n ≥ 1`. -/
theorem eq_numerators_of_root (Rs : Polynomial K[X]) (s : K) (hs : s ≠ 0)
    (h01 : (Rs.coeff 1).coeff 0 = s) {d : ℕ} (hd : Rs.natDegree ≤ d) (hd1 : 1 ≤ d)
    (ε : K[X]) (hε0 : ε.coeff 0 = 0)
    (hroot : (Rs.map (compRingHom (C (s ^ 2) * X))).eval (C s * ε) = 0) :
    ∀ n, 1 ≤ n → ε.coeff n = numerators Rs s d n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  set prior : ℕ → K := fun i ↦ if i ≤ t then numerators Rs s d i else 0
  set π := positivePrefix prior (t + 1)
  have hπ0 : π.coeff 0 = 0 := by simp [π, positivePrefix_coeff]
  have hagree : ∀ i < t + 1, ε.coeff i = π.coeff i := by
    intro i hi
    rw [positivePrefix_coeff]
    by_cases hi0 : i = 0
    · simp [hi0, hε0]
    · have hc : 0 < i ∧ i < t + 1 := ⟨by omega, hi⟩
      have hit : i ≤ t := by omega
      simp only [hc, hit, prior, and_self, ↓reduceIte]
      exact ih i hi (by omega)
  -- Termwise: `A s^(2a+b) (ε^b)_(n-a) = s² (A s^(2a+b-2) (π^b)_(n-a)) + [a = 0, b = 1] s² ε_n`.
  have hterm : ∀ a ∈ range (t + 1 + 1), ∀ b ∈ range (d + 1),
      (Rs.coeff b).coeff a * s ^ (2 * a + b) * (ε ^ b).coeff (t + 1 - a) =
        s ^ 2 * residualTerm Rs s (t + 1) a b prior +
          if a = 0 ∧ b = 1 then s ^ 2 * ε.coeff (t + 1) else 0 := by
    intro a _ b _
    simp only [residualTerm]
    by_cases h0 : a = 0 ∧ b = 1
    · obtain ⟨rfl, rfl⟩ := h0
      simp only [and_self, ↓reduceIte, Nat.sub_zero, pow_one, h01, positivePrefix_coeff_self]
      ring
    · simp only [h0, ↓reduceIte, add_zero]
      by_cases hab : 2 ≤ 2 * a + b
      · have hcoeff : (ε ^ b).coeff (t + 1 - a) = (π ^ b).coeff (t + 1 - a) := by
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb; simp
          · exact coeff_pow_eq_of_agree hε0 hπ0 hagree hb (by omega)
        have hp : s ^ (2 * a + b) = s ^ 2 * s ^ (2 * a + b - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [hcoeff, hp]
        ring
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha hb
        simp [coeff_one]
  have hsum := coeff_eval_scaled Rs s hd ε (t + 1)
  rw [hroot, coeff_zero, sum_congr rfl fun a ha ↦ sum_congr rfl fun b hb ↦ hterm a ha b hb] at hsum
  simp only [sum_add_distrib, ← mul_sum] at hsum
  have hite : ∑ a ∈ range (t + 1 + 1), ∑ b ∈ range (d + 1),
      (if a = 0 ∧ b = 1 then s ^ 2 * ε.coeff (t + 1) else 0) = s ^ 2 * ε.coeff (t + 1) := by
    rw [sum_eq_single 0 (fun a _ ha ↦ sum_eq_zero fun b _ ↦ by simp [ha]) (by simp),
      sum_eq_single 1 (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd (mem_range.mpr (by omega)) h)]
    simp
  rw [hite] at hsum
  have hN : numerators Rs s d (t + 1) =
      -∑ a ∈ range (t + 1 + 1), ∑ b ∈ range (d + 1), residualTerm Rs s (t + 1) a b prior := by
    rw [numerators_succ, numeratorStep]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  rw [hN]
  have : s ^ 2 * (ε.coeff (t + 1) + ∑ a ∈ range (t + 1 + 1), ∑ b ∈ range (d + 1),
      residualTerm Rs s (t + 1) a b prior) = 0 := by linear_combination -hsum
  have := (mul_eq_zero.mp this).resolve_left hs2
  linear_combination this

end Correctness

/-! ## Degrees -/

section Degrees

variable {σ K : Type*} [Field K]

/-- The coefficients of a power of a prefix without constant term: a nonzero coefficient at `m`
of `π^b` has `b ≤ m` and degree at most `b + (2m - b)(h - 1)`, when every nonzero coefficient
`π_i` has `1 ≤ i` and degree at most `1 + (2i - 1)(h - 1)`. -/
theorem totalDegree_coeff_pow_le (π : Polynomial (MvPolynomial σ K)) (h : ℕ)
    (hπ : ∀ i, π.coeff i ≠ 0 → 1 ≤ i ∧ (π.coeff i).totalDegree ≤ 1 + (2 * i - 1) * (h - 1))
    (b : ℕ) : ∀ m, (π ^ b).coeff m ≠ 0 →
      b ≤ m ∧ ((π ^ b).coeff m).totalDegree ≤ b + (2 * m - b) * (h - 1) := by
  induction b with
  | zero =>
    intro m hm
    rw [pow_zero, coeff_one] at hm ⊢
    split_ifs at hm with h0
    · subst h0; simp
    · exact absurd rfl hm
  | succ b ih =>
    intro m hm
    rw [pow_succ, coeff_mul] at hm ⊢
    -- Every nonzero term `(π^b)_i π_j` has `b ≤ i`, `1 ≤ j` and the degree bound.
    have hterm : ∀ x ∈ antidiagonal m, (π ^ b).coeff x.1 * π.coeff x.2 ≠ 0 →
        b + 1 ≤ m ∧ ((π ^ b).coeff x.1 * π.coeff x.2).totalDegree ≤
          b + 1 + (2 * m - (b + 1)) * (h - 1) := by
      intro x hx hne
      have hx := mem_antidiagonal.mp hx
      obtain ⟨hb, hdb⟩ := ih x.1 (left_ne_zero_of_mul hne)
      obtain ⟨hj, hdj⟩ := hπ x.2 (right_ne_zero_of_mul hne)
      refine ⟨by omega, (MvPolynomial.totalDegree_mul _ _).trans ?_⟩
      have harith : (2 * x.1 - b) + (2 * x.2 - 1) = 2 * m - (b + 1) := by omega
      calc _ ≤ b + (2 * x.1 - b) * (h - 1) + (1 + (2 * x.2 - 1) * (h - 1)) := add_le_add hdb hdj
        _ = b + 1 + ((2 * x.1 - b) + (2 * x.2 - 1)) * (h - 1) := by ring
        _ = _ := by rw [harith]
    obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_sum_ne_zero hm
    refine ⟨(hterm x hx hne).1, (MvPolynomial.totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun y hy ↦ ?_)⟩
    by_cases hy0 : (π ^ b).coeff y.1 * π.coeff y.2 = 0
    · rw [hy0, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
    · exact (hterm y hy hy0).2

/-- **Degree of the Hensel numerators** ([CWYZ26, Lemma 3.11]): if `deg A_{a,b} + b ≤ h` for
`b ≤ d`,
`deg s ≤ h - 1`, `d ≤ h` and `1 ≤ h`, then `deg N_n ≤ 1 + (2n - 1)(h - 1)` for `n ≥ 1`. -/
theorem totalDegree_numerators_le (Rs : Polynomial (Polynomial (MvPolynomial σ K)))
    (s : MvPolynomial σ K) {d h : ℕ} (hdh : d ≤ h)
    (hA : ∀ a b, b ≤ d → ((Rs.coeff b).coeff a).totalDegree + b ≤ h)
    (hs : s.totalDegree ≤ h - 1) :
    ∀ n, 1 ≤ n → (numerators Rs s d n).totalDegree ≤ 1 + (2 * n - 1) * (h - 1) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  set prior : ℕ → MvPolynomial σ K := fun i ↦ if i ≤ t then numerators Rs s d i else 0
  set π := positivePrefix prior (t + 1)
  have hπ : ∀ i, π.coeff i ≠ 0 → 1 ≤ i ∧ (π.coeff i).totalDegree ≤ 1 + (2 * i - 1) * (h - 1) := by
    intro i hi
    rw [positivePrefix_coeff] at hi ⊢
    split_ifs at hi ⊢ with hc
    · simp only [prior, show i ≤ t by omega, ↓reduceIte] at hi ⊢
      exact ⟨hc.1, ih i (by omega) hc.1⟩
    · exact absurd rfl hi
  rw [numerators_succ, numeratorStep, MvPolynomial.totalDegree_neg]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun a ha ↦ ?_)
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun b hb ↦ ?_)
  have ha := mem_range.mp ha
  have hb := mem_range.mp hb
  simp only [residualTerm]
  by_cases hz : (π ^ b).coeff (t + 1 - a) = 0
  · rw [hz, mul_zero, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
  obtain ⟨hbm, hdeg⟩ := totalDegree_coeff_pow_le π h hπ b _ hz
  -- `2a + b ≥ 2`: the terms `(0, 0)` and `(0, 1)` vanish.
  have hab : 2 ≤ 2 * a + b := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      rcases Nat.lt_or_ge b 2 with hb2 | hb2
      · interval_cases b
        · simp [coeff_one] at hz
        · exact absurd (by simp [π]) hz
      · omega
    · omega
  have hAb := hA a b (by omega)
  calc ((Rs.coeff b).coeff a * s ^ (2 * a + b - 2) * (π ^ b).coeff (t + 1 - a)).totalDegree
      ≤ (h - b) + (2 * a + b - 2) * (h - 1) + (b + (2 * (t + 1 - a) - b) * (h - 1)) := by
        refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ?_ hdeg)
        refine (MvPolynomial.totalDegree_mul _ _).trans
          (add_le_add (show ((Rs.coeff b).coeff a).totalDegree ≤ h - b by omega) ?_)
        exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hs)
    _ = h + ((2 * a + b - 2) + (2 * (t + 1 - a) - b)) * (h - 1) := by
        have : h - b + b = h := by omega
        rw [add_mul]; omega
    _ ≤ 1 + (2 * (t + 1) - 1) * (h - 1) := by
        rw [show (2 * a + b - 2) + (2 * (t + 1 - a) - b) = 2 * (t + 1) - 2 by omega]
        rcases Nat.eq_zero_or_pos (h - 1) with h1 | h1
        · rw [h1]; simp; omega
        · have : h = (h - 1) + 1 := by omega
          rw [show 2 * (t + 1) - 1 = (2 * (t + 1) - 2) + 1 by omega, add_mul, one_mul]
          omega

end Degrees

end
end LeanVM.Protocol.Whir.AffineCombiner
