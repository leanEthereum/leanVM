import FORS.Base.Split

/-! Rational bounds for the kernel-checkable certificates of the split bound of the one-coin H-term
(the FORS certificates are in `CoverBound/HTermCertificate.lean`): dyadic rounding, exponentials
bounded by `(1 - u / 2^s)^(-2^s)` (above) and by partial sums of the series (below), and the
Poisson weight `e^{-μ} μ^n / n!`. -/

open ENNReal NNReal

namespace FORS.Base.H0

open Domination

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### Rounding and exponential bounds -/

/-- Round down to a multiple of `2^-P`. -/
def rdown (x : ℚ) (P : ℕ) : ℚ := ((⌊x * 2 ^ P⌋ : ℤ) : ℚ) / 2 ^ P

/-- Round up to a multiple of `2^-P`. -/
def rup (x : ℚ) (P : ℕ) : ℚ := ((⌈x * 2 ^ P⌉ : ℤ) : ℚ) / 2 ^ P

/-- Iterated squaring, rounded up: an upper bound for `x^(2^s)`. -/
def sqUp (P : ℕ) : ℕ → ℚ → ℚ
  | 0, x => x
  | s + 1, x => sqUp P s (rup (x * x) P)

/-- Upper bound for `e^u`: `(1 - u / 2^s)^(-2^s)`, rounded up. -/
def expUp (u : ℚ) (s P : ℕ) : ℚ := sqUp P s (rup (1 / (1 - u / 2 ^ s)) P)

/-- Partial sums of the exponential series with rounded-down terms. -/
def expLowGo (u : ℚ) (P : ℕ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, t, acc => acc + t
  | r + 1, j, t, acc => expLowGo u P r (j + 1) (rdown (t * u / (j + 1)) P) (acc + t)

/-- Lower bound for `e^u` from `J + 1` terms of the series. -/
def expLow (u : ℚ) (J P : ℕ) : ℚ := expLowGo u P J 0 1 0

/-- A lower bound for `e`. -/
def eLowQ : ℚ := 27182818283 / 10 ^ 10

theorem rdown_le (x : ℚ) (P : ℕ) : rdown x P ≤ x := by
  unfold rdown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem rdown_nonneg {x : ℚ} (hx : 0 ≤ x) (P : ℕ) : 0 ≤ rdown x P := by
  unfold rdown
  have : (0 : ℤ) ≤ ⌊x * 2 ^ P⌋ := Int.floor_nonneg.mpr (by positivity)
  positivity

theorem le_rup (x : ℚ) (P : ℕ) : x ≤ rup x P := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem sqUp_ge (P : ℕ) : ∀ (s : ℕ) (x : ℚ) (y : ℝ), 0 ≤ y → y ≤ x → y ^ (2 ^ s) ≤ (sqUp P s x : ℝ)
  | 0, x, y, _, h => by simpa [sqUp] using h
  | s + 1, x, y, hy, h => by
      simp only [sqUp]
      have h2 : y ^ 2 ≤ ((rup (x * x) P : ℚ) : ℝ) := by
        calc y ^ 2 ≤ (x : ℝ) * x := by nlinarith
          _ = ((x * x : ℚ) : ℝ) := by push_cast; ring
          _ ≤ _ := by exact_mod_cast le_rup (x * x) P
      have := sqUp_ge P s (rup (x * x) P) (y ^ 2) (by positivity) h2
      rw [← pow_mul, ← pow_succ'] at this
      exact this

theorem exp_le_expUp (u : ℚ) (s P : ℕ) (hu : 0 ≤ u) (hus : u < 2 ^ s) : Real.exp u ≤ (expUp u s P : ℝ) := by
  set v : ℝ := (u : ℝ) / 2 ^ s with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v < 1 := by
    rw [hv, div_lt_one (by positivity)]
    exact_mod_cast hus
  have hexpv : Real.exp v ≤ 1 / (1 - v) := by
    have h := Real.one_sub_le_exp_neg v
    rw [le_div_iff₀ (by linarith)]
    calc Real.exp v * (1 - v) ≤ Real.exp v * Real.exp (-v) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hround : (1 / (1 - v) : ℝ) ≤ ((rup (1 / (1 - u / 2 ^ s)) P : ℚ) : ℝ) := by
    have := le_rup (1 / (1 - u / 2 ^ s)) P
    have h' : ((1 / (1 - u / 2 ^ s) : ℚ) : ℝ) ≤ ((rup (1 / (1 - u / 2 ^ s)) P : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have h := sqUp_ge P s _ (Real.exp v) (Real.exp_pos v).le (le_trans hexpv hround)
  rw [← Real.exp_nat_mul] at h
  unfold expUp
  convert h using 2
  rw [hv]
  push_cast
  field_simp

theorem expLowGo_le (u : ℚ) (P : ℕ) (hu : 0 ≤ u) :
    ∀ (r j : ℕ) (t acc : ℚ), (t : ℝ) ≤ (u : ℝ) ^ j / j.factorial →
      (acc : ℝ) ≤ ∑ i ∈ Finset.range j, (u : ℝ) ^ i / i.factorial →
      (expLowGo u P r j t acc : ℝ) ≤ ∑ i ∈ Finset.range (j + r + 1), (u : ℝ) ^ i / i.factorial
  | 0, j, t, acc, ht, hacc => by
      simp only [expLowGo, add_zero]
      push_cast
      rw [Finset.sum_range_succ]
      linarith
  | r + 1, j, t, acc, ht, hacc => by
      simp only [expLowGo]
      have ht' : ((rdown (t * u / (j + 1)) P : ℚ) : ℝ) ≤ (u : ℝ) ^ (j + 1) / (j + 1).factorial := by
        have h1 : ((rdown (t * u / (j + 1)) P : ℚ) : ℝ) ≤ ((t * u / (j + 1) : ℚ) : ℝ) := by
          exact_mod_cast rdown_le _ P
        refine le_trans h1 ?_
        push_cast
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
        have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
        rw [div_le_div_iff₀ hj (by positivity)]
        calc (t : ℝ) * u * (((j : ℝ) + 1) * j.factorial) = ((t : ℝ) * j.factorial) * u * ((j : ℝ) + 1) := by ring
          _ ≤ ((u : ℝ) ^ j) * u * ((j : ℝ) + 1) := by
              gcongr
              rwa [le_div_iff₀ hf] at ht
          _ = _ := by ring
      have hacc' : ((acc + t : ℚ) : ℝ) ≤ ∑ i ∈ Finset.range (j + 1), (u : ℝ) ^ i / i.factorial := by
        push_cast
        rw [Finset.sum_range_succ]
        linarith
      have h := expLowGo_le u P hu r (j + 1) _ _ ht' hacc'
      rw [show j + 1 + r + 1 = j + (r + 1) + 1 by ring] at h
      exact h

theorem expLow_le (u : ℚ) (J P : ℕ) (hu : 0 ≤ u) : (expLow u J P : ℝ) ≤ Real.exp u := by
  have h := expLowGo_le u P hu J 0 1 0 (by simp) (by simp)
  refine le_trans h ?_
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hu) _

theorem expLowGo_ge (u : ℚ) (P : ℕ) (hu : 0 ≤ u) :
    ∀ (r j : ℕ) (t acc : ℚ), 0 ≤ t → acc + t ≤ expLowGo u P r j t acc
  | 0, _, _, _, _ => le_rfl
  | r + 1, j, t, acc, ht => by
      simp only [expLowGo]
      have ht' : 0 ≤ rdown (t * u / (j + 1)) P := rdown_nonneg (by positivity) P
      have := expLowGo_ge u P hu r (j + 1) _ (acc + t) ht'
      linarith

theorem one_le_expLow (u : ℚ) (J P : ℕ) (hu : 0 ≤ u) : 1 ≤ expLow u J P := by
  have := expLowGo_ge u P hu J 0 1 0 zero_le_one
  unfold expLow
  linarith

theorem eLowQ_le : (eLowQ : ℝ) ≤ Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  unfold eLowQ
  push_cast
  norm_num at h ⊢
  linarith

/-! ### The Poisson weight -/

/-- The Poisson weight as a real number. -/
noncomputable def pR (μ : ℝ) (n : ℕ) : ℝ := Real.exp (-μ) * μ ^ n / n.factorial

theorem pR_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : 0 ≤ pR μ n := by unfold pR; positivity

theorem pR_succ (μ : ℝ) (n : ℕ) : pR μ (n + 1) = pR μ n * μ / (n + 1) := by
  unfold pR
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem poisW_eq_pR (μ : ℝ≥0) (n : ℕ) : poisW μ n = ENNReal.ofReal (pR μ n) := rfl

/-! ### Options -/

/-- `ofReal x ^ (2^b) ≤ ofReal (sqUp P b x)`. -/
theorem ofReal_pow_le_sqUp (P b : ℕ) (x : ℚ) :
    ENNReal.ofReal (x : ℝ) ^ (2 ^ b) ≤ ENNReal.ofReal (sqUp P b x : ℝ) := by
  rcases le_total 0 x with hx | hx
  · have hx' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    rw [← ENNReal.ofReal_pow hx']
    exact ENNReal.ofReal_le_ofReal (sqUp_ge P b x (x : ℝ) hx' le_rfl)
  · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast hx
    rw [ENNReal.ofReal_of_nonpos hx', zero_pow (by positivity)]
    exact bot_le

end FORS.Base.H0
