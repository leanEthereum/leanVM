import SphincsFors.H0BoundOnce
import SphincsFors.H0Split

/-! Kernel-checkable rational certificates for the split bound of the one-coin H-term. A
certificate has a Poisson table (a rate bound `μ̄ = m / 2^64`, upper bounds `pm[n] / 2^P` for the
Poisson weights `e^{-μ̄} μ̄^n / n!` up to `n1 + 1`, and a geometric bound `T` for
`Σ_{n > n1} e^{-μ̄} μ̄^n / n! n^24`), a list of options (cap `c1`, Chernoff parameter `θ`, threshold
`cthr` and the claimed bounds of the two leaf means and of the H-term), and a chain of budget
intervals, each with an option. Exponentials are bounded by `(1 - u / 2^s)^(-2^s)` (above) and by
partial sums of the series (below), with dyadic rounding. -/

open ENNReal NNReal

namespace SphincsFors.Security.H0

open Concrete Domination ForsPrice

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

/-- `κ n^24` with `κ = 2^-266`. -/
def yQ (n : ℕ) : ℚ := ((n ^ 24 : ℕ) : ℚ) / ((2 ^ 266 : ℕ) : ℚ)

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

/-! ### The Poisson table -/

/-- The Poisson table of a certificate: rate bound `μ̄ = m / 2^64`, weight bounds `pm[n] / 2^P`
for `n ≤ n1 + 1` (`n1 + 2 = pm.length`), `J` series terms for `e^μ̄`, and the tail bound `T`. -/
structure PoisTable where
  m : ℕ
  P : ℕ
  J : ℕ
  pm : List ℕ
  T : ℚ

namespace PoisTable

/-- The rate bound. -/
def mu (t : PoisTable) : ℚ := (t.m : ℚ) / 2 ^ 64

/-- The last index of the explicit part. -/
def n1 (t : PoisTable) : ℕ := t.pm.length - 2

/-- The weight bound at `n`. -/
def pb (t : PoisTable) (n : ℕ) : ℚ := (t.pm.getD n 0 : ℚ) / 2 ^ t.P

/-- The ratio of the geometric tail. -/
def rho (t : PoisTable) : ℚ := t.mu * (((t.n1 + 2) ^ 23 : ℕ) : ℚ) / (((t.n1 + 1) ^ 24 : ℕ) : ℚ)

end PoisTable

/-- The check of a Poisson table for subtree height `b` and `N` signatures. -/
def checkTable (b N : ℕ) (t : PoisTable) : Bool :=
  decide (2 ≤ t.pm.length) &&
    decide ((N : ℚ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) ≤ t.mu) &&
    decide ((2 : ℚ) ^ t.P ≤ (t.pm.getD 0 0 : ℚ) * expLow t.mu t.J t.P) &&
    decide (∀ n < t.pm.length - 1, t.pm.getD n 0 * t.m ≤ t.pm.getD (n + 1) 0 * ((n + 1) * 2 ^ 64)) &&
    decide (t.rho < 1) &&
    decide (t.pb (t.n1 + 1) * (((t.n1 + 1) ^ 24 : ℕ) : ℚ) ≤ t.T * (1 - t.rho))

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

theorem mu_nonneg (t : PoisTable) : (0 : ℚ) ≤ t.mu := by unfold PoisTable.mu; positivity

theorem pb_nonneg (t : PoisTable) (n : ℕ) : (0 : ℚ) ≤ t.pb n := by unfold PoisTable.pb; positivity

theorem checkTable_parts {b N : ℕ} {t : PoisTable} (ht : checkTable b N t = true) :
    2 ≤ t.pm.length ∧ (N : ℚ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) ≤ t.mu ∧
      (2 : ℚ) ^ t.P ≤ (t.pm.getD 0 0 : ℚ) * expLow t.mu t.J t.P ∧
      (∀ n < t.pm.length - 1, t.pm.getD n 0 * t.m ≤ t.pm.getD (n + 1) 0 * ((n + 1) * 2 ^ 64)) ∧
      t.rho < 1 ∧ t.pb (t.n1 + 1) * (((t.n1 + 1) ^ 24 : ℕ) : ℚ) ≤ t.T * (1 - t.rho) := by
  simp only [checkTable, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := ht
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The weight bounds.** -/
theorem table_pmf {b N : ℕ} {t : PoisTable} (ht : checkTable b N t = true) :
    ∀ n, n < t.pm.length → pR (t.mu : ℝ) n ≤ (t.pb n : ℝ)
  | 0, _ => by
      obtain ⟨-, -, h3, -⟩ := checkTable_parts ht
      have hE := expLow_le t.mu t.J t.P (mu_nonneg t)
      have hE1 := one_le_expLow t.mu t.J t.P (mu_nonneg t)
      have hE1' : (1 : ℝ) ≤ (expLow t.mu t.J t.P : ℝ) := by exact_mod_cast hE1
      have h3' : (2 : ℝ) ^ t.P ≤ (t.pm.getD 0 0 : ℝ) * (expLow t.mu t.J t.P : ℝ) := by exact_mod_cast h3
      unfold pR PoisTable.pb
      push_cast
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [Real.exp_neg, le_div_iff₀ (by positivity)]
      have hexp := Real.exp_pos (t.mu : ℝ)
      calc (Real.exp (t.mu : ℝ))⁻¹ * 2 ^ t.P ≤ (Real.exp (t.mu : ℝ))⁻¹ * ((t.pm.getD 0 0 : ℝ) * (expLow t.mu t.J t.P : ℝ)) := by
            gcongr
        _ ≤ (Real.exp (t.mu : ℝ))⁻¹ * ((t.pm.getD 0 0 : ℝ) * Real.exp (t.mu : ℝ)) := by gcongr
        _ = _ := by field_simp
  | n + 1, hn => by
      obtain ⟨-, -, -, h4, -⟩ := checkTable_parts ht
      have ih := table_pmf ht n (by omega)
      have hr := h4 n (by omega)
      have hr' : (t.pm.getD n 0 : ℝ) * t.m ≤ (t.pm.getD (n + 1) 0 : ℝ) * ((n + 1) * 2 ^ 64) := by exact_mod_cast hr
      rw [pR_succ]
      have hmu0 : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast mu_nonneg t
      calc pR (t.mu : ℝ) n * (t.mu : ℝ) / (n + 1) ≤ (t.pb n : ℝ) * (t.mu : ℝ) / (n + 1) := by gcongr
        _ ≤ (t.pb (n + 1) : ℝ) := by
            unfold PoisTable.pb PoisTable.mu
            push_cast
            rw [div_le_iff₀ (by positivity)]
            calc (t.pm.getD n 0 : ℝ) / 2 ^ t.P * ((t.m : ℝ) / 2 ^ 64)
                = (t.pm.getD n 0 : ℝ) * t.m / (2 ^ t.P * 2 ^ 64) := by ring
              _ ≤ (t.pm.getD (n + 1) 0 : ℝ) * ((n + 1) * 2 ^ 64) / (2 ^ t.P * 2 ^ 64) := by gcongr
              _ = _ := by field_simp

/-- `(n + 1)^23 a^24 ≤ (a + 1)^23 n^24` for `1 ≤ a ≤ n`. -/
theorem tail_ratio_nat (a n : ℕ) (han : a ≤ n) : (n + 1) ^ 23 * a ^ 24 ≤ (a + 1) ^ 23 * n ^ 24 := by
  have h1 : (n + 1) * a ≤ (a + 1) * n := by nlinarith
  have h2 : ((n + 1) * a) ^ 23 ≤ ((a + 1) * n) ^ 23 := Nat.pow_le_pow_left h1 23
  calc (n + 1) ^ 23 * a ^ 24 = ((n + 1) * a) ^ 23 * a := by ring
    _ ≤ ((a + 1) * n) ^ 23 * n := Nat.mul_le_mul h2 han
    _ = _ := by ring

/-- **The geometric tail.** -/
theorem table_tail {b N : ℕ} {t : PoisTable} (ht : checkTable b N t = true) :
    ∑' j, poisW (t.mu : ℝ).toNNReal (j + (t.n1 + 1)) * (((j + (t.n1 + 1) : ℕ) : ℝ≥0∞)) ^ 24 ≤
      ENNReal.ofReal (t.T : ℝ) := by
  obtain ⟨hlen, -, -, -, h5, h6⟩ := checkTable_parts ht
  have hmu0 : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast mu_nonneg t
  have hcoe : (((t.mu : ℝ).toNNReal : ℝ≥0) : ℝ) = (t.mu : ℝ) := Real.coe_toNNReal _ hmu0
  set a := t.n1 + 1 with ha
  have ha1 : 1 ≤ a := by omega
  set ρ : ℝ := (t.rho : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]; unfold PoisTable.rho; push_cast; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; exact_mod_cast h5
  set X : ℝ := (t.pb a : ℝ) * (a : ℝ) ^ 24 with hX
  have hX0 : 0 ≤ X := by rw [hX]; have := pb_nonneg t a; positivity
  have hstep : ∀ j : ℕ, pR (t.mu : ℝ) (j + a) * ((j + a : ℕ) : ℝ) ^ 24 ≤ X * ρ ^ j := by
    intro j
    induction j with
    | zero =>
        simp only [zero_add, pow_zero, mul_one]
        rw [hX]
        gcongr
        have hn1 : t.n1 = t.pm.length - 2 := rfl
        exact table_pmf ht a (by omega)
    | succ j ih =>
        rw [show j + 1 + a = (j + a) + 1 by ring, pR_succ]
        set n := j + a with hn
        have hna : a ≤ n := by omega
        have hrat : ((n + 1 : ℕ) : ℝ) ^ 23 * (a : ℝ) ^ 24 ≤ ((a + 1 : ℕ) : ℝ) ^ 23 * (n : ℝ) ^ 24 := by
          exact_mod_cast tail_ratio_nat a n hna
        have hρdef : ρ = (t.mu : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 23 / (a : ℝ) ^ 24 := by
          rw [hρ]; unfold PoisTable.rho
          push_cast
          rw [ha]; push_cast; ring
        have hpos : (0 : ℝ) < (a : ℝ) ^ 24 := by positivity
        have key : (t.mu : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 23 ≤ ρ * (n : ℝ) ^ 24 := by
          rw [hρdef, div_mul_eq_mul_div, le_div_iff₀ hpos]
          calc (t.mu : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 23 * (a : ℝ) ^ 24
              = (t.mu : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 23 * (a : ℝ) ^ 24) := by ring
            _ ≤ (t.mu : ℝ) * (((a + 1 : ℕ) : ℝ) ^ 23 * (n : ℝ) ^ 24) := by gcongr
            _ = _ := by ring
        have hp := pR_nonneg hmu0 n
        calc pR (t.mu : ℝ) n * (t.mu : ℝ) / ((n : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) ^ 24
            = pR (t.mu : ℝ) n * ((t.mu : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 23) := by
              push_cast
              field_simp
          _ ≤ pR (t.mu : ℝ) n * (ρ * (n : ℝ) ^ 24) := by gcongr
          _ = (pR (t.mu : ℝ) n * ((n : ℕ) : ℝ) ^ 24) * ρ := by ring
          _ ≤ X * ρ ^ j * ρ := by gcongr
          _ = X * ρ ^ (j + 1) := by ring
  calc ∑' j, poisW (t.mu : ℝ).toNNReal (j + a) * (((j + a : ℕ) : ℝ≥0∞)) ^ 24
      ≤ ∑' j : ℕ, ENNReal.ofReal X * ENNReal.ofReal ρ ^ j := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [poisW_eq_pR, hcoe, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (pR_nonneg hmu0 _), ← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_mul hX0]
        exact ENNReal.ofReal_le_ofReal (hstep j)
    _ = ENNReal.ofReal (X / (1 - ρ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ hρ0, ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul hX0, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (t.T : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ (by linarith)]
        have h6' : ((t.pb (t.n1 + 1) * (((t.n1 + 1) ^ 24 : ℕ) : ℚ) : ℚ) : ℝ) ≤ ((t.T * (1 - t.rho) : ℚ) : ℝ) := by
          exact_mod_cast h6
        push_cast at h6'
        rw [hX, hρ, ha]
        push_cast
        exact h6'

theorem table_T_nonneg {b N : ℕ} {t : PoisTable} (ht : checkTable b N t = true) : (0 : ℚ) ≤ t.T := by
  obtain ⟨-, -, -, -, h5, h6⟩ := checkTable_parts ht
  have h0 : 0 ≤ t.pb (t.n1 + 1) * (((t.n1 + 1) ^ 24 : ℕ) : ℚ) := by have := pb_nonneg t (t.n1 + 1); positivity
  have h1 : 0 < 1 - t.rho := by linarith
  by_contra hT
  push Not at hT
  have : t.T * (1 - t.rho) < 0 := mul_neg_of_neg_of_pos hT h1
  linarith

/-! ### Evaluating one-leaf Poisson means -/

/-- **Evaluation of a one-leaf Poisson mean.** With weight bounds up to `n1`, a tail bound `T`
for `Σ_{n > n1} p(n) n^24`, a nonnegative `f` below `F` up to `n1` and below `C n^24` beyond,
`E[f(K)] ≤ Σ_{n ≤ n1} p̄(n) F(n) + C T`. -/
theorem poisMean_le_eval (μ : ℝ≥0) (n1 : ℕ) (pb : ℕ → ℝ)
    (hp : ∀ n ≤ n1, pR μ n ≤ pb n) (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∑' j, poisW μ (j + (n1 + 1)) * (((j + (n1 + 1) : ℕ) : ℝ≥0∞)) ^ 24 ≤ ENNReal.ofReal T)
    (f F : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf0 : ∀ n, 0 ≤ f n) (hfF : ∀ n ≤ n1, f n ≤ F n)
    (hfC : ∀ n, n1 < n → f n ≤ C * (n : ℝ) ^ 24) :
    poisMean μ (fun n => ENNReal.ofReal (f n)) ≤
      ENNReal.ofReal (∑ n ∈ Finset.range (n1 + 1), pb n * F n + C * T) := by
  unfold poisMean
  have hsplit : ∑ i ∈ Finset.range (n1 + 1), poisW μ i * ENNReal.ofReal (f i) +
      ∑' i, poisW μ (i + (n1 + 1)) * ENNReal.ofReal (f (i + (n1 + 1))) = ∑' i, poisW μ i * ENNReal.ofReal (f i) :=
    Summable.sum_add_tsum_nat_add' (f := fun i => poisW μ i * ENNReal.ofReal (f i)) (k := n1 + 1) ENNReal.summable
  rw [← hsplit]
  have hpb0 : ∀ n ≤ n1, 0 ≤ pb n := fun n hn => le_trans (pR_nonneg (NNReal.coe_nonneg μ) n) (hp n hn)
  have hhead : ∑ n ∈ Finset.range (n1 + 1), poisW μ n * ENNReal.ofReal (f n) ≤
      ENNReal.ofReal (∑ n ∈ Finset.range (n1 + 1), pb n * F n) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n hn => by
      have hn' : n ≤ n1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact mul_nonneg (hpb0 n hn') (le_trans (hf0 n) (hfF n hn')))]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n ≤ n1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [poisW_eq_pR, ← ENNReal.ofReal_mul (pR_nonneg (NNReal.coe_nonneg μ) n)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (hp n hn') (hfF n hn') (hf0 n) (hpb0 n hn')
  have htail : ∑' j, poisW μ (j + (n1 + 1)) * ENNReal.ofReal (f (j + (n1 + 1))) ≤ ENNReal.ofReal (C * T) := by
    calc ∑' j, poisW μ (j + (n1 + 1)) * ENNReal.ofReal (f (j + (n1 + 1)))
        ≤ ∑' j, ENNReal.ofReal C * (poisW μ (j + (n1 + 1)) * (((j + (n1 + 1) : ℕ) : ℝ≥0∞)) ^ 24) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have h := hfC (j + (n1 + 1)) (by omega)
          calc poisW μ (j + (n1 + 1)) * ENNReal.ofReal (f (j + (n1 + 1)))
              ≤ poisW μ (j + (n1 + 1)) * ENNReal.ofReal (C * ((j + (n1 + 1) : ℕ) : ℝ) ^ 24) := by
                gcongr
            _ = _ := by
                rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
                ring
      _ = ENNReal.ofReal C * ∑' j, poisW μ (j + (n1 + 1)) * (((j + (n1 + 1) : ℕ) : ℝ≥0∞)) ^ 24 :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal T := by gcongr
      _ = ENNReal.ofReal (C * T) := (ENNReal.ofReal_mul hC).symm
  calc ∑ n ∈ Finset.range (n1 + 1), poisW μ n * ENNReal.ofReal (f n) +
        ∑' j, poisW μ (j + (n1 + 1)) * ENNReal.ofReal (f (j + (n1 + 1)))
      ≤ ENNReal.ofReal (∑ n ∈ Finset.range (n1 + 1), pb n * F n) + ENNReal.ofReal (C * T) :=
        add_le_add hhead htail
    _ = _ := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun n hn => by
          have hn' : n ≤ n1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          exact mul_nonneg (hpb0 n hn') (le_trans (hf0 n) (hfF n hn'))) (mul_nonneg hC hT0)]

/-! ### Options -/

/-- An option: cap `c1`, Chernoff parameter `θ`, `s` squarings for the exponential bounds, the
threshold `cthr` it is valid above, a bound `eC` for `e^{θ c1}`, and the claimed bounds `Eh` for
`E[(κ K^24 - c1)^+]`, `Ee` for `E[e^{θ min(κ K^24, c1)}] - 1` and `B` for the H-term. -/
structure OptS where
  c1 : ℚ
  θ : ℚ
  s : ℕ
  cthr : ℚ
  eC : ℚ
  Eh : ℚ
  Ee : ℚ
  B : ℚ

/-- Upper bound for `e^{θ min(κ n^24, c1)}`. -/
def eVal (θ c1 eC : ℚ) (s P n : ℕ) : ℚ :=
  if yQ n < c1 then
    (if θ * yQ n * 2 ^ 20 ≤ 1 then expUp (θ * yQ n) 0 P else expUp (θ * yQ n) s P)
  else eC

/-- The check of an option. -/
def checkOpt (b : ℕ) (t : PoisTable) (o : OptS) : Bool :=
  decide (0 < o.θ) && decide (0 ≤ o.c1) && decide (0 ≤ o.cthr) && decide (o.θ * o.c1 < 2 ^ o.s) &&
    decide (expUp (o.θ * o.c1) o.s t.P ≤ o.eC) &&
    decide (∑ n ∈ Finset.range (t.n1 + 1), t.pb n * max (yQ n - o.c1) 0 + yQ 1 * t.T ≤ o.Eh) &&
    decide (∑ n ∈ Finset.range (t.n1 + 1), t.pb n * (eVal o.θ o.c1 o.eC o.s t.P n - 1) +
      (o.eC - 1) * t.T / (((t.n1 + 1) ^ 24 : ℕ) : ℚ) ≤ o.Ee) &&
    decide ((2 : ℚ) ^ b * o.Eh + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B)

theorem checkOpt_parts {b : ℕ} {t : PoisTable} {o : OptS} (ho : checkOpt b t o = true) :
    0 < o.θ ∧ 0 ≤ o.c1 ∧ 0 ≤ o.cthr ∧ o.θ * o.c1 < 2 ^ o.s ∧ expUp (o.θ * o.c1) o.s t.P ≤ o.eC ∧
      ∑ n ∈ Finset.range (t.n1 + 1), t.pb n * max (yQ n - o.c1) 0 + yQ 1 * t.T ≤ o.Eh ∧
      ∑ n ∈ Finset.range (t.n1 + 1), t.pb n * (eVal o.θ o.c1 o.eC o.s t.P n - 1) +
        (o.eC - 1) * t.T / (((t.n1 + 1) ^ 24 : ℕ) : ℚ) ≤ o.Ee ∧
      (2 : ℚ) ^ b * o.Eh + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B := by
  simp only [checkOpt, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := ho
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem yQ_cast (n : ℕ) : (yQ n : ℝ) = ((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 := by
  unfold yQ
  push_cast
  ring

theorem table_pmf' {b N : ℕ} {t : PoisTable} (ht : checkTable b N t = true) :
    ∀ n ≤ t.n1, pR (((t.mu : ℝ).toNNReal : ℝ≥0) : ℝ) n ≤ (t.pb n : ℝ) := by
  intro n hn
  have hlen := (checkTable_parts ht).1
  have hn1 : t.n1 = t.pm.length - 2 := rfl
  rw [Real.coe_toNNReal _ (by exact_mod_cast mu_nonneg t)]
  exact table_pmf ht n (by omega)

/-- **The mean of the capped excess** is below `Eh`. -/
theorem opt_h_bound {b N : ℕ} {t : PoisTable} {o : OptS} (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) :
    poisMean (t.mu : ℝ).toNNReal (fun n => ENNReal.ofReal (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ))) ≤
      ENNReal.ofReal (o.Eh : ℝ) := by
  obtain ⟨-, hc1, -, -, -, h6, -⟩ := checkOpt_parts ho
  have hc1' : (0 : ℝ) ≤ (o.c1 : ℝ) := by exact_mod_cast hc1
  have hT0 : (0 : ℝ) ≤ (t.T : ℝ) := by exact_mod_cast table_T_nonneg ht
  have hfun : (fun n : ℕ => ENNReal.ofReal (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ))) =
      fun n : ℕ => ENNReal.ofReal (max (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ)) 0) := by
    funext n
    rcases le_total (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ)) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  rw [hfun]
  refine le_trans (poisMean_le_eval _ t.n1 (fun n => (t.pb n : ℝ)) (table_pmf' ht) (t.T : ℝ) hT0 (table_tail ht)
    _ (fun n : ℕ => max (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ)) 0) ((2 : ℝ) ^ 266)⁻¹ (by positivity)
    (fun n => le_max_right _ _) (fun n _ => le_rfl) (fun n _ => ?_)) ?_
  · exact max_le (by linarith) (by positivity)
  · apply ENNReal.ofReal_le_ofReal
    have h6' : (((∑ n ∈ Finset.range (t.n1 + 1), t.pb n * max (yQ n - o.c1) 0 + yQ 1 * t.T) : ℚ) : ℝ) ≤ (o.Eh : ℝ) := by
      exact_mod_cast h6
    push_cast at h6'
    simp only [yQ_cast, Nat.cast_one, one_pow, mul_one] at h6'
    exact h6'

theorem eVal_ge {θ c1 eC : ℚ} {s P : ℕ} (hθ : 0 < θ) (hc1 : 0 ≤ c1) (hs : θ * c1 < 2 ^ s)
    (heC : expUp (θ * c1) s P ≤ eC) (n : ℕ) :
    Real.exp ((θ : ℝ) * min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ)) ≤ (eVal θ c1 eC s P n : ℝ) := by
  have hy0 : 0 ≤ yQ n := by unfold yQ; positivity
  unfold eVal
  split_ifs with h1 h2
  · have hmin : min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ) = (yQ n : ℝ) := by
      rw [← yQ_cast]; exact min_eq_left (by exact_mod_cast h1.le)
    rw [hmin]
    have h := exp_le_expUp (θ * yQ n) 0 P (by positivity) (by
      rw [pow_zero]
      have : θ * yQ n ≤ 1 / 2 ^ 20 := by rw [le_div_iff₀ (by positivity)]; exact h2
      linarith [show (1 : ℚ) / 2 ^ 20 < 1 by norm_num])
    push_cast at h
    exact h
  · have hmin : min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ) = (yQ n : ℝ) := by
      rw [← yQ_cast]; exact min_eq_left (by exact_mod_cast h1.le)
    rw [hmin]
    have h := exp_le_expUp (θ * yQ n) s P (by positivity) (by
      have : θ * yQ n ≤ θ * c1 := by gcongr
      linarith)
    push_cast at h
    exact h
  · have hmin : min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ) = (c1 : ℝ) := by
      rw [← yQ_cast]; exact min_eq_right (by exact_mod_cast not_lt.mp h1)
    rw [hmin]
    have h := exp_le_expUp (θ * c1) s P (by positivity) hs
    have h' : ((expUp (θ * c1) s P : ℚ) : ℝ) ≤ (eC : ℝ) := by exact_mod_cast heC
    push_cast at h
    linarith

/-- **The mean of the capped exponential** is below `1 + Ee`. -/
theorem opt_g_bound {b N : ℕ} {t : PoisTable} {o : OptS} (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) :
    poisMean (t.mu : ℝ).toNNReal
        (fun n => ENNReal.ofReal (Real.exp ((o.θ : ℝ) * min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (o.c1 : ℝ)))) ≤
      ENNReal.ofReal (1 + (o.Ee : ℝ)) := by
  obtain ⟨hθ, hc1, -, hs, heC, -, h7, -⟩ := checkOpt_parts ho
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hc1' : (0 : ℝ) ≤ (o.c1 : ℝ) := by exact_mod_cast hc1
  have hT0 : (0 : ℝ) ≤ (t.T : ℝ) := by exact_mod_cast table_T_nonneg ht
  set e : ℕ → ℝ := fun n => Real.exp ((o.θ : ℝ) * min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (o.c1 : ℝ)) with he
  have he1 : ∀ n, 1 ≤ e n := by
    intro n
    rw [he]
    apply Real.one_le_exp
    have : 0 ≤ min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (o.c1 : ℝ) := le_min (by positivity) hc1'
    positivity
  have heCr : Real.exp ((o.θ : ℝ) * o.c1) ≤ (o.eC : ℝ) := by
    have h := exp_le_expUp (o.θ * o.c1) o.s t.P (by positivity) hs
    have h' : ((expUp (o.θ * o.c1) o.s t.P : ℚ) : ℝ) ≤ (o.eC : ℝ) := by exact_mod_cast heC
    push_cast at h
    linarith
  have heC1 : (1 : ℝ) ≤ (o.eC : ℝ) := le_trans (Real.one_le_exp (by positivity)) heCr
  set a : ℕ := t.n1 + 1 with ha
  have ha0 : (0 : ℝ) < ((a ^ 24 : ℕ) : ℝ) := by positivity
  set C : ℝ := ((o.eC : ℝ) - 1) / ((a ^ 24 : ℕ) : ℝ) with hC
  have hC0 : 0 ≤ C := div_nonneg (by linarith) ha0.le
  have hsplit : poisMean (t.mu : ℝ).toNNReal (fun n => ENNReal.ofReal (e n)) =
      1 + poisMean (t.mu : ℝ).toNNReal (fun n => ENNReal.ofReal (e n - 1)) := by
    unfold poisMean
    have : ∀ n, poisW (t.mu : ℝ).toNNReal n * ENNReal.ofReal (e n) =
        poisW (t.mu : ℝ).toNNReal n * 1 + poisW (t.mu : ℝ).toNNReal n * ENNReal.ofReal (e n - 1) := by
      intro n
      rw [← mul_add, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith [he1 n])]
      congr 2; ring
    simp only [this, ENNReal.tsum_add, mul_one, poisW_tsum]
  have heval := poisMean_le_eval _ t.n1 (fun n => (t.pb n : ℝ)) (table_pmf' ht) (t.T : ℝ) hT0 (table_tail ht)
    (fun n => e n - 1) (fun n => (eVal o.θ o.c1 o.eC o.s t.P n : ℝ) - 1) C hC0
    (fun n => by linarith [he1 n])
    (fun n _ => by linarith [show e n ≤ (eVal o.θ o.c1 o.eC o.s t.P n : ℝ) from eVal_ge hθ hc1 hs heC n])
    (fun n hn => by
      have hmin : e n ≤ Real.exp ((o.θ : ℝ) * o.c1) := by
        rw [he]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hθ'.le
      have hna : ((a ^ 24 : ℕ) : ℝ) ≤ (n : ℝ) ^ 24 := by
        have : a ≤ n := by omega
        exact_mod_cast Nat.pow_le_pow_left this 24
      calc e n - 1 ≤ (o.eC : ℝ) - 1 := by linarith
        _ = C * ((a ^ 24 : ℕ) : ℝ) := by rw [hC]; field_simp
        _ ≤ C * (n : ℝ) ^ 24 := by gcongr)
  have h7' : ((∑ n ∈ Finset.range (t.n1 + 1), t.pb n * (eVal o.θ o.c1 o.eC o.s t.P n - 1) +
      (o.eC - 1) * t.T / (((t.n1 + 1) ^ 24 : ℕ) : ℚ) : ℚ) : ℝ) ≤ (o.Ee : ℝ) := by exact_mod_cast h7
  push_cast at h7'
  have hEe : ∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * ((eVal o.θ o.c1 o.eC o.s t.P n : ℝ) - 1) + C * (t.T : ℝ) ≤
      (o.Ee : ℝ) := by
    rw [hC, ha]
    push_cast
    calc ∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * ((eVal o.θ o.c1 o.eC o.s t.P n : ℝ) - 1) +
          ((o.eC : ℝ) - 1) / ((t.n1 : ℝ) + 1) ^ 24 * (t.T : ℝ)
        = ∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * ((eVal o.θ o.c1 o.eC o.s t.P n : ℝ) - 1) +
          ((o.eC : ℝ) - 1) * (t.T : ℝ) / ((t.n1 : ℝ) + 1) ^ 24 := by ring
      _ ≤ _ := h7'
  have hS0 : 0 ≤ ∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * ((eVal o.θ o.c1 o.eC o.s t.P n : ℝ) - 1) + C * (t.T : ℝ) := by
    refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (by exact_mod_cast pb_nonneg t n) ?_) (mul_nonneg hC0 hT0)
    linarith [show e n ≤ (eVal o.θ o.c1 o.eC o.s t.P n : ℝ) from eVal_ge hθ hc1 hs heC n, he1 n]
  rw [hsplit, ENNReal.ofReal_add zero_le_one (le_trans hS0 hEe), ENNReal.ofReal_one]
  gcongr
  exact le_trans heval (ENNReal.ofReal_le_ofReal hEe)

/-- The Chernoff prefactor at the option's threshold. -/
theorem opt_pref_le {o : OptS} (J P : ℕ) (hθ : 0 < o.θ) (hc : 0 ≤ o.cthr) :
    Real.exp (-(o.θ : ℝ) * o.cthr) / (Real.exp 1 * o.θ) ≤
      ((1 / (expLow (o.θ * o.cthr) J P * eLowQ * o.θ) : ℚ) : ℝ) := by
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hE := expLow_le (o.θ * o.cthr) J P (by positivity)
  have hE1 : (1 : ℝ) ≤ (expLow (o.θ * o.cthr) J P : ℝ) := by exact_mod_cast one_le_expLow (o.θ * o.cthr) J P (by positivity)
  have he := eLowQ_le
  have he0 : (0 : ℝ) < (eLowQ : ℝ) := by unfold eLowQ; norm_num
  push_cast at hE ⊢
  rw [neg_mul, Real.exp_neg, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [one_mul, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
  calc (expLow (o.θ * o.cthr) J P : ℝ) * eLowQ * o.θ ≤ Real.exp ((o.θ : ℝ) * o.cthr) * Real.exp 1 * o.θ := by
        gcongr
    _ = _ := by ring

theorem eVal_one_le {θ c1 eC : ℚ} {s P : ℕ} (hθ : 0 < θ) (hc1 : 0 ≤ c1) (hs : θ * c1 < 2 ^ s)
    (heC : expUp (θ * c1) s P ≤ eC) (n : ℕ) : 1 ≤ eVal θ c1 eC s P n := by
  have h := eVal_ge (P := P) hθ hc1 hs heC n
  have h1 : (1 : ℝ) ≤ Real.exp ((θ : ℝ) * min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ)) := by
    apply Real.one_le_exp
    have hθ' : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hθ.le
    have : 0 ≤ min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (c1 : ℝ) := le_min (by positivity) (by exact_mod_cast hc1)
    positivity
  exact_mod_cast le_trans h1 h

theorem opt_Eh_nonneg {b N : ℕ} {t : PoisTable} {o : OptS} (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) : 0 ≤ o.Eh := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := checkOpt_parts ho
  refine le_trans ?_ h6
  refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (pb_nonneg t n) (le_max_right _ _)) ?_
  have := table_T_nonneg ht
  unfold yQ
  positivity

theorem opt_Ee_nonneg {b N : ℕ} {t : PoisTable} {o : OptS} (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) : 0 ≤ o.Ee := by
  obtain ⟨hθ, hc1, -, hs, heC, -, h7, -⟩ := checkOpt_parts ho
  refine le_trans ?_ h7
  have heC1 : 1 ≤ o.eC := by
    have h := exp_le_expUp (o.θ * o.c1) o.s t.P (by positivity) hs
    have h1 : (1 : ℝ) ≤ Real.exp ((o.θ * o.c1 : ℚ) : ℝ) := Real.one_le_exp (by
      have : (0 : ℚ) ≤ o.θ * o.c1 := by positivity
      exact_mod_cast this)
    have : (1 : ℝ) ≤ (o.eC : ℝ) := le_trans h1 (le_trans h (by exact_mod_cast heC))
    exact_mod_cast this
  refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (pb_nonneg t n) ?_) ?_
  · linarith [eVal_one_le (P := t.P) hθ hc1 hs heC n]
  · have := table_T_nonneg ht
    have : (0 : ℚ) ≤ o.eC - 1 := by linarith
    positivity

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

/-- **One option bounds the H-term** for every threshold above `cthr`, generic in the view type:
`H ≤ B` whenever the rate `N / 2^b + q λ w / 2^b` is below the table rate. -/
theorem hTermO_le_opt {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι) (U : Finset V)
    (hU : UniformIndex idx U) (b N : ℕ) (hcard : Fintype.card ι = 2 ^ b) (t : PoisTable) (o : OptS)
    (ht : checkTable b N t = true) (ho : checkOpt b t o = true) (κ : ℝ≥0∞) (hκ : κ = ((2 : ℝ≥0∞) ^ 266)⁻¹)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (Ns q : ℕ)
    (hrate : (Ns : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b ≤ (t.mu : ℝ))
    (β : ℝ≥0∞) (hβ : β ≠ ⊤) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    hTermO U w lam Ns q (fun d => countPrice idx κ d - β) ≤ ENNReal.ofReal (o.B : ℝ) := by
  obtain ⟨hθ, -, hcthr, -, -, -, -, h8⟩ := checkOpt_parts ho
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hκT : κ ≠ ⊤ := by rw [hκ]; exact ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hκr : κ.toReal = ((2 : ℝ) ^ 266)⁻¹ := by
    rw [hκ, ENNReal.toReal_inv, ENNReal.toReal_pow]; simp
  have hlw : lam * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' hlam hw)
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (lam * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := (t.mu : ℝ).toNNReal with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card ι : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card ι : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (Ns : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, Real.coe_toNNReal _ (by exact_mod_cast mu_nonneg t), hγdef, hαdef]
    push_cast
    calc (Ns : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((lam * w).toReal / 2 ^ b)
        = (Ns : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b := by ring
      _ ≤ _ := hrate
  have hsplit := hTermO_split_le idx U hU κ β hκT hβ (o.cthr : ℝ) (o.c1 : ℝ) (o.θ : ℝ) hβc hθ' w lam hw hlam
    α γ hα hγ Ns q μ hμ
  rw [hκr, hcard] at hsplit
  have hh := opt_h_bound ht ho
  have hg := opt_g_bound ht ho
  have hp := opt_pref_le (o := o) t.J t.P hθ hcthr
  have hEh := opt_Eh_nonneg ht ho
  have hEe := opt_Ee_nonneg ht ho
  set prefQ : ℚ := 1 / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) with hprefQ
  have hpref0 : 0 ≤ prefQ := by
    rw [hprefQ]
    have := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
    have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
    positivity
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  calc hTermO U w lam Ns q (fun d => countPrice idx κ d - β)
      ≤ ((2 ^ b : ℕ) : ℝ≥0∞) * poisMean μ (fun n => ENNReal.ofReal (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24 - (o.c1 : ℝ))) +
          ENNReal.ofReal (Real.exp (-(o.θ : ℝ) * o.cthr) / (Real.exp 1 * o.θ)) *
            poisMean μ (fun n => ENNReal.ofReal (Real.exp ((o.θ : ℝ) *
              min (((2 : ℝ) ^ 266)⁻¹ * (n : ℝ) ^ 24) (o.c1 : ℝ)))) ^ (2 ^ b) := hsplit
    _ ≤ ((2 ^ b : ℕ) : ℝ≥0∞) * ENNReal.ofReal (o.Eh : ℝ) +
          ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by
        refine add_le_add (mul_le_mul_right hh _) (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) ?_)
        refine pow_le_pow_left₀ bot_le ?_ _
        push_cast
        exact hg
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ b * o.Eh) + ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal (sqUp t.P b (1 + o.Ee) : ℝ) := by
        gcongr
        · rw [ENNReal.ofReal_mul (by positivity)]
          push_cast
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        · exact ofReal_pow_le_sqUp t.P b (1 + o.Ee)
    _ = ENNReal.ofReal (((2 : ℚ) ^ b * o.Eh + sqUp t.P b (1 + o.Ee) * prefQ : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_mul (by exact_mod_cast hpref0), ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg (by exact_mod_cast hpref0) (by exact_mod_cast hsq0))]
        push_cast
        ring_nf
    _ ≤ ENNReal.ofReal (o.B : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        have h8' : ((2 : ℚ) ^ b * o.Eh + sqUp t.P b (1 + o.Ee) * prefQ) ≤ o.B := by
          rw [hprefQ, mul_one_div]
          exact h8
        exact_mod_cast h8'

/-! ### The FORS H-term at a general threshold -/

section Fors

variable [Params]

/-- The one-coin rate of the FORS H-term is below the table rate for every budget `q ≤ 2^127`. -/
theorem rate_le_table (b N : ℕ) (t : PoisTable) (ht : checkTable b N t = true) (hN : signatureLimit = N) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * wbarOf q).toReal / 2 ^ b ≤ (t.mu : ℝ) := by
  obtain ⟨-, h2, -⟩ := checkTable_parts ht
  have h2' : (((N : ℚ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) : ℚ) : ℝ) ≤ (t.mu : ℝ) := by
    exact_mod_cast h2
  push_cast at h2'
  have hD := dReal_pos q hq
  have hlw : (landing * wbarOf q).toReal = 1 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) := by
    rw [landing_eq, wbar_eq q hq, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
    field_simp
  rw [hlw, hN]
  have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have hqD : (q : ℝ) * (1 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ≤ 2 ^ 127 / (2 ^ 127 - 2 ^ 32) := by
    rw [mul_one_div, div_le_div_iff₀ hD (by norm_num)]
    nlinarith
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  calc (N : ℝ) / 2 ^ b + (q : ℝ) * (1 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) / 2 ^ b
      ≤ (N : ℝ) / 2 ^ b + 2 ^ 127 / (2 ^ 127 - 2 ^ 32) / 2 ^ b := by gcongr
    _ = (N : ℝ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) := by rw [div_div]
    _ ≤ _ := h2'

/-- **General threshold.** A checked table and option bound the one-coin FORS H-term at every
budget `q ≤ 2^127` and every finite threshold `β ≥ cthr`: `H ≤ B`. -/
theorem hTermO_fors_le_opt (b N : ℕ) (t : PoisTable) (o : OptS) (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ)
    (hq : 2 * q ≤ 2 ^ 128) (β : ℝ≥0∞) (hβ : β ≠ ⊤) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q
        (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) ≤
      ENNReal.ofReal (o.B : ℝ) := by
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  exact hTermO_le_opt (Prod.fst : View → Fin (2 ^ subtreeHeight)) Finset.univ uniformIndex_univ b N
    (by rw [Fintype.card_fin, hb]) t o ht ho kappa rfl (wbarOf q) landing (fair_of q hq).le_one
    ForsPotential.landing_le_one signatureLimit q (rate_le_table b N t ht hN q hq127) β hβ hβc

/-- The check of a general-threshold bound: a table and one option. -/
def checkThreshS (b N : ℕ) (t : PoisTable) (o : OptS) : Bool := checkTable b N t && checkOpt b t o

/-- **General threshold**, from one Bool check: for a rational threshold `cthr` (any finite
`β ≥ cthr`), the one-coin FORS H-term at every budget `q ≤ 2^127` is at most `B`. -/
theorem hTermO_fors_le_of_check (b N : ℕ) (t : PoisTable) (o : OptS) (hc : checkThreshS b N t o = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ) (hq : 2 * q ≤ 2 ^ 128) (β : ℝ≥0∞)
    (hβ : β ≠ ⊤) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q
        (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) ≤
      ENNReal.ofReal (o.B : ℝ) := by
  simp only [checkThreshS, Bool.and_eq_true] at hc
  exact hTermO_fors_le_opt b N t o hc.1 hc.2 hb hN q hq β hβ hβc

theorem opt_B_nonneg {b N : ℕ} {t : PoisTable} {o : OptS} (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) : 0 ≤ o.B := by
  obtain ⟨hθ, -, hcthr, -, -, -, -, h8⟩ := checkOpt_parts ho
  have hEh := opt_Eh_nonneg ht ho
  have hEe := opt_Ee_nonneg ht ho
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  have hE := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
  have he : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
  refine le_trans ?_ h8
  positivity

/-! ### Covers of budget intervals -/

/-- A cover entry: budgets `[qa, qb]` and the index of its option. -/
abbrev EntryS := ℕ × ℕ × ℕ

/-- A split-bound certificate: the Poisson table, the options and the chain of entries. -/
structure CoverS where
  tab : PoisTable
  opts : List OptS
  entries : List EntryS

end Fors

end SphincsFors.Security.H0
