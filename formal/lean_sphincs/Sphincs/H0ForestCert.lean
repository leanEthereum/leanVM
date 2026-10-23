import Sphincs.H0MomCert
import Sphincs.H0Forest

/-! **Kernel-checkable certificates for the forest H-term.** A Poisson table (rate bound
`μ̄ = m / 2^64`, weight bounds `pm[n] / 2^P` up to `n1 + 1`, geometric tail with ratio
`r = μ̄ / (n1 + 2)`), and per option the leaf tables `ḡ`, `h̄` (convex, increasing, extended
linearly beyond `n1`), which dominate the averaged split terms through the moment bounds. -/

open ENNReal NNReal

namespace Sphincs.Security.H0

open Concrete SphincsFors.Security.H0 SphincsFors.Security.Domination H0Avg

set_option linter.unusedSectionVars false

/-! ### The Poisson table -/

/-- A Poisson table: rate bound `m / 2^64`, weight bounds `pm[n] / 2^P` for `n ≤ n1 + 1`, and `J`
series terms for `e^μ̄`. -/
structure PoisT where
  m : ℕ
  P : ℕ
  J : ℕ
  pm : List ℕ

namespace PoisT

def mu (t : PoisT) : ℚ := (t.m : ℚ) / 2 ^ 64
def n1 (t : PoisT) : ℕ := t.pm.length - 2
def pb (t : PoisT) (n : ℕ) : ℚ := (t.pm.getD n 0 : ℚ) / 2 ^ t.P
def r (t : PoisT) : ℚ := t.mu / (t.n1 + 2)

end PoisT

/-- The check of a Poisson table. -/
def checkPT (t : PoisT) : Bool :=
  decide (2 ≤ t.pm.length) &&
    decide ((2 : ℚ) ^ t.P ≤ (t.pm.getD 0 0 : ℚ) * expLow t.mu t.J t.P) &&
    decide (∀ n < t.pm.length - 1, t.pm.getD n 0 * t.m ≤ t.pm.getD (n + 1) 0 * ((n + 1) * 2 ^ 64)) &&
    decide (t.r < 1)

theorem PoisT.mu_nonneg (t : PoisT) : (0 : ℚ) ≤ t.mu := by unfold PoisT.mu; positivity
theorem PoisT.pb_nonneg (t : PoisT) (n : ℕ) : (0 : ℚ) ≤ t.pb n := by unfold PoisT.pb; positivity
theorem PoisT.r_nonneg (t : PoisT) : (0 : ℚ) ≤ t.r := by unfold PoisT.r; have := t.mu_nonneg; positivity

theorem checkPT_parts {t : PoisT} (ht : checkPT t = true) :
    2 ≤ t.pm.length ∧ (2 : ℚ) ^ t.P ≤ (t.pm.getD 0 0 : ℚ) * expLow t.mu t.J t.P ∧
      (∀ n < t.pm.length - 1, t.pm.getD n 0 * t.m ≤ t.pm.getD (n + 1) 0 * ((n + 1) * 2 ^ 64)) ∧ t.r < 1 := by
  simp only [checkPT, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
  exact ⟨h1, h2, h3, h4⟩

/-- **The weight bounds.** -/
theorem PoisT.pmf {t : PoisT} (ht : checkPT t = true) :
    ∀ n, n < t.pm.length → pR (t.mu : ℝ) n ≤ (t.pb n : ℝ)
  | 0, _ => by
      obtain ⟨-, h3, -⟩ := checkPT_parts ht
      have hE := expLow_le t.mu t.J t.P t.mu_nonneg
      have hE1' : (1 : ℝ) ≤ (expLow t.mu t.J t.P : ℝ) := by exact_mod_cast one_le_expLow t.mu t.J t.P t.mu_nonneg
      have h3' : (2 : ℝ) ^ t.P ≤ (t.pm.getD 0 0 : ℝ) * (expLow t.mu t.J t.P : ℝ) := by exact_mod_cast h3
      unfold pR PoisT.pb
      push_cast
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [Real.exp_neg, le_div_iff₀ (by positivity)]
      have hexp := Real.exp_pos (t.mu : ℝ)
      calc (Real.exp (t.mu : ℝ))⁻¹ * 2 ^ t.P ≤ (Real.exp (t.mu : ℝ))⁻¹ * ((t.pm.getD 0 0 : ℝ) * (expLow t.mu t.J t.P : ℝ)) := by
            gcongr
        _ ≤ (Real.exp (t.mu : ℝ))⁻¹ * ((t.pm.getD 0 0 : ℝ) * Real.exp (t.mu : ℝ)) := by gcongr
        _ = _ := by field_simp
  | n + 1, hn => by
      obtain ⟨-, -, h4, -⟩ := checkPT_parts ht
      have ih := PoisT.pmf ht n (by omega)
      have hr := h4 n (by omega)
      have hr' : (t.pm.getD n 0 : ℝ) * t.m ≤ (t.pm.getD (n + 1) 0 : ℝ) * ((n + 1) * 2 ^ 64) := by exact_mod_cast hr
      rw [pR_succ]
      have hmu0 : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast t.mu_nonneg
      calc pR (t.mu : ℝ) n * (t.mu : ℝ) / (n + 1) ≤ (t.pb n : ℝ) * (t.mu : ℝ) / (n + 1) := by gcongr
        _ ≤ (t.pb (n + 1) : ℝ) := by
            unfold PoisT.pb PoisT.mu
            push_cast
            rw [div_le_iff₀ (by positivity)]
            calc (t.pm.getD n 0 : ℝ) / 2 ^ t.P * ((t.m : ℝ) / 2 ^ 64)
                = (t.pm.getD n 0 : ℝ) * t.m / (2 ^ t.P * 2 ^ 64) := by ring
              _ ≤ (t.pm.getD (n + 1) 0 : ℝ) * ((n + 1) * 2 ^ 64) / (2 ^ t.P * 2 ^ 64) := by gcongr
              _ = _ := by field_simp

/-- **The geometric tail.** -/
theorem PoisT.tail {t : PoisT} (ht : checkPT t = true) (k : ℕ) :
    pR (t.mu : ℝ) (t.n1 + 1 + k) ≤ (t.pb (t.n1 + 1) : ℝ) * (t.r : ℝ) ^ k := by
  obtain ⟨h1, -, -, -⟩ := checkPT_parts ht
  induction k with
  | zero =>
      rw [add_zero, pow_zero, mul_one]
      exact PoisT.pmf ht _ (by unfold PoisT.n1; omega)
  | succ k ih =>
      rw [show t.n1 + 1 + (k + 1) = (t.n1 + 1 + k) + 1 by ring, pR_succ, pow_succ, ← mul_assoc]
      have hmu0 : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast t.mu_nonneg
      have hr0 : (0 : ℝ) ≤ (t.r : ℝ) := by exact_mod_cast t.r_nonneg
      have hratio : (t.mu : ℝ) / ((t.n1 + 1 + k : ℕ) + 1 : ℝ) ≤ (t.r : ℝ) := by
        unfold PoisT.r
        push_cast
        apply div_le_div_of_nonneg_left hmu0 (by positivity)
        push_cast
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      calc pR (t.mu : ℝ) (t.n1 + 1 + k) * (t.mu : ℝ) / (((t.n1 + 1 + k : ℕ) : ℝ) + 1)
          = pR (t.mu : ℝ) (t.n1 + 1 + k) * ((t.mu : ℝ) / (((t.n1 + 1 + k : ℕ) : ℝ) + 1)) := by ring
        _ ≤ ((t.pb (t.n1 + 1) : ℝ) * (t.r : ℝ) ^ k) * (t.r : ℝ) := by
            have hratio' : (t.mu : ℝ) / (((t.n1 + 1 + k : ℕ) : ℝ) + 1) ≤ (t.r : ℝ) := by exact_mod_cast hratio
            exact mul_le_mul ih hratio' (div_nonneg hmu0 (by positivity))
              (mul_nonneg (by exact_mod_cast t.pb_nonneg _) (pow_nonneg hr0 k))
        _ = _ := by ring

/-! ### Poisson means of tables with linear extensions -/

theorem tsum_geom_lin (r a J : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => r ^ k * (a + J * ((k : ℝ) + 1))) (a / (1 - r) + J / (1 - r) ^ 2) := by
  have h1 : HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun k : ℕ => (k : ℝ) * r ^ k) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have h := (h1.mul_left a).add ((h2.add h1).mul_left J)
  have hfun : (fun k : ℕ => r ^ k * (a + J * ((k : ℝ) + 1))) = fun b : ℕ => a * r ^ b + J * ((b : ℝ) * r ^ b + r ^ b) := by
    funext k; ring
  have hne : (1 - r) ≠ 0 := by linarith
  have hval : a / (1 - r) + J / (1 - r) ^ 2 = a * (1 - r)⁻¹ + J * (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
    field_simp
    ring
  rw [hfun, hval]
  exact h


/-! ### Leaf tables with linear extensions -/

/-- A table extended linearly with slope `J` beyond its last entry. -/
def leafQ (tab : List ℚ) (J : ℚ) (n : ℕ) : ℚ :=
  if n < tab.length then tab.getD n 0 else tab.getD (tab.length - 1) 0 + J * ((n - (tab.length - 1) : ℕ) : ℚ)

/-- Nonnegative, increasing and convex, with an extension slope at least the last increment. -/
def checkLeaf (tab : List ℚ) (J : ℚ) : Bool :=
  decide (2 ≤ tab.length) && decide (0 ≤ tab.getD 0 0) &&
    decide (∀ n < tab.length - 1, tab.getD n 0 ≤ tab.getD (n + 1) 0) &&
    decide (∀ n < tab.length - 2, 2 * tab.getD (n + 1) 0 ≤ tab.getD n 0 + tab.getD (n + 2) 0) &&
    decide (tab.getD (tab.length - 1) 0 - tab.getD (tab.length - 2) 0 ≤ J)

theorem checkLeaf_parts {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) :
    2 ≤ tab.length ∧ 0 ≤ tab.getD 0 0 ∧ (∀ n < tab.length - 1, tab.getD n 0 ≤ tab.getD (n + 1) 0) ∧
      (∀ n < tab.length - 2, 2 * tab.getD (n + 1) 0 ≤ tab.getD n 0 + tab.getD (n + 2) 0) ∧
      tab.getD (tab.length - 1) 0 - tab.getD (tab.length - 2) 0 ≤ J := by
  simp only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The increments of an extended table. -/
theorem leafQ_succ_sub {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) (n : ℕ) :
    leafQ tab J (n + 1) - leafQ tab J n =
      if n + 1 < tab.length then tab.getD (n + 1) 0 - tab.getD n 0 else J := by
  obtain ⟨hl, -⟩ := checkLeaf_parts h
  unfold leafQ
  by_cases h1 : n + 1 < tab.length
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h0 : n < tab.length
    · rw [ite_eq_left h0]
      have hn : n = tab.length - 1 := by omega
      subst hn
      have : tab.length - 1 + 1 - (tab.length - 1) = 1 := by omega
      rw [this]
      push_cast
      ring
    · rw [ite_eq_right h0]
      have : n + 1 - (tab.length - 1) = (n - (tab.length - 1)) + 1 := by omega
      rw [this]
      push_cast
      ring

theorem leaf_incr_mono {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) (n : ℕ) :
    leafQ tab J (n + 1) - leafQ tab J n ≤ leafQ tab J (n + 2) - leafQ tab J (n + 1) := by
  obtain ⟨hl, -, -, hconv, hJ⟩ := checkLeaf_parts h
  rw [leafQ_succ_sub h n, leafQ_succ_sub h (n + 1)]
  by_cases h2 : n + 1 + 1 < tab.length
  · rw [ite_eq_left (by omega), ite_eq_left h2]
    have := hconv n (by omega)
    linarith
  · rw [ite_eq_right h2]
    by_cases h1 : n + 1 < tab.length
    · rw [ite_eq_left h1]
      have hn : n = tab.length - 2 := by omega
      subst hn
      have e1 : tab.length - 2 + 1 = tab.length - 1 := by omega
      rw [e1]
      exact hJ
    · rw [ite_eq_right h1]

theorem leaf_incr_nonneg {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) (n : ℕ) :
    0 ≤ leafQ tab J (n + 1) - leafQ tab J n := by
  obtain ⟨hl, -, hmono, -, hJ⟩ := checkLeaf_parts h
  have hJ0 : 0 ≤ J := le_trans (by have := hmono (tab.length - 2) (by omega); rw [show tab.length - 2 + 1 = tab.length - 1 by omega] at this; linarith) hJ
  rw [leafQ_succ_sub h n]
  split_ifs with h1
  · have := hmono n (by omega); linarith
  · exact hJ0

theorem leafQ_nonneg {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) : ∀ n, 0 ≤ leafQ tab J n
  | 0 => by
      obtain ⟨hl, h0, -⟩ := checkLeaf_parts h
      unfold leafQ
      rw [ite_eq_left (by omega)]
      exact h0
  | n + 1 => by
      have := leaf_incr_nonneg h n
      have := leafQ_nonneg h n
      linarith

theorem leafQ_mono {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) : Monotone (leafQ tab J) :=
  monotone_nat_of_le_succ fun n => by have := leaf_incr_nonneg h n; linarith

/-- **Checked tables are separable good leaves.** -/
theorem leaf_sepGood {tab : List ℚ} {J : ℚ} (h : checkLeaf tab J = true) :
    SepGood (fun n => ENNReal.ofReal (leafQ tab J n : ℝ)) where
  mono := fun a b hab => ENNReal.ofReal_le_ofReal (by exact_mod_cast leafQ_mono h hab)
  convex := by
    intro n
    have hc := leaf_incr_mono h n
    have h0 := leafQ_nonneg h n
    have h1 := leafQ_nonneg h (n + 1)
    have h2 := leafQ_nonneg h (n + 2)
    rw [← ENNReal.ofReal_add (by exact_mod_cast h1) (by exact_mod_cast h1),
      ← ENNReal.ofReal_add (by exact_mod_cast h2) (by exact_mod_cast h0)]
    apply ENNReal.ofReal_le_ofReal
    have : (leafQ tab J (n + 1) + leafQ tab J (n + 1) : ℚ) ≤ leafQ tab J (n + 2) + leafQ tab J n := by linarith
    exact_mod_cast this
  growth := by
    obtain ⟨hl, -, hmono, -, hJ⟩ := checkLeaf_parts h
    set T := tab.getD (tab.length - 1) 0
    have hJ0 : 0 ≤ J := le_trans (by have := hmono (tab.length - 2) (by omega); rw [show tab.length - 2 + 1 = tab.length - 1 by omega] at this; linarith) hJ
    have hT0 : 0 ≤ T := by
      have := leafQ_nonneg h (tab.length - 1)
      unfold leafQ at this
      rwa [ite_eq_left (by omega)] at this
    refine ⟨⟨((T + J : ℚ) : ℝ), by positivity⟩, fun n => ?_⟩
    have hle : leafQ tab J n ≤ (T + J) * ((n : ℚ) + 1) := by
      by_cases hn : n < tab.length
      · have hm := leafQ_mono h (show n ≤ tab.length - 1 by omega)
        have hT : leafQ tab J (tab.length - 1) = T := by unfold leafQ; rw [ite_eq_left (by omega)]
        rw [hT] at hm
        nlinarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
      · unfold leafQ
        rw [ite_eq_right hn]
        have hk : ((n - (tab.length - 1) : ℕ) : ℚ) ≤ (n : ℚ) + 1 := by
          have : n - (tab.length - 1) ≤ n + 1 := by omega
          exact_mod_cast this
        nlinarith
    have h2 : ((n : ℚ) + 1) ≤ 2 ^ n := by
      have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ENNReal.ofReal (leafQ tab J n : ℝ) ≤ ENNReal.ofReal (((T + J : ℚ) : ℝ) * 2 ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have : leafQ tab J n ≤ (T + J) * 2 ^ n := le_trans hle (mul_le_mul_of_nonneg_left h2 (by linarith))
          exact_mod_cast this
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_eq_coe_nnreal (by positivity)]
          rfl

/-- **Poisson means of extended tables.** -/
theorem poisMean_leaf_le {t : PoisT} (ht : checkPT t = true) {tab : List ℚ} {J : ℚ} (hleaf : checkLeaf tab J = true)
    (hlen : tab.length = t.n1 + 1) :
    poisMean ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ (fun n => ENNReal.ofReal (leafQ tab J n : ℝ)) ≤
      ENNReal.ofReal ((((List.range (t.n1 + 1)).map fun n => t.pb n * tab.getD n 0).sum +
        t.pb (t.n1 + 1) * (tab.getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2) : ℚ) : ℝ) := by
  obtain ⟨hpm2, -, -, hr1⟩ := checkPT_parts ht
  obtain ⟨hl, -, hmono, -, hJ⟩ := checkLeaf_parts hleaf
  have hJ0 : 0 ≤ J := le_trans (by have := hmono (tab.length - 2) (by omega); rw [show tab.length - 2 + 1 = tab.length - 1 by omega] at this; linarith) hJ
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμ
  have hpm : t.pm.length = t.n1 + 2 := by unfold PoisT.n1; omega
  unfold poisMean
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun i => poisW μ i * ENNReal.ofReal (leafQ tab J i : ℝ))
    (k := t.n1 + 1) ENNReal.summable
  rw [← hsplit]
  have hr0 : (0 : ℝ) ≤ (t.r : ℝ) := by exact_mod_cast t.r_nonneg
  have hr1' : (t.r : ℝ) < 1 := by exact_mod_cast hr1
  -- the head
  have htab0 : ∀ n, n < t.n1 + 1 → (0 : ℝ) ≤ (tab.getD n 0 : ℝ) := by
    intro n hn
    have := leafQ_nonneg hleaf n
    unfold leafQ at this
    rw [ite_eq_left (by omega)] at this
    exact_mod_cast this
  have hhead : ∑ i ∈ Finset.range (t.n1 + 1), poisW μ i * ENNReal.ofReal (leafQ tab J i : ℝ) ≤
      ENNReal.ofReal (∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * (tab.getD n 0 : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n hn => mul_nonneg (by exact_mod_cast t.pb_nonneg n)
      (htab0 n (Finset.mem_range.1 hn)))]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n < t.n1 + 1 := Finset.mem_range.1 hn
    have hlq : leafQ tab J n = tab.getD n 0 := by unfold leafQ; rw [ite_eq_left (by omega)]
    rw [poisW_eq_pR, ← ENNReal.ofReal_mul (pR_nonneg (NNReal.coe_nonneg μ) n), hlq]
    apply ENNReal.ofReal_le_ofReal
    have hp := t.pmf ht n (by omega)
    have hv : (0 : ℝ) ≤ (tab.getD n 0 : ℝ) := by
      have := leafQ_nonneg hleaf n; rw [hlq] at this; exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hp hv
  -- the tail
  set T := tab.getD t.n1 0
  have htail : ∑' j, poisW μ (j + (t.n1 + 1)) * ENNReal.ofReal (leafQ tab J (j + (t.n1 + 1)) : ℝ) ≤
      ENNReal.ofReal ((t.pb (t.n1 + 1) : ℝ) * ((T : ℝ) / (1 - (t.r : ℝ)) + (J : ℝ) / (1 - (t.r : ℝ)) ^ 2)) := by
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := by
      have := leafQ_nonneg hleaf t.n1
      unfold leafQ at this
      rw [ite_eq_left (by omega)] at this
      exact_mod_cast this
    have hpt : ∀ j : ℕ, poisW μ (j + (t.n1 + 1)) * ENNReal.ofReal (leafQ tab J (j + (t.n1 + 1)) : ℝ) ≤
        ENNReal.ofReal ((t.pb (t.n1 + 1) : ℝ) * ((t.r : ℝ) ^ j * ((T : ℝ) + (J : ℝ) * ((j : ℝ) + 1)))) := by
      intro j
      have hlq : leafQ tab J (j + (t.n1 + 1)) = T + J * ((j : ℚ) + 1) := by
        unfold leafQ
        rw [ite_eq_right (by omega), hlen]
        have : j + (t.n1 + 1) - (t.n1 + 1 - 1) = j + 1 := by omega
        rw [this, show t.n1 + 1 - 1 = t.n1 by omega]
        push_cast
        ring
      rw [poisW_eq_pR, ← ENNReal.ofReal_mul (pR_nonneg (NNReal.coe_nonneg μ) _), hlq]
      apply ENNReal.ofReal_le_ofReal
      have hp := t.tail ht j
      rw [show t.n1 + 1 + j = j + (t.n1 + 1) by ring] at hp
      push_cast
      have hv : (0 : ℝ) ≤ (T : ℝ) + (J : ℝ) * ((j : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ0
        positivity
      calc pR (μ : ℝ) (j + (t.n1 + 1)) * ((T : ℝ) + (J : ℝ) * ((j : ℝ) + 1))
          ≤ ((t.pb (t.n1 + 1) : ℝ) * (t.r : ℝ) ^ j) * ((T : ℝ) + (J : ℝ) * ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hp hv
        _ = _ := by ring
    have hsum := tsum_geom_lin (t.r : ℝ) (T : ℝ) (J : ℝ) hr0 hr1'
    have hJ0' : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ0
    calc ∑' j, poisW μ (j + (t.n1 + 1)) * ENNReal.ofReal (leafQ tab J (j + (t.n1 + 1)) : ℝ)
        ≤ ∑' j : ℕ, ENNReal.ofReal ((t.pb (t.n1 + 1) : ℝ) * ((t.r : ℝ) ^ j * ((T : ℝ) + (J : ℝ) * ((j : ℝ) + 1)))) :=
          ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal (∑' j : ℕ, (t.pb (t.n1 + 1) : ℝ) * ((t.r : ℝ) ^ j * ((T : ℝ) + (J : ℝ) * ((j : ℝ) + 1)))) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (by exact_mod_cast t.pb_nonneg _)
            (mul_nonneg (pow_nonneg hr0 j) (by positivity))) ((hsum.mul_left _).summable)]
      _ = _ := by rw [(hsum.mul_left _).tsum_eq]
  calc _ ≤ ENNReal.ofReal (∑ n ∈ Finset.range (t.n1 + 1), (t.pb n : ℝ) * (tab.getD n 0 : ℝ)) +
        ENNReal.ofReal ((t.pb (t.n1 + 1) : ℝ) * ((T : ℝ) / (1 - (t.r : ℝ)) + (J : ℝ) / (1 - (t.r : ℝ)) ^ 2)) :=
        add_le_add hhead htail
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add]
        · apply ENNReal.ofReal_le_ofReal
          rw [list_sum_range]
          push_cast
          exact le_rfl
        · exact Finset.sum_nonneg fun n hn => mul_nonneg (by exact_mod_cast t.pb_nonneg n)
            (htab0 n (Finset.mem_range.1 hn))
        · have hT0 : (0 : ℝ) ≤ (T : ℝ) := by
            have := leafQ_nonneg hleaf t.n1
            unfold leafQ at this
            rw [ite_eq_left (by omega)] at this
            exact_mod_cast this
          have hJ0' : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ0
          have h1r : 0 < 1 - (t.r : ℝ) := by linarith
          exact mul_nonneg (by exact_mod_cast t.pb_nonneg _) (by positivity)
end Sphincs.Security.H0
