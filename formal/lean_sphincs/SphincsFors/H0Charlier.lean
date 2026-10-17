import Mathlib

/-! Charlier polynomials `charlier n a ρ = E[(a + Poisson ρ)_n]` (falling factorial), defined by
recursion on `a`, and the inequalities used by the factorial-moment majorant of the virtual
future. -/

open ENNReal

namespace SphincsFors.Security.H0

/-- `charlier n a ρ = Σ_i C(n,i) (a)_i ρ^(n-i)`, by recursion on the shift `a`. -/
noncomputable def charlier : ℕ → ℕ → ℝ≥0∞ → ℝ≥0∞
  | n, 0, ρ => ρ ^ n
  | 0, _ + 1, _ => 1
  | n + 1, a + 1, ρ => charlier (n + 1) a ρ + (n + 1 : ℕ) * charlier n a ρ

@[simp] theorem charlier_zero_shift (n : ℕ) (ρ : ℝ≥0∞) : charlier n 0 ρ = ρ ^ n := by
  cases n <;> rfl

@[simp] theorem charlier_zero_order (a : ℕ) (ρ : ℝ≥0∞) : charlier 0 a ρ = 1 := by
  cases a <;> simp [charlier]

/-- (P1) one more disclosure at the index. -/
theorem charlier_succ (n a : ℕ) (ρ : ℝ≥0∞) :
    charlier (n + 1) (a + 1) ρ = charlier (n + 1) a ρ + (n + 1 : ℕ) * charlier n a ρ := rfl

/-- At rate zero the Charlier polynomial is the falling factorial. -/
theorem charlier_rate_zero : ∀ (n a : ℕ), charlier n a 0 = (a.descFactorial n : ℝ≥0∞)
  | 0, a => by simp
  | n + 1, 0 => by simp
  | n + 1, a + 1 => by
      rw [charlier_succ, charlier_rate_zero (n + 1) a, charlier_rate_zero n a]
      norm_cast
      rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
      rcases Nat.lt_or_ge a n with h | h
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp
      · have : a - n + (n + 1) = a + 1 := by omega
        calc (a - n) * a.descFactorial n + (n + 1) * a.descFactorial n
            = a.descFactorial n * (a - n + (n + 1)) := by ring
          _ = (a + 1) * a.descFactorial n := by rw [this]; ring

/-- Base case of (P2)/(P3): Bernoulli-type bounds for powers. -/
theorem pow_add_ge (ρ δ : ℝ≥0∞) : ∀ n : ℕ, ρ ^ (n + 1) + δ * (n + 1 : ℕ) * ρ ^ n ≤ (ρ + δ) ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
      have ih := pow_add_ge ρ δ n
      calc ρ ^ (n + 2) + δ * ((n + 2 : ℕ) : ℝ≥0∞) * ρ ^ (n + 1)
          = ρ * (ρ ^ (n + 1) + δ * ((n + 1 : ℕ) : ℝ≥0∞) * ρ ^ n) + δ * ρ ^ (n + 1) := by
            push_cast; ring
        _ ≤ ρ * (ρ + δ) ^ (n + 1) + δ * (ρ + δ) ^ (n + 1) := by
            gcongr
            exact le_self_add
        _ = (ρ + δ) ^ (n + 2) := by ring

theorem pow_add_le (ρ δ : ℝ≥0∞) : ∀ n : ℕ, (ρ + δ) ^ (n + 1) ≤ ρ ^ (n + 1) + δ * (n + 1 : ℕ) * (ρ + δ) ^ n
  | 0 => by simp
  | n + 1 => by
      have ih := pow_add_le ρ δ n
      have h1 : ρ * (ρ + δ) ^ (n + 1) ≤ ρ * (ρ ^ (n + 1) + δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ n) :=
        mul_le_mul_right ih ρ
      have h2 : ρ * (δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ n) ≤ δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ (n + 1) := by
        calc ρ * (δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ n) = δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ * (ρ + δ) ^ n) := by ring
          _ ≤ δ * ((n + 1 : ℕ) : ℝ≥0∞) * ((ρ + δ) * (ρ + δ) ^ n) := by gcongr; exact le_self_add
          _ = δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ (n + 1) := by ring
      calc (ρ + δ) ^ (n + 2) = ρ * (ρ + δ) ^ (n + 1) + δ * (ρ + δ) ^ (n + 1) := by ring
        _ ≤ ρ * (ρ ^ (n + 1) + δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ n) + δ * (ρ + δ) ^ (n + 1) := by gcongr
        _ = ρ ^ (n + 2) + ρ * (δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ n) + δ * (ρ + δ) ^ (n + 1) := by ring
        _ ≤ ρ ^ (n + 2) + δ * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ (n + 1) + δ * (ρ + δ) ^ (n + 1) := by gcongr
        _ = ρ ^ (n + 2) + δ * ((n + 2 : ℕ) : ℝ≥0∞) * (ρ + δ) ^ (n + 1) := by push_cast; ring

/-- (P2) lower bound: raising the rate by `δ` gains at least `δ n P_{n-1}`. -/
theorem charlier_lower (δ : ℝ≥0∞) : ∀ (n a : ℕ) (ρ : ℝ≥0∞),
    charlier (n + 1) a ρ + δ * (n + 1 : ℕ) * charlier n a ρ ≤ charlier (n + 1) a (ρ + δ)
  | n, 0, ρ => by simpa using pow_add_ge ρ δ n
  | 0, a + 1, ρ => by
      have h := charlier_lower δ 0 a ρ
      rw [charlier_succ, charlier_succ 0 a (ρ + δ)]
      simp only [charlier_zero_order, zero_add, Nat.cast_one, mul_one] at h ⊢
      calc charlier 1 a ρ + 1 + δ = (charlier 1 a ρ + δ) + 1 := by ring
        _ ≤ charlier 1 a (ρ + δ) + 1 := by gcongr
  | n + 1, a + 1, ρ => by
      have h1 := charlier_lower δ (n + 1) a ρ
      have h2 := charlier_lower δ n a ρ
      rw [charlier_succ, charlier_succ (n + 1) a (ρ + δ), charlier_succ n a ρ]
      calc charlier (n + 2) a ρ + ((n + 2 : ℕ) : ℝ≥0∞) * charlier (n + 1) a ρ +
            δ * ((n + 2 : ℕ) : ℝ≥0∞) * (charlier (n + 1) a ρ + ((n + 1 : ℕ) : ℝ≥0∞) * charlier n a ρ)
          = (charlier (n + 2) a ρ + δ * ((n + 2 : ℕ) : ℝ≥0∞) * charlier (n + 1) a ρ) +
            ((n + 2 : ℕ) : ℝ≥0∞) * (charlier (n + 1) a ρ + δ * ((n + 1 : ℕ) : ℝ≥0∞) * charlier n a ρ) := by ring
        _ ≤ charlier (n + 2) a (ρ + δ) + ((n + 2 : ℕ) : ℝ≥0∞) * charlier (n + 1) a (ρ + δ) := by
            gcongr

/-- (P3) upper bound (mean value): raising the rate by `δ` gains at most `δ n P_{n-1}(ρ+δ)`. -/
theorem charlier_upper (δ : ℝ≥0∞) : ∀ (n a : ℕ) (ρ : ℝ≥0∞),
    charlier (n + 1) a (ρ + δ) ≤ charlier (n + 1) a ρ + δ * (n + 1 : ℕ) * charlier n a (ρ + δ)
  | n, 0, ρ => by simpa using pow_add_le ρ δ n
  | 0, a + 1, ρ => by
      have h := charlier_upper δ 0 a ρ
      rw [charlier_succ, charlier_succ 0 a ρ]
      simp only [charlier_zero_order, zero_add, Nat.cast_one, mul_one] at h ⊢
      calc charlier 1 a (ρ + δ) + 1 ≤ charlier 1 a ρ + δ + 1 := by gcongr
        _ = charlier 1 a ρ + 1 + δ := by ring
  | n + 1, a + 1, ρ => by
      have h1 := charlier_upper δ (n + 1) a ρ
      have h2 := charlier_upper δ n a ρ
      rw [charlier_succ, charlier_succ (n + 1) a ρ, charlier_succ n a (ρ + δ)]
      calc charlier (n + 2) a (ρ + δ) + ((n + 2 : ℕ) : ℝ≥0∞) * charlier (n + 1) a (ρ + δ)
          ≤ (charlier (n + 2) a ρ + δ * ((n + 2 : ℕ) : ℝ≥0∞) * charlier (n + 1) a (ρ + δ)) +
            ((n + 2 : ℕ) : ℝ≥0∞) * (charlier (n + 1) a ρ + δ * ((n + 1 : ℕ) : ℝ≥0∞) * charlier n a (ρ + δ)) := by
            gcongr
        _ = _ := by ring

/-- (P5) scaling: if `δ ≤ θ ρ` then `P_n(a, ρ+δ) ≤ (1+θ)^n P_n(a, ρ)`. -/
theorem charlier_scale (θ δ : ℝ≥0∞) (ρ : ℝ≥0∞) (hδ : δ ≤ θ * ρ) :
    ∀ (n a : ℕ), charlier n a (ρ + δ) ≤ (1 + θ) ^ n * charlier n a ρ
  | n, 0 => by
      simp only [charlier_zero_shift]
      rw [← mul_pow]
      gcongr
      calc ρ + δ ≤ ρ + θ * ρ := by gcongr
        _ = (1 + θ) * ρ := by ring
  | 0, a + 1 => by simp
  | n + 1, a + 1 => by
      have h1 := charlier_scale θ δ ρ hδ (n + 1) a
      have h2 := charlier_scale θ δ ρ hδ n a
      have hθ : (1 + θ) ^ n ≤ (1 + θ) ^ (n + 1) := pow_le_pow_right₀ le_self_add (Nat.le_succ n)
      rw [charlier_succ, charlier_succ]
      calc charlier (n + 1) a (ρ + δ) + ((n + 1 : ℕ) : ℝ≥0∞) * charlier n a (ρ + δ)
          ≤ (1 + θ) ^ (n + 1) * charlier (n + 1) a ρ + ((n + 1 : ℕ) : ℝ≥0∞) * ((1 + θ) ^ n * charlier n a ρ) := by
            gcongr
        _ ≤ (1 + θ) ^ (n + 1) * charlier (n + 1) a ρ +
            ((n + 1 : ℕ) : ℝ≥0∞) * ((1 + θ) ^ (n + 1) * charlier n a ρ) := by gcongr
        _ = _ := by ring

/-- **Per-index fresh step.** A fresh disclosure at the index together with the future coins of
the new item (rate `mw`) is dominated by raising the rate by `α`, provided
`(1 + mw)(1 + θ)^n ≤ L α` and `mw ≤ θ y`. -/
theorem fresh_index (n c : ℕ) (y mw α L θ : ℝ≥0∞) (hmw : mw ≤ θ * y)
    (hslack : (1 + mw) * (1 + θ) ^ n ≤ L * α) :
    charlier (n + 1) (c + 1) (y + mw) ≤
      charlier (n + 1) c y + L * (α * (n + 1 : ℕ) * charlier n c y) := by
  rw [charlier_succ]
  have h3 := charlier_upper mw n c y
  have h5 := charlier_scale θ mw y hmw n c
  calc charlier (n + 1) c (y + mw) + ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c (y + mw)
      ≤ charlier (n + 1) c y + mw * ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c (y + mw) +
        ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c (y + mw) := by gcongr
    _ = charlier (n + 1) c y + ((n + 1 : ℕ) : ℝ≥0∞) * ((1 + mw) * charlier n c (y + mw)) := by ring
    _ ≤ charlier (n + 1) c y + ((n + 1 : ℕ) : ℝ≥0∞) * ((1 + mw) * ((1 + θ) ^ n * charlier n c y)) := by
        gcongr
    _ = charlier (n + 1) c y + ((n + 1 : ℕ) : ℝ≥0∞) * (((1 + mw) * (1 + θ) ^ n) * charlier n c y) := by ring
    _ ≤ charlier (n + 1) c y + ((n + 1 : ℕ) : ℝ≥0∞) * ((L * α) * charlier n c y) := by gcongr
    _ = _ := by ring

/-- Product expansion lower bound: `Π (a + b) ≥ Π a + Σ_v b_v Π_{l ≠ v} a_l`. -/
theorem prod_add_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ≥0∞) :
    ∏ l ∈ s, a l + ∑ v ∈ s, b v * ∏ l ∈ s.erase v, a l ≤ ∏ l ∈ s, (a l + b l) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.erase_insert hj]
      have herase : ∀ v ∈ s, (insert j s).erase v = insert j (s.erase v) := by
        intro v hv
        rw [Finset.erase_insert_of_ne (by rintro rfl; exact hj hv)]
      have hsum : ∑ v ∈ s, b v * ∏ l ∈ (insert j s).erase v, a l =
          a j * ∑ v ∈ s, b v * ∏ l ∈ s.erase v, a l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [herase v hv, Finset.prod_insert (fun h => hj (Finset.mem_of_mem_erase h))]
        ring
      rw [hsum]
      calc a j * ∏ l ∈ s, a l + (b j * ∏ l ∈ s, a l + a j * ∑ v ∈ s, b v * ∏ l ∈ s.erase v, a l)
          = a j * (∏ l ∈ s, a l + ∑ v ∈ s, b v * ∏ l ∈ s.erase v, a l) + b j * ∏ l ∈ s, a l := by ring
        _ ≤ a j * ∏ l ∈ s, (a l + b l) + b j * ∏ l ∈ s, (a l + b l) := by
            gcongr
            exact le_self_add
        _ = (a j + b j) * ∏ l ∈ s, (a l + b l) := by ring

/-- Linear form of the averaged perturbation bound. -/
theorem avg_perturbed_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (a b e : ι → ℝ≥0∞)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (he : ∀ v, e v ≤ a v + (Fintype.card ι : ℝ≥0∞) * b v) :
    (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ v, e v * ∏ l ∈ Finset.univ.erase v, a l ≤
      ∏ l, a l + ∑ v, b v * ∏ l ∈ Finset.univ.erase v, a l := by
  set L := (Fintype.card ι : ℝ≥0∞)
  have hLtop : L ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∑ v, (a v + L * b v) * ∏ l ∈ Finset.univ.erase v, a l =
      L * ∏ l, a l + L * ∑ v, b v * ∏ l ∈ Finset.univ.erase v, a l := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_prod_erase _ _ (Finset.mem_univ _),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, mul_assoc]
    rfl
  calc L⁻¹ * ∑ v, e v * ∏ l ∈ Finset.univ.erase v, a l
      ≤ L⁻¹ * ∑ v, (a v + L * b v) * ∏ l ∈ Finset.univ.erase v, a l := by
        gcongr with v; exact he v
    _ = ∏ l, a l + ∑ v, b v * ∏ l ∈ Finset.univ.erase v, a l := by
        rw [hsplit, mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hL hLtop, one_mul, one_mul]

/-- **Averaged fresh step over the indices.** If each perturbed factor satisfies
`e v ≤ a v + L b v`, the uniform average of the perturbed products is at most `Π (a + b)`. -/
theorem avg_perturbed_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a b e : ι → ℝ≥0∞)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (he : ∀ v, e v ≤ a v + (Fintype.card ι : ℝ≥0∞) * b v) :
    (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ v, e v * ∏ l ∈ Finset.univ.erase v, a l ≤ ∏ l, (a l + b l) := by
  set L := (Fintype.card ι : ℝ≥0∞)
  have hLtop : L ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∑ v, (a v + L * b v) * ∏ l ∈ Finset.univ.erase v, a l =
      L * ∏ l, a l + L * ∑ v, b v * ∏ l ∈ Finset.univ.erase v, a l := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_prod_erase _ _ (Finset.mem_univ _),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, mul_assoc]
    rfl
  calc L⁻¹ * ∑ v, e v * ∏ l ∈ Finset.univ.erase v, a l
      ≤ L⁻¹ * ∑ v, (a v + L * b v) * ∏ l ∈ Finset.univ.erase v, a l := by
        gcongr with v; exact he v
    _ = ∏ l, a l + ∑ v, b v * ∏ l ∈ Finset.univ.erase v, a l := by
        rw [hsplit, mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hL hLtop, one_mul, one_mul]
    _ ≤ ∏ l, (a l + b l) := prod_add_ge _ a b

end SphincsFors.Security.H0
