import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# A quadratic potential for the landed count

`X = V / p` rescales the landed count, `D = X - n` its drift from the query count. `Λ` is a
supermartingale of an encoding step (a query that lands with probability `p`, caching one input and
spending one unit of budget), so `X C + (1 - p) X²` is bounded in mean by `A n`.
-/

namespace XmssSecurity.Partner

noncomputable def momentK : ℝ := 2 ^ 76

noncomputable def momentκ : ℝ := 1 / 2 ^ 74

noncomputable def momentA (p : ℝ) (Q : ℕ) : ℝ := (2 - p) * Q + momentK

/-- The potential: landed count `V`, cached count `C`, query count `n`, remaining budget `F`. -/
noncomputable def Λ (p : ℝ) (Q V C n F : ℕ) : ℝ :=
  (V / p) * C + (1 - p) * (V / p) ^ 2 - momentA p Q * n + (2 - p) * (Q * n - n ^ 2)
    + momentκ * (V / p - n) ^ 2 * F

theorem encoding_step {p : ℝ} {Q V C n F : ℕ} (hp : 1 / 2 ^ 21 ≤ p) (hp' : p ≤ 1 / 2 ^ 20)
    (hQ : Q ≤ 2 ^ 127) (hC : C ≤ n) (hF : 1 ≤ F) (hnF : n + F ≤ Q) :
    p * Λ p Q (V + 1) (C + 1) (n + 1) (F - 1) + (1 - p) * Λ p Q V (C + 1) (n + 1) (F - 1)
      ≤ Λ p Q V C n F := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hp1 : p ≤ 1 := hp'.trans (by norm_num)
  have hFc : ((F - 1 : ℕ) : ℝ) = F - 1 := by rw [Nat.cast_sub hF, Nat.cast_one]
  have hCn : (C : ℝ) ≤ n := by exact_mod_cast hC
  have hFQ : (F : ℝ) - 1 ≤ 2 ^ 127 := by
    have : (F : ℝ) ≤ Q := by exact_mod_cast (Nat.le_add_left F n).trans hnF
    have : (Q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hQ
    linarith
  have hF1 : (0 : ℝ) ≤ F - 1 := by
    have : (1 : ℝ) ≤ F := by exact_mod_cast hF
    linarith
  set u := 1 / p with hu
  have hpu : p * u = 1 := by rw [hu]; field_simp
  have hu21 : u ≤ 2 ^ 21 := by
    rw [hu, div_le_iff₀ hp0]
    have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 ^ 21)
    field_simp at this ⊢
    linarith
  have hu0 : 0 ≤ u := by positivity
  set x := (V : ℝ) / p with hx
  have hxV : ((V + 1 : ℕ) : ℝ) / p = x + u := by push_cast; rw [hx, hu, add_div]
  set D := x - n with hD
  -- The one-step drift, as an identity.
  have key : p * Λ p Q (V + 1) (C + 1) (n + 1) (F - 1) + (1 - p) * Λ p Q V (C + 1) (n + 1) (F - 1)
      - Λ p Q V C n F
      = (3 - 2 * p) * x + C + 1 + (1 - p) * u - momentK - (2 - p) * (2 * n + 1) - momentκ * D ^ 2
        + momentκ * (F - 1) * (1 - p) * u := by
    simp only [Λ, momentA, hFc, hxV]
    rw [← hx, hD]
    push_cast
    linear_combination
      (C + 1 + (1 - p) * (2 * x + u) + momentκ * (F - 1) * (2 * (x - n - 1) + u)) * hpu
        + momentκ * (F - 1) * mul_inv_cancel₀ hp0.ne'
  -- AM-GM on the drift term.
  have hsq := sq_nonneg (momentκ * D - (3 - 2 * p) / 2)
  have hκ : momentκ = 1 / 2 ^ 74 := rfl
  have hamgm : (3 - 2 * p) * D - momentκ * D ^ 2 ≤ 9 * 2 ^ 72 := by
    have h1 : momentκ * ((3 - 2 * p) * D - momentκ * D ^ 2) ≤ 9 / 4 := by nlinarith
    rw [hκ] at h1 ⊢
    linarith
  have hbud : momentκ * (F - 1) * (1 - p) * u ≤ 2 ^ 74 := by
    have : (F - 1) * (1 - p) * u ≤ 2 ^ 127 * 2 ^ 21 := by
      have h1 : (F - 1) * (1 - p) ≤ 2 ^ 127 := by nlinarith
      have h2 : 0 ≤ (F - 1) * (1 - p) := mul_nonneg hF1 (by linarith)
      calc (F - 1) * (1 - p) * u ≤ 2 ^ 127 * u := mul_le_mul_of_nonneg_right h1 hu0
        _ ≤ 2 ^ 127 * 2 ^ 21 := by gcongr
    rw [hκ, mul_assoc, mul_assoc, ← mul_assoc ((F : ℝ) - 1)]
    linarith
  have hlin : (1 - p) * u ≤ 2 ^ 21 := by nlinarith
  have hK : momentK = 2 ^ 76 := rfl
  have hCn' : (C : ℝ) - (2 - p) * (2 * n) ≤ -(3 - 2 * p) * n := by nlinarith
  have : (3 - 2 * p) * x - (3 - 2 * p) * n = (3 - 2 * p) * D := by rw [hD]; ring
  linarith

theorem budget_step (p : ℝ) {Q V C n F : ℕ} (hF : 1 ≤ F) : Λ p Q V C n (F - 1) ≤ Λ p Q V C n F := by
  have hFc : ((F - 1 : ℕ) : ℝ) = F - 1 := by rw [Nat.cast_sub hF, Nat.cast_one]
  have : 0 ≤ momentκ * ((V : ℝ) / p - n) ^ 2 := by rw [momentκ]; positivity
  simp only [Λ, hFc]
  nlinarith

theorem Λ_zero (p : ℝ) (Q F : ℕ) : Λ p Q 0 0 0 F = 0 := by simp [Λ]

theorem final_bound {p : ℝ} {Q V C n : ℕ} (F : ℕ) (hp : p ≤ 2) (hn : n ≤ Q) :
    (V / p) * C + (1 - p) * (V / p) ^ 2 ≤ Λ p Q V C n F + momentA p Q * n := by
  have hn' : (n : ℝ) ≤ Q := by exact_mod_cast hn
  have h1 : 0 ≤ (2 - p) * (Q * n - n ^ 2 : ℝ) := mul_nonneg (by linarith) (by nlinarith [n.cast_nonneg (α := ℝ)])
  have h2 : 0 ≤ momentκ * ((V : ℝ) / p - n) ^ 2 * F := by rw [momentκ]; positivity
  simp only [Λ]
  linarith

end XmssSecurity.Partner
