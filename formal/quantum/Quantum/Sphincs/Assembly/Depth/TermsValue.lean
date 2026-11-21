module

public import Quantum.Sphincs.Assembly.Depth.Chain
public import Quantum.Sphincs.Assembly.BoundValue
public import Quantum.Sphincs.Assembly.Depth.EventGame

@[expose] public section

/-!
# The terms of the depth-aware leanSPHINCS QRPM bound

Real bounds on the terms of the depth-aware bound that do not depend on the classical caps,
`d' = min d q`, amplitudes in units of `2^-64`:

* the coverage Half event `√(advBD² covPS) ≤ 1522 √(q d') + 2^20` (`advBDcov_le`,
  `√(24 · 2^16 rhoCov) ≤ 1522`);
* the hybrid `√(4 · 10 d' · 6q kappaSph) ≤ 39 √(q d')` (`hybTermSD_le`);
* the capacity rates at grade `S = 6q + 2^67`: `capRate`, `capRateBound ≤ 54 S³ / 2^512`
  (`capRate_le_S`, `capRateBound_le_S`), and the verification's price-free rate `freshKD q ≤
  2^-128 + 2^-200` for `q ≤ 2^90` (`freshKD_le`).
-/

open scoped ENNReal

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (rpow_inv_two_le_ofReal sq_add_rpow_inv_two_le pow_two_rpow_inv_two
  card_Z keepCost inv_two_pow_eq_ofReal two_div_natCast_le)

namespace Quantum.Sphincs.Assembly

/-! ## The capacity rates -/

section rates

set_option exponentiation.threshold 1100 in
/-- **The capacity rate below `S` entries**: `capRate T 18 ≤ 54 S³ / 2^512` for `T + 1 ≤ S`. -/
theorem capRate_le_S {T S : ℕ} (h : T + 1 ≤ S) :
    capRate T 18 ≤ ENNReal.ofReal (54 * (S : ℝ) ^ 3 / 2 ^ 512) := by
  have hc : 3 * 18 * (T + 1) ^ 3 ≤ 54 * S ^ 3 := by
    have := Nat.pow_le_pow_left h 3
    omega
  have hZ : ((Fintype.card Z : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 ^ 512) := by
    rw [card_Z, ← ENNReal.ofReal_natCast]
    norm_num
  have key : ∀ n : ℕ, n ≤ 54 * S ^ 3 →
      (n : ℝ≥0∞) / Fintype.card Z ≤ ENNReal.ofReal (54 * (S : ℝ) ^ 3 / 2 ^ 512) := fun n hn ↦ by
    rw [hZ, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by positivity)]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
    exact_mod_cast hn
  unfold capRate
  exact max_le (key _ ((rateK_le T 18).trans hc)) (key _ ((rateK'_le (by norm_num) T).trans hc))

/-- **The capacity rate bound below `S` entries**: `capRateBound Z T 18 ≤ 54 S³ / 2^512`. -/
theorem capRateBound_le_S {T S : ℕ} (h : T + 1 ≤ S) :
    capRateBound Z T 18 ≤ ENNReal.ofReal (54 * (S : ℝ) ^ 3 / 2 ^ 512) :=
  capRate_le_S h

/-- The verification's grade: `progCap + 6q + clsCap + 3 verifyBlocks + 2 ≤ 6q + 2^67`. -/
theorem verGrade_le (q : ℕ) :
    progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1 ≤ 6 * q + 2 ^ 67 := by
  have hc : progCap + clsCap + 3 * verifyBlocks + 2 ≤ 2 ^ 67 := by
    rw [clsCap_eq, progCap_eq, verifyBlocks_eq]
    norm_num [signatureLimit]
  omega

/-- The game's grade: `progCap + (2q + 4q + clsCap + 1) + 1 ≤ 6q + 2^67`. -/
theorem advGrade_le (q : ℕ) : progCap + (2 * q + 4 * q + clsCap + 1) + 1 ≤ 6 * q + 2 ^ 67 := by
  have := verGrade_le q
  omega

end rates

/-! ## The terms -/

section terms

set_option exponentiation.threshold 1100 in
/-- **The capacity residual** for a grade bound `6q + 2^67 ≤ M²`:
`capTermSD q ≤ 4q · 26 M³ / 2^256` (`√(12 · 54) ≤ 26`). -/
theorem capTermSD_le {q : ℕ} {M : ℝ} (hM : 0 ≤ M) (hS : (6 * q + 2 ^ 67 : ℝ) ≤ M ^ 2) :
    capTermSD q ≤ ENNReal.ofReal (4 * q * (26 * M ^ 3 / 2 ^ 256)) := by
  have hc := capRateBound_le_S (advGrade_le q)
  have hS' : ((6 * q + 2 ^ 67 : ℕ) : ℝ) ≤ M ^ 2 := by
    have e : ((6 * q + 2 ^ 67 : ℕ) : ℝ) = 6 * q + 2 ^ 67 := by push_cast; ring
    rw [e]
    exact hS
  have h0 : (0 : ℝ) ≤ ((6 * q + 2 ^ 67 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : 6 * (2 * capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18) ≤
      ENNReal.ofReal (648 * (M ^ 2) ^ 3 / 2 ^ 512) := by
    grw [hc]
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow_le_pow_left₀ h0 hS' 3
    have e : 6 * (2 * (54 * ((6 * q + 2 ^ 67 : ℕ) : ℝ) ^ 3 / 2 ^ 512)) =
        648 * ((6 * q + 2 ^ 67 : ℕ) : ℝ) ^ 3 / 2 ^ 512 := by ring
    rw [e]
    gcongr
  have hs := rpow_inv_two_le_ofReal (a := 26 * M ^ 3 / 2 ^ 256) (by positivity) h6 (by
    have e1 : 648 * (M ^ 2) ^ 3 / 2 ^ 512 = 648 * (M ^ 3) ^ 2 / 2 ^ 512 := by ring
    have e2 : (26 * M ^ 3 / 2 ^ 256) ^ 2 = 676 * (M ^ 3) ^ 2 / 2 ^ 512 := by ring
    rw [e1, e2]
    have := sq_nonneg (M ^ 3)
    gcongr
    norm_num)
  unfold capTermSD
  grw [hs]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

set_option exponentiation.threshold 1100 in
/-- **The verification's price-free rate** for `q ≤ 2^90`: `freshKD q ≤ 2^-128 + 2^-200`. -/
theorem freshKD_le {q : ℕ} (hq : q ≤ 2 ^ 90) :
    freshKD q ≤ ENNReal.ofReal (1 / 2 ^ 128 + 1 / 2 ^ 200) := by
  have hS : ((6 * q + 2 ^ 67 : ℕ) : ℝ) ≤ 2 ^ 93 := by
    have : 6 * q + 2 ^ 67 ≤ 2 ^ 93 := by omega
    exact_mod_cast this
  have hc := capRate_le_S (verGrade_le q)
  have h3 : 54 * ((6 * q + 2 ^ 67 : ℕ) : ℝ) ^ 3 / 2 ^ 512 ≤ 1 / 2 ^ 202 := by
    calc 54 * ((6 * q + 2 ^ 67 : ℕ) : ℝ) ^ 3 / 2 ^ 512 ≤ 54 * (2 ^ 93) ^ 3 / 2 ^ 512 := by
          gcongr
      _ ≤ 1 / 2 ^ 202 := by norm_num
  unfold freshKD
  grw [hc, ENNReal.ofReal_le_ofReal h3]
  rw [inv_two_pow_eq_ofReal]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The verification's price-free reads** for `q ≤ 2^90`: `3 verifyBlocks √(freshKD q) ≤
2711 · 2^-64`. -/
theorem verReadD_le {q : ℕ} (hq : q ≤ 2 ^ 90) :
    ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * freshKD q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2711 / 2 ^ 64) := by
  have h := rpow_inv_two_le_ofReal (a := 10004 / 10000 / 2 ^ 64) (by positivity) (freshKD_le hq)
    (by norm_num)
  grw [h]
  rw [verifyBlocks_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The verification's linear term and coverage part** for `q ≤ 2^90`: at most `2^-99`. -/
theorem verSD_le {q : ℕ} (hq : q ≤ 2 ^ 90) :
    verLinSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS ≤ ENNReal.ofReal (1 / 2 ^ 99) := by
  have hX : (2 : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [Quantum.Xmss.card_X]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hZ : (2 : ℝ≥0∞) / (Fintype.card Z : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_Z]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hr : ((rhoCov : ℚ) : ℝ) = 7363 / 5000 := by norm_num [rhoCov]
  unfold verLinSD keepCost covPS
  rw [verifyBlocks_eq, hr]
  grw [freshKD_le hq, hX, hZ]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num

set_option exponentiation.threshold 1100 in
/-- **The coverage term at depth `d`**: `√(advBD q d² covPS) ≤ (1522 √(q d') + 2^20) 2^-64`. -/
theorem advBDcov_le (q d : ℕ) :
    (advBD q d ^ 2 * covPS) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (1522 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hsq := Real.sq_sqrt hX
  have hm := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  have hc : covPS ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (31066 / 100 / 2 ^ 64) := by
    refine rpow_inv_two_le_ofReal (r := 96509 / 2 ^ 128) (by positivity) ?_ (by norm_num)
    unfold covPS
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num [rhoCov])
  have h24 : (6 * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞)) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (4899 / 1000 * √((q : ℝ) * (min d q : ℕ))) := by
    refine rpow_inv_two_le_ofReal (r := 24 * ((q : ℝ) * (min d q : ℕ))) (by positivity) ?_ ?_
    · simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      push_cast
      ring
    · rw [mul_pow, hsq]
      nlinarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), pow_two_rpow_inv_two]
  unfold advBD
  rw [verifyBlocks_eq]
  grw [h24, hc]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  have hm' := Real.sqrt_nonneg ((q : ℝ) * min (d : ℝ) q)
  nlinarith

set_option exponentiation.threshold 1100 in
/-- **The hybrid term at depth `d`**: `hybTermSD q d kappaSph readCapS ≤ 39 √(q d') 2^-64 +
30 · 2^-34` (`4 · 10 d' · 6q · 6.25 · 2^-128 = 1500 q d' 2^-128`). -/
theorem hybTermSD_le (q d : ℕ) :
    hybTermSD q d kappaSph readCapS ≤
      ENNReal.ofReal (39 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 30 / 2 ^ 34) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hsq := Real.sq_sqrt hX
  have hs : 4 * (((10 * min d q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaSph)) ≤
      ENNReal.ofReal (1500 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) := by
    grw [kappaSph_le]
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  unfold hybTermSD
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add (rpow_inv_two_le_ofReal (by positivity) hs ?_)
    (rpow_inv_two_le_ofReal (by positivity) readCapS_le (by norm_num))
  rw [div_pow, mul_pow, hsq]
  have h0 : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := hX
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end terms

end Quantum.Sphincs.Assembly

end
