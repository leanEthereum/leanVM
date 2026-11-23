module

public import Quantum.Xmss.Assembly.Security

@[expose] public section

/-!
# The size of the leanXMSS QRPM bound

Security's `qrpmBound q` in closed form for `q ≤ 2^64` (`qrpmBound_le`):
`qrpmBound q ≤ ((28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`, at most `2^-55.5` for small `q` and
about `q² 2^-118.4` for large `q`. Each term is bounded by a real number separately:

* the adversary term `advTerm q ≤ 15 q 2^-64` (`advTerm_le`, from `advEps n ≤ 2^-128`), the
  verification `verTerm q ≤ 1194 · 2^-64` (`verTerm_le_ofReal`) and `progBound + verLin q ≤
  2^-116` (`progVer_le`);
* the flip-value recorded mass `flipMassCap q ≤ 6 q 2^-94 + 2^-60` (`flipMassCap_le`), the Enc
  term of `clsBound` at most `q 2^-102 + 2^-60` (`encIn_le`, from `encEC_le`, `encBeta_le`,
  `encGamma_le`), hence `√(clsBound q + verLin q) ≤ 41 √q 2^-51 + 2^-29 + 2^-58`
  (`clsVer_rpow_le`);
* the read error, trial and good-table terms at most `2^-168` (`restTerms_le`), the hybrid
  `hybTerm q ≤ 13 q 2^-64 + 41 · 2^-34` (`hybTerm_le`, `readCap ≤ 41² 2^-68`) and
  `r0Term ≤ 2^-173` (`r0Term_le`).

At `q ≤ 2^30` the bound is at most `2^-54` (`qrpmBound_two_pow_30_le`), at `q ≤ 2^50` at most
`2^-18` (`qrpmBound_two_pow_50_le`).
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Helpers -/

section helpers

/-- A square root below `a` from a bound below `a²`. -/
theorem rpow_inv_two_le_ofReal {x : ℝ≥0∞} {r a : ℝ} (ha : 0 ≤ a) (hx : x ≤ ENNReal.ofReal r)
    (h : r ≤ a ^ 2) : x ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal a :=
  calc x ^ (2⁻¹ : ℝ) ≤ (ENNReal.ofReal a ^ 2) ^ (2⁻¹ : ℝ) := by
        rw [← ENNReal.ofReal_pow ha]
        exact ENNReal.rpow_le_rpow (hx.trans (ENNReal.ofReal_le_ofReal h)) (by norm_num)
    _ = ENNReal.ofReal a := pow_two_rpow_inv_two _

/-- `√(a² + b) ≤ a + √b`. -/
theorem sq_add_rpow_inv_two_le (a b : ℝ≥0∞) : (a ^ 2 + b) ^ (2⁻¹ : ℝ) ≤ a + b ^ (2⁻¹ : ℝ) :=
  (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans_eq
    (by rw [pow_two_rpow_inv_two])

theorem clsCap_le_102 : (clsCap : ℝ) ≤ 102 * 2 ^ 60 := by
  rw [clsCap, verifyBlocks_eq, signBlocks_eq, progCap_eq]
  norm_num [lifetime, layerCount, layerHeight]

theorem progCap_le_five : (progCap : ℝ) ≤ 5 * 2 ^ 40 := by
  rw [progCap_eq]
  norm_num

theorem nWD_le {q : ℕ} (hq : q ≤ 2 ^ 64) : nW + nD q ≤ 2 ^ 68 + 1 := by
  have := progCap_add_le hq
  unfold nW nD
  omega

theorem potCap_le_real {q : ℕ} (hq : q ≤ 2 ^ 64) : (potCap q : ℝ) ≤ 2 ^ 68 + 2 := by
  have h : potCap q ≤ 2 ^ 68 + 2 := by
    have := nWD_le hq
    unfold potCap
    omega
  exact_mod_cast h

end helpers

/-! ## The adversary and verification terms -/

section adv

/-- The entries below which the adversary's fresh bounds are taken: below `2^68`. -/
theorem advEntries_le {q n : ℕ} (hq : q ≤ 2 ^ 64) (hn : n < 6 * q) :
    progCap + (n + clsCap + 1) + 1 ≤ 2 ^ 68 :=
  le_trans (by omega) (verEntries_le hq)

set_option exponentiation.threshold 1100 in
/-- **The adversary's fresh bound at Keccak sizes**: `advEps n ≤ 2^-128` for `n < 6q`,
`q ≤ 2^64`. -/
theorem advEps_le {q n : ℕ} (hq : q ≤ 2 ^ 64) (hn : n < 6 * q) :
    advEps n ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (preimageRateBound_le_cube (by norm_num) _ _).trans (max_le ?_ ?_)
  · rw [card_X]
    exact natCast_div_le_inv_two_pow (pow_add 2 960 128).symm.le
  · rw [card_Z]
    refine natCast_div_le_inv_two_pow ?_
    calc 3 * 18 * (progCap + (n + clsCap + 1) + 1) ^ 3 * 2 ^ 128
        ≤ 3 * 18 * (2 ^ 68) ^ 3 * 2 ^ 128 := by gcongr; exact advEntries_le hq hn
      _ ≤ 2 ^ 6 * (2 ^ 68) ^ 3 * 2 ^ 128 := by gcongr; norm_num
      _ = 2 ^ 338 := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The adversary term**: `advTerm q ≤ 15 q 2^-64` for `q ≤ 2^64` (`6q` calls at
`√(6 · 2^-128) ≤ (5/2) 2^-64` each). -/
theorem advTerm_le {q : ℕ} (hq : q ≤ 2 ^ 64) : advTerm q ≤ ENNReal.ofReal (15 * q / 2 ^ 64) := by
  have hs : ∀ n ∈ Finset.range (6 * q),
      (6 * advEps n) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (5 / 2 ^ 65) := by
    intro n hn
    refine rpow_inv_two_le_ofReal (r := 6 / 2 ^ 128) (by positivity) ?_ (by norm_num)
    grw [advEps_le hq (Finset.mem_range.mp hn)]
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  unfold advTerm
  refine (Finset.sum_le_card_nsmul _ _ _ hs).trans_eq ?_
  rw [Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

set_option exponentiation.threshold 1100 in
/-- **The verification term**: `verTerm q ≤ 1194 · 2^-64` for `q ≤ 2^64`. -/
theorem verTerm_le_ofReal {q : ℕ} (hq : q ≤ 2 ^ 64) :
    verTerm q ≤ ENNReal.ofReal (1194 / 2 ^ 64) := by
  refine (verTerm_le hq).trans ?_
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The programs**: `progBound ≤ 2^-126`. -/
theorem progBound_le : progBound ≤ ENNReal.ofReal (1 / 2 ^ 126) := by
  have hp := progCap_le_five
  unfold progBound keyBadCap
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- **The programs and the verification's linear term**: `progBound + verLin q ≤ 2^-116` for
`q ≤ 2^64`. -/
theorem progVer_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    progBound + verLin q ≤ ENNReal.ofReal (1 / 2 ^ 116) := by
  grw [progBound_le, verLin_le hq]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end adv

/-! ## The flip-value recorded mass -/

section flip

set_option exponentiation.threshold 1100 in
/-- The fresh constant below `2^68` cells: `cwFreshEps G ≤ 2^-370`. -/
theorem cwFreshEps_le_of {G : ℕ} (hG : G ≤ 2 ^ 68) : cwFreshEps G ≤ 1 / 2 ^ 370 := by
  have hG' : (G : ℝ) ≤ 2 ^ 68 := by exact_mod_cast hG
  have h2 : (G : ℝ) * G ≤ 2 ^ 68 * 2 ^ 68 := mul_le_mul hG' hG' (Nat.cast_nonneg G) (by positivity)
  unfold cwFreshEps
  rw [card_Z]
  push_cast
  nlinarith

set_option exponentiation.threshold 1100 in
/-- **The flip-value recorded mass**: `flipMassCap q ≤ 6 q 2^-94 + 2^-60` for `q ≤ 2^64` (the
first reveals `6q 2^-94`, the conversion `recConv ≤ 204 · 2^-68`, the rest below `2^-72`). -/
theorem flipMassCap_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    flipMassCap q ≤ ENNReal.ofReal (6 * q / 2 ^ 94 + 1 / 2 ^ 60) := by
  have hf : ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) ≤ ENNReal.ofReal (1 / 2 ^ 370) :=
    ENNReal.ofReal_le_ofReal (cwFreshEps_le_of (le_add_self.trans (progCap_add_le hq)))
  have hc := clsCap_le_102
  unfold flipMassCap cwRecCap cwRevTau recBadCap decHitTau recConv recOffTau cwReEpsC
  rw [revFirstC_eq, card_Z]
  grw [hf, cwJunk_le]
  simp (disch := positivity) only [add_zero, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [randomizerAttemptLimit]
  push_cast
  linarith

end flip

/-! ## The Enc term of the prefix's classical costs -/

section enc

set_option exponentiation.threshold 4096 in
/-- `kapS q ≤ 2^-78` for `q ≤ 2^64`. -/
theorem kapS_le {q : ℕ} (hq : q ≤ 2 ^ 64) : kapS q ≤ (2 ^ 78 : ℝ)⁻¹ := by
  have he := epsQ_le hq
  have he0 := epsQ_nonneg q
  have h6 : 6 * epsQ q ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by
    calc 6 * epsQ q ≤ 6 * (2 ^ 302 : ℝ)⁻¹ := by gcongr
      _ ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by norm_num
  have hs : √(6 * epsQ q) ≤ (2 ^ 149 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt h6).trans_eq (Real.sqrt_sq (by positivity))
  unfold kapS
  calc (potCap q : ℝ) * (2 * √(6 * epsQ q) + 6 * epsQ q)
      ≤ (2 ^ 68 + 2) * (2 * (2 ^ 149 : ℝ)⁻¹ + ((2 ^ 149 : ℝ)⁻¹) ^ 2) := by
        gcongr
        exact potCap_le_real hq
    _ ≤ (2 ^ 78 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- `kapR6 q ≤ 2^-79` for `q ≤ 2^64`. -/
theorem kapR6_le {q : ℕ} (hq : q ≤ 2 ^ 64) : kapR6 q ≤ (2 ^ 79 : ℝ)⁻¹ := by
  have he := epsQ_le hq
  have he0 := epsQ_nonneg q
  have he' : epsQ q ≤ ((2 ^ 151 : ℝ)⁻¹) ^ 2 := he.trans_eq (by norm_num)
  have hs : √(epsQ q) ≤ (2 ^ 151 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt he').trans_eq (Real.sqrt_sq (by positivity))
  have hX : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hZ : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_Z]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hX6 : (6 : ℝ) / Fintype.card X ≤ (2 ^ 1000 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold kapR6
  calc (potCap q : ℝ) * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) +
        6 / (Fintype.card X : ℝ)
      ≤ (2 ^ 68 + 2) * ((2 ^ 302 : ℝ)⁻¹ + ((2 ^ 511 : ℝ)⁻¹ + (2 ^ 511 : ℝ)⁻¹) +
          2 * (2 ^ 151 : ℝ)⁻¹) + (2 ^ 1000 : ℝ)⁻¹ := by
        gcongr
        exact potCap_le_real hq
    _ ≤ (2 ^ 79 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- `kapRR ≤ 2^-148`. -/
theorem kapRR_le : kapRR ≤ (2 ^ 148 : ℝ)⁻¹ := by
  have h' : (2 ^ 301 : ℝ)⁻¹ ≤ ((2 ^ 150 : ℝ)⁻¹) ^ 2 := by norm_num
  have hs : √((2 ^ 301 : ℝ)⁻¹) ≤ (2 ^ 150 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt h').trans_eq (Real.sqrt_sq (by positivity))
  have hX : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hZ : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_Z]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold kapRR
  calc (2 ^ 301 : ℝ)⁻¹ + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √((2 ^ 301 : ℝ)⁻¹)
      ≤ (2 ^ 301 : ℝ)⁻¹ + ((2 ^ 511 : ℝ)⁻¹ + (2 ^ 511 : ℝ)⁻¹) + 2 * (2 ^ 150 : ℝ)⁻¹ := by
        gcongr
    _ ≤ (2 ^ 148 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 1100 in
/-- **The refined Enc constant**: `encE0 q ≤ 6 q 2^-106 + 123 · 2^-68` for `q ≤ 2^64`. -/
theorem encE0_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encE0 q ≤ ENNReal.ofReal (6 * q / 2 ^ 106 + 123 / 2 ^ 68) := by
  have hS : ENNReal.ofReal (kapS q) ≤ ENNReal.ofReal (2 ^ 78 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (kapS_le hq)
  have hR : ENNReal.ofReal (kapR6 q) ≤ ENNReal.ofReal (2 ^ 79 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (kapR6_le hq)
  have hc := clsCap_le_102
  have hp := progCap_le_five
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  unfold encE0
  grw [hS, hR]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The prefix's linear charge constant**: `encEC q ≤ 6 q 2^-105 + 247 · 2^-68` for
`q ≤ 2^64`. -/
theorem encEC_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encEC q ≤ ENNReal.ofReal (6 * q / 2 ^ 105 + 247 / 2 ^ 68) := by
  have hR : ENNReal.ofReal kapRR ≤ ENNReal.ofReal (2 ^ 148 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal kapRR_le
  have hc := clsCap_le_102
  unfold encEC encDelta
  rw [card_Z]
  grw [encE0_le hq, hR]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- `encBeta q ≤ 2^-36` for `q ≤ 2^64`. -/
theorem encBeta_le {q : ℕ} (hq : q ≤ 2 ^ 64) : encBeta q ≤ ENNReal.ofReal (1 / 2 ^ 36) := by
  have hN : ((nW + nD q : ℕ) : ℝ) ≤ 2 ^ 68 + 1 := by exact_mod_cast nWD_le hq
  unfold encBeta
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- `encGamma q ≤ 2^-37` for `q ≤ 2^64`. -/
theorem encGamma_le {q : ℕ} (hq : q ≤ 2 ^ 64) : encGamma q ≤ ENNReal.ofReal (1 / 2 ^ 37) := by
  have hP := potCap_le_real hq
  unfold encGamma
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- **The Enc term of `clsBound`**: at most `q 2^-102 + 2^-60` for `q ≤ 2^64`. -/
theorem encIn_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encEC q + 2 * encBeta q * flipMassCap q + 2 * encGamma q * (progBound + recJCap) ≤
      ENNReal.ofReal (q / 2 ^ 102 + 1 / 2 ^ 60) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  grw [encEC_le hq, encBeta_le hq, flipMassCap_le hq, encGamma_le hq, progBound_le]
  unfold recJCap
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

/-- **The prefix's classical costs and the verification's linear term, square-rooted**:
`√(clsBound q + verLin q) ≤ 41 √q 2^-51 + 2^-29 + 2^-58` for `q ≤ 2^64`. -/
theorem clsVer_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    (clsBound q + verLin q) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (41 * √(q : ℝ) / 2 ^ 51 + 1 / 2 ^ 29 + 1 / 2 ^ 58) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hE := rpow_inv_two_le_ofReal (a := √(q : ℝ) / 2 ^ 51 + 1 / 2 ^ 30) (by positivity)
    (encIn_le hq) (by nlinarith)
  have hF := rpow_inv_two_le_ofReal (a := 5 * √(q : ℝ) / 2 ^ 48 + 1 / 2 ^ 30) (by positivity)
    (flipMassCap_le hq) (by nlinarith)
  have hP := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 58) (by positivity) (progVer_le hq)
    (by norm_num)
  unfold clsBound
  rw [add_assoc]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add hE hF) hP).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end enc

/-! ## The event term, the hybrid and the closed form -/

section closed

set_option exponentiation.threshold 4096 in
/-- **The read error, trial and good-table terms**: at most `2^-168`. -/
theorem restTerms_le : readTerm + (trialCap + goodTerm) ≤ ENNReal.ofReal (1 / 2 ^ 168) := by
  unfold readTerm trialCap goodTerm permTerm disjCap readError
  rw [card_X, card_Z, verifyBlocks_eq]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  norm_num

set_option exponentiation.threshold 1100 in
/-- `r0Term ≤ 2^-173`. -/
theorem r0Term_le : r0Term ≤ ENNReal.ofReal (1 / 2 ^ 173) := by
  unfold r0Term
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The square-rooted event term**: `√eventTerm q ≤ 15 q 2^-64 + 1194 · 2^-64 +
(41 √q 2^-51 + 2^-29 + 2^-58) + 2^-84` for `q ≤ 2^64`. -/
theorem eventTerm_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    eventTerm q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (15 * q / 2 ^ 64 + 1194 / 2 ^ 64 +
      (41 * √(q : ℝ) / 2 ^ 51 + 1 / 2 ^ 29 + 1 / 2 ^ 58) + 1 / 2 ^ 84) := by
  have hs := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 84) (by positivity) restTerms_le (by norm_num)
  unfold eventTerm
  rw [add_assoc, add_assoc]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add (add_le_add
    (advTerm_le hq) (verTerm_le_ofReal hq)) (clsVer_rpow_le hq)) hs).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

set_option exponentiation.threshold 1100 in
/-- **The read ports' mass**: `readCap ≤ 41² 2^-68` (`16 clsCap 2^-128 ≤ 1632 · 2^-68`). -/
theorem readCap_le : readCap ≤ ENNReal.ofReal (1681 / 2 ^ 68) := by
  have hc := clsCap_le_102
  unfold readCap htrialTau
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- **The hybrid term**: `hybTerm q ≤ 13 q 2^-64 + 41 · 2^-34` (`4 · 6q · 6q κ ≤ 169 q² 2^-128`). -/
theorem hybTerm_le (q : ℕ) : hybTerm q ≤ ENNReal.ofReal (13 * q / 2 ^ 64 + 41 / 2 ^ 34) := by
  have hq2 := sq_nonneg (q : ℝ)
  have hs : 4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS)) ≤
      ENNReal.ofReal (145 * (q : ℝ) ^ 2 / 2 ^ 128) := by
    unfold kappaS
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_add]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith
  unfold hybTerm
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (rpow_inv_two_le_ofReal (by positivity) hs (by nlinarith))
    (rpow_inv_two_le_ofReal (by positivity) readCap_le (by norm_num))

/-- The arithmetic of the closed form: the sum of the term bounds is at most
`(28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64 - 2^-34`, which absorbs `r0Term`. -/
theorem root_sq_le (q : ℕ) :
    (15 * q / 2 ^ 64 + 1194 / 2 ^ 64 + (41 * √(q : ℝ) / 2 ^ 51 + 1 / 2 ^ 29 + 1 / 2 ^ 58) +
      1 / 2 ^ 84 + (13 * q / 2 ^ 64 + 41 / 2 ^ 34)) ^ 2 + 1 / 2 ^ 173 ≤
      ((28 * q + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  set F := (28 * (q : ℝ) + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64 with hF
  have h1 : 15 * (q : ℝ) / 2 ^ 64 + 1194 / 2 ^ 64 +
      (41 * √(q : ℝ) / 2 ^ 51 + 1 / 2 ^ 29 + 1 / 2 ^ 58) + 1 / 2 ^ 84 +
      (13 * q / 2 ^ 64 + 41 / 2 ^ 34) ≤ F - 1 / 2 ^ 34 := by
    rw [hF]
    linarith
  have h2 : 75 / 2 ^ 34 ≤ F := by
    rw [hF]
    linarith
  calc _ ≤ (F - 1 / 2 ^ 34) ^ 2 + 1 / 2 ^ 173 := by gcongr
    _ ≤ F ^ 2 := by nlinarith

/-- **The leanXMSS QRPM bound in closed form**: for `q ≤ 2^64`,
`qrpmBound q ≤ ((28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`. -/
theorem qrpmBound_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    qrpmBound q ≤
      ENNReal.ofReal (((28 * q + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2) := by
  have h1 := eventTerm_rpow_le hq
  have h2 := hybTerm_le q
  have h3 := r0Term_le
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (root_sq_le q))
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold qrpmBound
  gcongr

set_option exponentiation.threshold 1100 in
/-- **At most `2^30` permutation calls**: `qrpmBound q ≤ 2^-54`. -/
theorem qrpmBound_two_pow_30_le {q : ℕ} (hq : q ≤ 2 ^ 30) :
    qrpmBound q ≤ (2 ^ 54 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 15 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 30 = (2 ^ 15) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (qrpmBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((28 * q + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2
      ≤ ((28 * 2 ^ 30 + 21 * 2 ^ 14 * 2 ^ 15 + 75 * 2 ^ 30) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 54 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^50` permutation calls**: `qrpmBound q ≤ 2^-18`. -/
theorem qrpmBound_two_pow_50_le {q : ℕ} (hq : q ≤ 2 ^ 50) :
    qrpmBound q ≤ (2 ^ 18 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 50 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 25 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 50 = (2 ^ 25) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (qrpmBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((28 * q + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2
      ≤ ((28 * 2 ^ 50 + 21 * 2 ^ 14 * 2 ^ 25 + 75 * 2 ^ 30) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 18 := by norm_num

end closed

end Quantum.Xmss.Assembly

end
