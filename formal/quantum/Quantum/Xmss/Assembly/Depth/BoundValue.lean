module

public import Quantum.Xmss.Assembly.Depth.Caps
public import Quantum.Xmss.Assembly.BoundValue

@[expose] public section

/-!
# The size of the depth-aware leanXMSS QRPM bound

Caps' `qrpmDepthBound q d` in closed form for `q ≤ 2^84` (`qrpmDepthBound_le`), with
`d' = min d q`:
`((20.4 √(q d') + 11 · 2^-28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`.

* the adversary term: the `h` rounds `√(24 · 2^-128 q d') ≤ 4.9 √(q d') 2^-64` and the capacity
  residual `capTermD q ≤ q 2^-119` (`advTermD_le`); the hybrid
  `√(240 q d' κ) ≤ 15.5 √(q d') 2^-64` (`hybTermD_le`);
* the capacity rate at the game's grade: `epsQ q ≤ 37 (6q + 2^67)³ / 2^512`
  (`epsQ_le_cube`), hence `√(epsQ q) ≤ 15 · 2^-214 (6q + 2^67)` and `≤ 2^-123`
  (`sqrt_epsQ_le_lin`, `sqrt_epsQ_le`);
* the Enc term of `clsBoundD` (`encInD_le`): at most `7110² 2^-128 q + (43 · 2^-94 q)² +
  (63 · 2^-36)²`. Its `q²` part is the `RecJ` weight times the Enc program-jump factor,
  `2 encGamma q · recS q · 6q`: the `RecJ` charge per sponge call, `recN · 2 √(6 epsQ q)`, grows
  like `q^1.5`, so this term grows like `q^3.5` and is absorbed here into `q²` with `q ≤ 2^84`.
  It is what limits the range (the bound exceeds `1` near `q = 2^87`); a sharper `RecJ` estimate
  would extend it.

At `q ≤ 2^80` calls in `d ≤ 2^28` rounds the bound is at most `2^-9`
(`qrpmDepthBound_two_pow_80_28_le`), at `q ≤ 2^64` calls in `d ≤ 2^40` rounds at most `2^-15`
(`qrpmDepthBound_two_pow_64_40_le`).
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The game's grade and the capacity rate -/

section grade

/-- The capacity counts at grade `T ≥ 2^7`: `capKJ T 18 + capKJ' T 18 ≤ 37 T³`. -/
theorem capKJ_add_le_cube {T : ℕ} (hT : 2 ^ 7 ≤ T) : capKJ T 18 + capKJ' T 18 ≤ 37 * T ^ 3 := by
  have h1 : 128 * T ^ 2 ≤ T ^ 3 := by
    rw [pow_succ T 2, mul_comm (T ^ 2) T]
    exact Nat.mul_le_mul_right _ hT
  have h2 : 128 * T ≤ T ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hT
  unfold capKJ capKJ'
  ring_nf
  nlinarith

theorem two_pow_seven_le_nWD (q : ℕ) : 2 ^ 7 ≤ nW + nD q := by
  unfold nW
  rw [progCap_eq]
  omega

theorem nWD_le_lin (q : ℕ) : ((nW + nD q : ℕ) : ℝ) ≤ 6 * q + 2 ^ 67 := by
  have hc := clsCap_le_102
  have hp := progCap_le_five
  unfold nW nD
  push_cast
  linarith

theorem potCap_le_lin (q : ℕ) : (potCap q : ℝ) ≤ 6 * q + 2 ^ 67 := by
  have hc := clsCap_le_102
  have hp := progCap_le_five
  unfold potCap nW nD
  push_cast
  linarith

theorem recN_le_lin : (recN : ℝ) ≤ 10 * 2 ^ 40 + 1 := by
  have hp := progCap_le_five
  unfold recN
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The capacity rate at the game's grade**: `epsQ q ≤ 37 (6q + 2^67)³ / 2^512`. -/
theorem epsQ_le_cube (q : ℕ) : epsQ q ≤ 37 * (6 * q + 2 ^ 67) ^ 3 / 2 ^ 512 := by
  have h : ((capKJ (nW + nD q) 18 + capKJ' (nW + nD q) 18 : ℕ) : ℝ) ≤
      37 * ((nW + nD q : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast capKJ_add_le_cube (two_pow_seven_le_nWD q)
  have hT := nWD_le_lin q
  have h0 : (0 : ℝ) ≤ ((nW + nD q : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold epsQ epsLev
  rw [card_Z, Nat.cast_pow, Nat.cast_ofNat]
  calc _ ≤ 37 * ((nW + nD q : ℕ) : ℝ) ^ 3 / 2 ^ 512 := by gcongr
    _ ≤ 37 * (6 * q + 2 ^ 67) ^ 3 / 2 ^ 512 := by gcongr

set_option exponentiation.threshold 1100 in
/-- **The square-rooted capacity rate, linear in the grade**: `√(epsQ q) ≤ 15 · 2^-214 (6q +
2^67)` for `q ≤ 2^84`. -/
theorem sqrt_epsQ_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) :
    √(epsQ q) ≤ 15 / 2 ^ 214 * (6 * q + 2 ^ 67) := by
  have hq' : (q : ℝ) ≤ 2 ^ 84 := by exact_mod_cast hq
  have hP0 : (0 : ℝ) ≤ 6 * q + 2 ^ 67 := by positivity
  have h1 : 37 * (6 * (q : ℝ) + 2 ^ 67) ≤ 225 * 2 ^ 84 := by linarith
  have h : epsQ q ≤ (15 / 2 ^ 214 * (6 * q + 2 ^ 67)) ^ 2 := by
    refine (epsQ_le_cube q).trans ?_
    have e1 : 37 * (6 * (q : ℝ) + 2 ^ 67) ^ 3 / 2 ^ 512 =
        37 * (6 * q + 2 ^ 67) * ((6 * q + 2 ^ 67) ^ 2 / 2 ^ 512) := by ring
    have e2 : (15 / 2 ^ 214 * (6 * (q : ℝ) + 2 ^ 67)) ^ 2 =
        225 * 2 ^ 84 * ((6 * q + 2 ^ 67) ^ 2 / 2 ^ 512) := by ring
    rw [e1, e2]
    gcongr
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (by positivity))

set_option exponentiation.threshold 1100 in
/-- `√(epsQ q) ≤ 2^-123` for `q ≤ 2^84`. -/
theorem sqrt_epsQ_le {q : ℕ} (hq : q ≤ 2 ^ 84) : √(epsQ q) ≤ (2 ^ 123 : ℝ)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 84 := by exact_mod_cast hq
  refine (sqrt_epsQ_le_lin hq).trans ?_
  linarith

/-- `epsQ q` as the square of its root. -/
theorem epsQ_eq_sqrt_mul (q : ℕ) : epsQ q = √(epsQ q) * √(epsQ q) :=
  (Real.mul_self_sqrt (epsQ_nonneg q)).symm

set_option exponentiation.threshold 1100 in
/-- `epsQ q ≤ 2^-246` for `q ≤ 2^84`. -/
theorem epsQ_le_two_pow {q : ℕ} (hq : q ≤ 2 ^ 84) : epsQ q ≤ (2 ^ 246 : ℝ)⁻¹ := by
  have hr := sqrt_epsQ_le hq
  have hr0 := Real.sqrt_nonneg (epsQ q)
  rw [epsQ_eq_sqrt_mul]
  calc √(epsQ q) * √(epsQ q) ≤ (2 ^ 123 : ℝ)⁻¹ * (2 ^ 123 : ℝ)⁻¹ :=
        mul_le_mul hr hr hr0 (by positivity)
    _ = (2 ^ 246 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 1100 in
/-- `epsQ q ≤ 2^-123 · 15 · 2^-214 (6q + 2^67)` for `q ≤ 2^84`. -/
theorem epsQ_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) :
    epsQ q ≤ (2 ^ 123 : ℝ)⁻¹ * (15 / 2 ^ 214 * (6 * q + 2 ^ 67)) := by
  have hr0 := Real.sqrt_nonneg (epsQ q)
  rw [epsQ_eq_sqrt_mul]
  exact mul_le_mul (sqrt_epsQ_le hq) (sqrt_epsQ_le_lin hq) hr0 (by positivity)

theorem sqrt_six_le : √(6 : ℝ) ≤ 49 / 20 :=
  (Real.sqrt_le_sqrt (by norm_num : (6 : ℝ) ≤ (49 / 20) ^ 2)).trans_eq
    (Real.sqrt_sq (by norm_num))

set_option exponentiation.threshold 1100 in
/-- `2 √(6 epsQ q) + 6 epsQ q ≤ 5 · 2^-123` for `q ≤ 2^84`. -/
theorem sponge_rate_le {q : ℕ} (hq : q ≤ 2 ^ 84) :
    2 * √(6 * epsQ q) + 6 * epsQ q ≤ 5 / 2 ^ 123 := by
  have hr := sqrt_epsQ_le hq
  have hr0 := Real.sqrt_nonneg (epsQ q)
  have he := epsQ_le_two_pow hq
  have h6 : √(6 * epsQ q) ≤ 49 / 20 * (2 ^ 123 : ℝ)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num)]
    exact mul_le_mul sqrt_six_le hr hr0 (by norm_num)
  linarith

set_option exponentiation.threshold 1100 in
theorem two_div_card_X_le : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
  rw [card_X]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num

set_option exponentiation.threshold 1100 in
theorem two_div_card_Z_le : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
  rw [card_Z]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num

set_option exponentiation.threshold 1100 in
/-- The read rate `epsQ q + 2/|X| + 2/|Z| + 2 √(epsQ q)` at most `31 · 2^-214 (6q + 2^67) +
2^-509` for `q ≤ 2^84`. -/
theorem read_rate_le {q : ℕ} (hq : q ≤ 2 ^ 84) :
    epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q) ≤
      31 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 509 : ℝ)⁻¹ := by
  have hl := sqrt_epsQ_le_lin hq
  have he := epsQ_le_lin hq
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  linarith

end grade

/-! ## The caps at `q ≤ 2^84` -/

section caps

set_option exponentiation.threshold 1100 in
/-- `kapS q ≤ 5 · 2^-123 (6q + 2^67)` for `q ≤ 2^84`. -/
theorem kapS_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) : kapS q ≤ 5 / 2 ^ 123 * (6 * q + 2 ^ 67) := by
  have hb := sponge_rate_le hq
  have hb0 : 0 ≤ 2 * √(6 * epsQ q) + 6 * epsQ q := by
    have := epsQ_nonneg q
    positivity
  unfold kapS
  calc (potCap q : ℝ) * (2 * √(6 * epsQ q) + 6 * epsQ q)
      ≤ (6 * q + 2 ^ 67) * (5 / 2 ^ 123) := mul_le_mul (potCap_le_lin q) hb hb0 (by positivity)
    _ = _ := by ring

set_option exponentiation.threshold 1100 in
/-- `kapR6 q ≤ 2^-121 (6q + 2^67) + 2^-1000` for `q ≤ 2^84`. -/
theorem kapR6_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) :
    kapR6 q ≤ (6 * q + 2 ^ 67) / 2 ^ 121 + (2 ^ 1000 : ℝ)⁻¹ := by
  have he := epsQ_le_two_pow hq
  have hr := sqrt_epsQ_le hq
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  have hb : epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q) ≤
      (2 ^ 121 : ℝ)⁻¹ := by linarith
  have hb0 : 0 ≤ epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q) := by
    have := epsQ_nonneg q
    positivity
  have hX6 : (6 : ℝ) / Fintype.card X ≤ (2 ^ 1000 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold kapR6
  calc (potCap q : ℝ) * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) +
        6 / (Fintype.card X : ℝ)
      ≤ (6 * q + 2 ^ 67) * (2 ^ 121 : ℝ)⁻¹ + (2 ^ 1000 : ℝ)⁻¹ :=
        add_le_add (mul_le_mul (potCap_le_lin q) hb hb0 (by positivity)) hX6
    _ = _ := by ring

set_option exponentiation.threshold 1100 in
/-- `kapRRAt (nW + nD q) ≤ 31 · 2^-214 (6q + 2^67) + 2^-148` for `q ≤ 2^84`. -/
theorem kapRRAt_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) :
    kapRRAt (nW + nD q) ≤ 31 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 148 : ℝ)⁻¹ := by
  have hl := sqrt_epsQ_le_lin hq
  have he := epsQ_le_lin hq
  have hr0 := Real.sqrt_nonneg (epsQ q)
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 : 0 ≤ 15 / 2 ^ 214 * (6 * (q : ℝ) + 2 ^ 67) := by positivity
  have hrr : √(epsQ q) * √(epsQ q) ≤ (15 / 2 ^ 214 * (6 * (q : ℝ) + 2 ^ 67)) *
      (15 / 2 ^ 214 * (6 * (q : ℝ) + 2 ^ 67)) := mul_le_mul hl hl hr0 hs0
  have hs : √(epsQ q + (2 ^ 301 : ℝ)⁻¹) ≤ 15 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 150 : ℝ)⁻¹ := by
    refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
    rw [epsQ_eq_sqrt_mul]
    nlinarith
  have e : rhoAt (nW + nD q) = epsQ q + (2 ^ 301 : ℝ)⁻¹ := rfl
  unfold kapRRAt
  rw [e]
  linarith

set_option exponentiation.threshold 1100 in
/-- `recS q ≤ 51 · 2^-83` for `q ≤ 2^84`. -/
theorem recS_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) : recS q ≤ 51 / 2 ^ 83 := by
  have hb := sponge_rate_le hq
  have hb0 : 0 ≤ 2 * √(6 * epsQ q) + 6 * epsQ q := by
    have := epsQ_nonneg q
    positivity
  unfold recS
  calc (recN : ℝ) * (2 * √(6 * epsQ q) + 6 * epsQ q)
      ≤ (10 * 2 ^ 40 + 1) * (5 / 2 ^ 123) := mul_le_mul recN_le_lin hb hb0 (by positivity)
    _ ≤ 51 / 2 ^ 83 := by norm_num

/-- `recR q ≤ (10 · 2^40 + 1) (31 · 2^-214 (6q + 2^67) + 2^-509)` for `q ≤ 2^84`. -/
theorem recR_le_lin {q : ℕ} (hq : q ≤ 2 ^ 84) :
    recR q ≤ (10 * 2 ^ 40 + 1) * (31 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 509 : ℝ)⁻¹) := by
  have hb0 : 0 ≤ epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q) := by
    have := epsQ_nonneg q
    positivity
  unfold recR
  exact mul_le_mul recN_le_lin (read_rate_le hq) hb0 (by positivity)

set_option exponentiation.threshold 1100 in
/-- `progBoundAt (nW + nD q) ≤ 2^-126` for `q ≤ 2^84`. -/
theorem progBoundAt_le {q : ℕ} (hq : q ≤ 2 ^ 84) :
    progBoundAt (nW + nD q) ≤ ENNReal.ofReal (1 / 2 ^ 126) := by
  have he : ENNReal.ofReal (epsLev (nW + nD q) 18) ≤ ENNReal.ofReal (2 ^ 246 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (epsQ_le_two_pow hq)
  have hp := progCap_le_five
  unfold progBoundAt keyBadCap
  grw [he]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- `6q + clsCap ≤ 2^88` for `q ≤ 2^84`. -/
theorem clsGrade_le {q : ℕ} (hq : q ≤ 2 ^ 84) : 6 * q + clsCap ≤ 2 ^ 88 := by
  have h84 : q ≤ 19342813113834066795298816 := hq
  have hl : lifetime = 4294967296 := by simp [lifetime, layerCount, layerHeight]
  have h88 : (2 : ℕ) ^ 88 = 309485009821345068724781056 := by norm_num
  rw [clsCap, signBlocks_eq, verifyBlocks_eq, progCap_eq, hl, h88]
  omega

set_option exponentiation.threshold 1100 in
/-- The fresh constant below `2^88` cells: `cwFreshEps G ≤ 2^-330`. -/
theorem cwFreshEps_le_of_88 {G : ℕ} (hG : G ≤ 2 ^ 88) : cwFreshEps G ≤ 1 / 2 ^ 330 := by
  have hG' : (G : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hG
  have h2 : (G : ℝ) * G ≤ 2 ^ 88 * 2 ^ 88 := mul_le_mul hG' hG' (Nat.cast_nonneg G) (by positivity)
  unfold cwFreshEps
  rw [card_Z]
  push_cast
  nlinarith

set_option exponentiation.threshold 1100 in
/-- **The flip-value recorded mass**: `flipMassCap q ≤ 6 q 2^-94 + 2^-60` for `q ≤ 2^84`. -/
theorem flipMassCap_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) :
    flipMassCap q ≤ ENNReal.ofReal (6 * q / 2 ^ 94 + 1 / 2 ^ 60) := by
  have hf : ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) ≤ ENNReal.ofReal (1 / 2 ^ 330) :=
    ENNReal.ofReal_le_ofReal (cwFreshEps_le_of_88 (clsGrade_le hq))
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

end caps

/-! ## The verification terms at `q ≤ 2^84` -/

section ver

set_option exponentiation.threshold 1100 in
/-- The entries below which the verification's fresh bound is taken: below `2^88`. -/
theorem verEntries_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) :
    progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1 ≤ 2 ^ 88 := by
  have h84 : q ≤ 19342813113834066795298816 := hq
  have hl : lifetime = 4294967296 := by simp [lifetime, layerCount, layerHeight]
  have h88 : (2 : ℕ) ^ 88 = 309485009821345068724781056 := by norm_num
  rw [clsCap, signBlocks_eq, verifyBlocks_eq, progCap_eq, hl, h88]
  omega

set_option exponentiation.threshold 1100 in
/-- `verEps q ≤ 2^-128` for `q ≤ 2^84`. -/
theorem verEps_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) : verEps q ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (preimageRateBound_le_cube (by norm_num) _ _).trans (max_le ?_ ?_)
  · rw [card_X]
    exact natCast_div_le_inv_two_pow (pow_add 2 960 128).symm.le
  · rw [card_Z]
    refine natCast_div_le_inv_two_pow ?_
    calc 3 * 18 * (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1) ^ 3 * 2 ^ 128
        ≤ 3 * 18 * (2 ^ 88) ^ 3 * 2 ^ 128 := by gcongr; exact verEntries_le_84 hq
      _ ≤ 2 ^ 6 * (2 ^ 88) ^ 3 * 2 ^ 128 := by gcongr; norm_num
      _ = 2 ^ 398 := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

set_option exponentiation.threshold 1100 in
/-- `verTerm q ≤ 1194 · 2^-64` for `q ≤ 2^84`. -/
theorem verTerm_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) : verTerm q ≤ ENNReal.ofReal (1194 / 2 ^ 64) := by
  have h2 : ((2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) = (2 ^ 64 : ℝ≥0∞)⁻¹ := by
    rw [show (2 ^ 128 : ℝ≥0∞) = (2 ^ 64) ^ 2 by rw [← pow_mul],
      ENNReal.inv_pow (a := (2 ^ 64 : ℝ≥0∞)) (n := 2), pow_two_rpow_inv_two]
  have h := ENNReal.rpow_le_rpow (verEps_le_84 hq) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  rw [h2] at h
  unfold verTerm
  rw [verifyBlocks_eq]
  calc ((3 * 398 : ℕ) : ℝ≥0∞) * verEps q ^ (2⁻¹ : ℝ) ≤ ((3 * 398 : ℕ) : ℝ≥0∞) * (2 ^ 64)⁻¹ := by
        gcongr
    _ = ENNReal.ofReal (1194 / 2 ^ 64) := by
        simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
        congr 1

set_option exponentiation.threshold 1100 in
/-- `verLin q ≤ 3582 · 2^-128` for `q ≤ 2^84`. -/
theorem verLin_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) : verLin q ≤ 3582 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have hE := verEps_le_84 hq
  have hX : (2 : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_X]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hZ : (2 : ℝ≥0∞) / (Fintype.card Z : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_Z]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  unfold verLin keepCost
  rw [verifyBlocks_eq]
  calc ((3 * 398 : ℕ) : ℝ≥0∞) * (verEps q + 2 / (Fintype.card X : ℝ≥0∞) +
        2 / (Fintype.card Z : ℝ≥0∞)) ≤
        ((3 * 398 : ℕ) : ℝ≥0∞) * ((2 ^ 128)⁻¹ + (2 ^ 128)⁻¹ + (2 ^ 128)⁻¹) := by
        gcongr
    _ = 3582 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        rw [show (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 128)⁻¹ + (2 ^ 128)⁻¹ = 3 * (2 ^ 128)⁻¹ by ring,
          ← mul_assoc]
        norm_num

set_option exponentiation.threshold 1100 in
/-- `progBoundAt (nW + nD q) + verLin q ≤ 2^-116` for `q ≤ 2^84`. -/
theorem progVer_le_84 {q : ℕ} (hq : q ≤ 2 ^ 84) :
    progBoundAt (nW + nD q) + verLin q ≤ ENNReal.ofReal (1 / 2 ^ 116) := by
  grw [progBoundAt_le hq, verLin_le_84 hq]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end ver

/-! ## The classical costs -/

section cls

set_option exponentiation.threshold 4096 in
/-- **The Enc term of `clsBoundD`** for `q ≤ 2^84`: at most `7110² 2^-128 q + (43 · 2^-94 q)² +
(63 · 2^-36)²` (the `q²` part is the `RecJ` weight times the program-jump factor). -/
theorem encInD_le {q : ℕ} (hq : q ≤ 2 ^ 84) :
    encECAt (nW + nD q) q + 2 * encBeta q * flipMassCap q +
        2 * encGamma q * (progBoundAt (nW + nD q) + recCapAt (nW + nD q) q) ≤
      ENNReal.ofReal ((7110 / 2 ^ 64) ^ 2 * q + (43 / 2 ^ 94 * q) ^ 2 + (63 / 2 ^ 36) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hS : ENNReal.ofReal (kapS q) ≤ ENNReal.ofReal (5 / 2 ^ 123 * (6 * q + 2 ^ 67)) :=
    ENNReal.ofReal_le_ofReal (kapS_le_lin hq)
  have hR6 : ENNReal.ofReal (kapR6 q) ≤
      ENNReal.ofReal ((6 * q + 2 ^ 67) / 2 ^ 121 + (2 ^ 1000 : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal (kapR6_le_lin hq)
  have hRR : ENNReal.ofReal (kapRRAt (nW + nD q)) ≤
      ENNReal.ofReal (31 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 148 : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal (kapRRAt_le_lin hq)
  have hrS : ENNReal.ofReal (recS q) ≤ ENNReal.ofReal (51 / 2 ^ 83) :=
    ENNReal.ofReal_le_ofReal (recS_le_lin hq)
  have hrR : ENNReal.ofReal (recR q) ≤ ENNReal.ofReal
      ((10 * 2 ^ 40 + 1) * (31 / 2 ^ 214 * (6 * q + 2 ^ 67) + (2 ^ 509 : ℝ)⁻¹)) :=
    ENNReal.ofReal_le_ofReal (recR_le_lin hq)
  have hF := flipMassCap_le_84 hq
  have hB := progBoundAt_le hq
  have hN : ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) ≤ ENNReal.ofReal (3 * (6 * q + 2 ^ 67)) :=
    ENNReal.ofReal_le_ofReal (by linarith [nWD_le_lin q])
  have hP : (potCap q : ℝ≥0∞) ≤ ENNReal.ofReal (6 * q + 2 ^ 67) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (potCap_le_lin q)
  have hc : (clsCap : ℝ≥0∞) ≤ ENNReal.ofReal (102 * 2 ^ 60) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal clsCap_le_102
  have hn : (recN : ℝ≥0∞) ≤ ENNReal.ofReal (10 * 2 ^ 40 + 1) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal recN_le_lin
  have h6p : ((6 * q + progCap : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (6 * q + 5 * 2 ^ 40) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [progCap_le_five]
  have h6 : ((6 * q : ℕ) : ℝ≥0∞) = ENNReal.ofReal (6 * q) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hZ2 : ENNReal.ofReal (2 / Fintype.card Z) = ENNReal.ofReal (2 / 2 ^ 512) := by
    rw [card_Z, Nat.cast_pow, Nat.cast_ofNat]
  unfold encECAt recCapAt encE0 encBeta encGamma encDelta
  rw [h6, hZ2]
  grw [h6p, hS, hR6, hRR, hrS, hrR, hF, hB, hN, hP, hc, hn]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
  ring_nf
  ring_nf at hq2
  linarith

/-- `x ≤ c₁² q + (e q)² + a₀²` gives `√x ≤ c₁ √q + e q + a₀`. -/
theorem rpow_inv_two_le_of_quad {x : ℝ≥0∞} {q c₁ e a₀ : ℝ} (hq : 0 ≤ q) (hc₁ : 0 ≤ c₁)
    (he : 0 ≤ e) (ha₀ : 0 ≤ a₀) (hx : x ≤ ENNReal.ofReal (c₁ ^ 2 * q + (e * q) ^ 2 + a₀ ^ 2)) :
    x ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (c₁ * √q + e * q + a₀) := by
  have hs0 := Real.sqrt_nonneg q
  have hsq := Real.sq_sqrt hq
  refine rpow_inv_two_le_ofReal (by positivity) hx ?_
  have h1 : 0 ≤ c₁ * √q * (e * q) := by positivity
  have h2 : 0 ≤ c₁ * √q * a₀ := by positivity
  have h3 : 0 ≤ e * q * a₀ := by positivity
  have e1 : (c₁ * √q + e * q + a₀) ^ 2 = c₁ ^ 2 * √q ^ 2 + (e * q) ^ 2 + a₀ ^ 2 +
      2 * (c₁ * √q * (e * q)) + 2 * (c₁ * √q * a₀) + 2 * (e * q * a₀) := by
    ring
  rw [e1, hsq]
  linarith

set_option exponentiation.threshold 1100 in
/-- **The classical costs and the verification's linear term, square-rooted**: for `q ≤ 2^84`,
`√(clsBoundD q + verLin q) ≤ 7110 √q 2^-64 + 43 q 2^-94 + 63 · 2^-36 + (2.45 √q 2^-47 + 2^-30) +
2^-58`. -/
theorem clsVer_rpow_leD {q : ℕ} (hq : q ≤ 2 ^ 84) :
    (clsBoundD q + verLin q) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (7110 / 2 ^ 64 * √(q : ℝ) +
      43 / 2 ^ 94 * q + 63 / 2 ^ 36 + (49 / 20 * √(q : ℝ) / 2 ^ 47 + 1 / 2 ^ 30) + 1 / 2 ^ 58) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hE := rpow_inv_two_le_of_quad hq0 (by positivity) (by positivity) (by positivity)
    (encInD_le hq)
  have hF := rpow_inv_two_le_ofReal (a := 49 / 20 * √(q : ℝ) / 2 ^ 47 + 1 / 2 ^ 30)
    (by positivity) (flipMassCap_le_84 hq) (by nlinarith)
  have hP := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 58) (by positivity) (progVer_le_84 hq)
    (by norm_num)
  unfold clsBoundD clsBoundAt
  rw [add_assoc]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add hE hF) hP).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end cls

/-! ## The depth terms and the closed form -/

section closed

set_option exponentiation.threshold 1100 in
/-- **The capacity residual**: `capTermD q ≤ q 2^-119` for `q ≤ 2^84`. -/
theorem capTermD_le {q : ℕ} (hq : q ≤ 2 ^ 84) : capTermD q ≤ ENNReal.ofReal (q / 2 ^ 119) := by
  have he : 6 * ENNReal.ofReal (epsQ q) ≤ ENNReal.ofReal (6 / 2 ^ 246) := by
    rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := epsQ_le_two_pow hq
    rw [div_eq_mul_inv]
    linarith
  have hs := rpow_inv_two_le_ofReal (a := 49 / 20 / 2 ^ 123) (by positivity) he (by norm_num)
  unfold capTermD
  grw [hs]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The adversary term at depth `d`**: `advTermD q d ≤ 4.9 √(q d') 2^-64 + q 2^-119` for
`q ≤ 2^84`, `d' = min d q`. -/
theorem advTermD_le {q d : ℕ} (hq : q ≤ 2 ^ 84) :
    advTermD q d ≤
      ENNReal.ofReal (49 / 10 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 119) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hsq := Real.sq_sqrt hX
  have hx : 6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (24 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) := by
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hh := rpow_inv_two_le_ofReal (a := 49 / 10 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64)
    (by positivity) hx (by
      have e : (49 / 10 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) ^ 2 =
          2401 / 100 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128 := by
        rw [div_pow, mul_pow, hsq]
        ring
      rw [e]
      linarith)
  unfold advTermD
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add hh (capTermD_le hq)

set_option exponentiation.threshold 1100 in
/-- **The hybrid term at depth `d`**: `hybTermD q d ≤ 15.5 √(q d') 2^-64 + 41 · 2^-34`
(`4 · 10 d' · 6q κ ≤ 240.25 q d' 2^-128`). -/
theorem hybTermD_le (q d : ℕ) :
    hybTermD q d ≤ ENNReal.ofReal (31 / 2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 41 / 2 ^ 34) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hsq := Real.sq_sqrt hX
  have hs : 4 * (((10 * min d q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS)) ≤
      ENNReal.ofReal (240 * ((q : ℝ) * (min d q : ℕ)) * ((2 ^ 128)⁻¹ + (2 ^ 189)⁻¹)) := by
    unfold kappaS
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_add]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hh := rpow_inv_two_le_ofReal (a := 31 / 2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64)
    (by positivity) hs (by
      have e : (31 / 2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) ^ 2 =
          961 / 4 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128 := by
        rw [div_pow, mul_pow, hsq]
        ring
      rw [e]
      nlinarith)
  unfold hybTermD
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add hh (rpow_inv_two_le_ofReal (by positivity) readCap_le (by norm_num))

set_option exponentiation.threshold 1100 in
/-- **The square-rooted event term at depth `d`** for `q ≤ 2^84`. -/
theorem eventTermD_rpow_le {q d : ℕ} (hq : q ≤ 2 ^ 84) :
    eventTermD q d ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal
      (49 / 10 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 119 + 1194 / 2 ^ 64 +
        (7110 / 2 ^ 64 * √(q : ℝ) + 43 / 2 ^ 94 * q + 63 / 2 ^ 36 +
          (49 / 20 * √(q : ℝ) / 2 ^ 47 + 1 / 2 ^ 30) + 1 / 2 ^ 58) + 1 / 2 ^ 84) := by
  have hs := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 84) (by positivity) restTerms_le (by norm_num)
  unfold eventTermD
  rw [add_assoc, add_assoc]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add (add_le_add
    (advTermD_le hq) (verTerm_le_84 hq)) (clsVer_rpow_leD hq)) hs).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The arithmetic of the closed form: the sum of the term bounds is at most
`(20.4 √(q d') + 11 · 2^-28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64 - 2^-34`, which absorbs
`r0Term`. -/
theorem root_sq_leD (q m : ℕ) :
    (49 / 10 * √((q : ℝ) * m) / 2 ^ 64 + q / 2 ^ 119 + 1194 / 2 ^ 64 +
        (7110 / 2 ^ 64 * √(q : ℝ) + 43 / 2 ^ 94 * q + 63 / 2 ^ 36 +
          (49 / 20 * √(q : ℝ) / 2 ^ 47 + 1 / 2 ^ 30) + 1 / 2 ^ 58) + 1 / 2 ^ 84 +
      (31 / 2 * √((q : ℝ) * m) / 2 ^ 64 + 41 / 2 ^ 34)) ^ 2 + 1 / 2 ^ 173 ≤
      ((102 / 5 * √((q : ℝ) * m) + 11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) /
        2 ^ 64) ^ 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hm0 := Real.sqrt_nonneg ((q : ℝ) * m)
  set F := (102 / 5 * √((q : ℝ) * m) + 11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) /
    2 ^ 64 with hF
  have h1 : 49 / 10 * √((q : ℝ) * m) / 2 ^ 64 + q / 2 ^ 119 + 1194 / 2 ^ 64 +
      (7110 / 2 ^ 64 * √(q : ℝ) + 43 / 2 ^ 94 * q + 63 / 2 ^ 36 +
        (49 / 20 * √(q : ℝ) / 2 ^ 47 + 1 / 2 ^ 30) + 1 / 2 ^ 58) + 1 / 2 ^ 84 +
      (31 / 2 * √((q : ℝ) * m) / 2 ^ 64 + 41 / 2 ^ 34) ≤ F - 1 / 2 ^ 34 := by
    rw [hF]
    linarith
  have h2 : 75 / 2 ^ 34 ≤ F := by
    rw [hF]
    linarith
  calc _ ≤ (F - 1 / 2 ^ 34) ^ 2 + 1 / 2 ^ 173 := by gcongr
    _ ≤ F ^ 2 := by nlinarith

/-- **The depth-aware leanXMSS QRPM bound in closed form**: for `q ≤ 2^84` and every `d`, with
`d' = min d q`,
`qrpmDepthBound q d ≤ ((20.4 √(q d') + 11 · 2^-28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`. -/
theorem qrpmDepthBound_le {q d : ℕ} (hq : q ≤ 2 ^ 84) :
    qrpmDepthBound q d ≤ ENNReal.ofReal (((102 / 5 * √((q : ℝ) * (min d q : ℕ)) +
      11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermD_rpow_le (d := d) hq
  have h2 := hybTermD_le q d
  have h3 := r0Term_le
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (root_sq_leD q (min d q)))
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold qrpmDepthBound
  gcongr

set_option exponentiation.threshold 1100 in
/-- **At most `2^80` permutation calls in at most `2^28` rounds**: `qrpmDepthBound q d ≤ 2^-9`. -/
theorem qrpmDepthBound_two_pow_80_28_le {q d : ℕ} (hq : q ≤ 2 ^ 80) (hd : d ≤ 2 ^ 28) :
    qrpmDepthBound q d ≤ (2 ^ 9 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 80 := by exact_mod_cast hq
  have hm : ((min d q : ℕ) : ℝ) ≤ 2 ^ 28 := by exact_mod_cast (min_le_left d q).trans hd
  have hs : √(q : ℝ) ≤ 2 ^ 40 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 80 = (2 ^ 40) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  have hsm : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 54 :=
    (Real.sqrt_le_sqrt (mul_le_mul hq' hm (Nat.cast_nonneg _) (by positivity))).trans_eq
      (by rw [show (2 : ℝ) ^ 80 * 2 ^ 28 = (2 ^ 54) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  refine (qrpmDepthBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((102 / 5 * √((q : ℝ) * (min d q : ℕ)) + 11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) +
        75 * 2 ^ 30) / 2 ^ 64) ^ 2
      ≤ ((102 / 5 * 2 ^ 54 + 11 * 2 ^ 80 / 2 ^ 28 + 21 * 2 ^ 14 * 2 ^ 40 + 75 * 2 ^ 30) /
          2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 9 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^64` permutation calls in at most `2^40` rounds**: `qrpmDepthBound q d ≤
2^-15`. -/
theorem qrpmDepthBound_two_pow_64_40_le {q d : ℕ} (hq : q ≤ 2 ^ 64) (hd : d ≤ 2 ^ 40) :
    qrpmDepthBound q d ≤ (2 ^ 15 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hm : ((min d q : ℕ) : ℝ) ≤ 2 ^ 40 := by exact_mod_cast (min_le_left d q).trans hd
  have hs : √(q : ℝ) ≤ 2 ^ 32 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 64 = (2 ^ 32) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  have hsm : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 52 :=
    (Real.sqrt_le_sqrt (mul_le_mul hq' hm (Nat.cast_nonneg _) (by positivity))).trans_eq
      (by rw [show (2 : ℝ) ^ 64 * 2 ^ 40 = (2 ^ 52) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  refine (qrpmDepthBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((102 / 5 * √((q : ℝ) * (min d q : ℕ)) + 11 * q / 2 ^ 28 + 21 * 2 ^ 14 * √(q : ℝ) +
        75 * 2 ^ 30) / 2 ^ 64) ^ 2
      ≤ ((102 / 5 * 2 ^ 52 + 11 * 2 ^ 64 / 2 ^ 28 + 21 * 2 ^ 14 * 2 ^ 32 + 75 * 2 ^ 30) /
          2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 15 := by norm_num

end closed

end Quantum.Xmss.Assembly

end
