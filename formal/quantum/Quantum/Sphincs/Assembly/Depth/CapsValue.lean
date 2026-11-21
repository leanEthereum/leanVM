module

public import Quantum.Sphincs.Assembly.Depth.Caps
public import Quantum.Sphincs.Assembly.BoundValue
public import Quantum.Xmss.Assembly.Depth.BoundValue
public import Quantum.Xmss.Assembly.Depth.Event

@[expose] public section

/-!
# The size of leanSPHINCS's depth-aware classical caps

Caps' `clsBoundSD q` in closed form for `q ≤ 2^88` (`clsBoundSD_rpow_le`):
`√clsBoundSD q ≤ (641 √q + 7 · 2^-28 q + 19 · 2^30) / 2^64`.

* **The capacity rate at the prefix's grade** `T = nW progCap + 6q + clsCap ≤ 6q + 2^66`:
  `epsQ (6q + clsCap) progCap ≤ 37 (6q + 2^66)³ / 2^512` for every `q` (`epsS_le_cube`), hence for
  `q ≤ 2^88` `√epsQ ≤ (6q + 2^66) 2^-208` and `≤ 2^-117` (`sqrt_epsS_le_lin`, `sqrt_epsS_le`).
* **The Enc term of `clsBoundSD`** (`encInSD_le`): at most `(636 · 2^-64)² q + (28 · 2^-94 q)² +
  (9 · 2^-34)²`. Its `q²` part is the `RecJ` weight times the Enc program-jump factor,
  `2 encGamma q · 6q rjS`: the `RecJ` charge per sponge call `rjN progCap · 2 √(6 epsQ)` grows
  like `q^1.5`, so this term grows like `q^3.5`; it is absorbed into `q²` with `q ≤ 2^88` and is
  what limits the range (alone it reaches `1` near `q = 2^88.9`). The flip-value recorded mass is
  `flipCapS q cfEps ≤ 6q 2^-126 + 81 · 2^-68` (`flipCapS_le_88`).
* **The capacity rates of the depth event bound** (`capRateBound_le_cube`, `capRate_le_cube`,
  `rpow_capRateBound_le`): at the grades `progCap + 6q + clsCap + 1` (adversary) and
  `progCap + 6q + clsCap + 3 verifyBlocks + 1` (verification), at most `37 (6q + 2^66)³ / 2^512`,
  and `√(12 capRateBound) ≤ (6q + 2^66) 2^-206` for `q ≤ 2^88`.
-/

open scoped ENNReal

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (rpow_inv_two_le_ofReal sq_add_rpow_inv_two_le rpow_inv_two_le_of_quad
  capKJ_add_le_cube sqrt_six_le two_div_card_X_le two_div_card_Z_le card_Z epsLev capKJ capKJ'
  cwFreshEps)

namespace Quantum.Sphincs.Assembly

/-! ## The prefix's grade and the capacity rate -/

section grade

theorem two_pow_seven_le_progCap : 2 ^ 7 ≤ progCap := by
  rw [progCap_eq]
  norm_num [signatureLimit]

/-- The prefix's grade: `nW progCap + 6q + clsCap ≤ 6q + 2^66`. -/
theorem gradeS_le_lin (q : ℕ) : ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ) ≤ 6 * q + 2 ^ 66 := by
  have hc := clsCap_le_sph
  have hp := progCap_le_sph
  unfold nW
  push_cast
  linarith

theorem potCap_le_linS (q : ℕ) : (potCap (6 * q + clsCap) progCap : ℝ) ≤ 6 * q + 2 ^ 66 := by
  have hc := clsCap_le_sph
  have hp := progCap_le_sph
  unfold potCap nW
  push_cast
  linarith

/-- The capacity counts below `T` entries over `|Z|`, cubed: for `2^7 ≤ T ≤ B`, any `N` at most
`capKJ T 18 + capKJ' T 18` gives `N / |Z| ≤ 37 B³ / 2^512`. -/
theorem capCount_div_le {T N : ℕ} (hT : 2 ^ 7 ≤ T) (hN : N ≤ capKJ T 18 + capKJ' T 18) {B : ℝ}
    (hB : (T : ℝ) ≤ B) : (N : ℝ) / Fintype.card Z ≤ 37 * B ^ 3 / 2 ^ 512 := by
  have h : (N : ℝ) ≤ 37 * (T : ℝ) ^ 3 := by exact_mod_cast hN.trans (capKJ_add_le_cube hT)
  have h0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  rw [card_Z, Nat.cast_pow, Nat.cast_ofNat]
  calc (N : ℝ) / 2 ^ 512 ≤ 37 * (T : ℝ) ^ 3 / 2 ^ 512 := by gcongr
    _ ≤ 37 * B ^ 3 / 2 ^ 512 := by gcongr

set_option exponentiation.threshold 1100 in
/-- **The capacity rate at the prefix's grade**: `epsQ (6q + clsCap) progCap ≤
37 (6q + 2^66)³ / 2^512` for every `q`. -/
theorem epsS_le_cube (q : ℕ) :
    epsQ (6 * q + clsCap) progCap ≤ 37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512 := by
  have h7 : 2 ^ 7 ≤ nW progCap + (6 * q + clsCap) :=
    two_pow_seven_le_progCap.trans (by unfold nW; omega)
  unfold epsQ epsLev
  exact capCount_div_le h7 le_rfl (gradeS_le_lin q)

set_option exponentiation.threshold 1100 in
/-- **The square-rooted capacity rate, linear in the grade**: `√epsQ ≤ (6q + 2^66) 2^-208` for
`q ≤ 2^88`. -/
theorem sqrt_epsS_le_lin {q : ℕ} (hq : q ≤ 2 ^ 88) :
    √(epsQ (6 * q + clsCap) progCap) ≤ (6 * q + 2 ^ 66) / 2 ^ 208 := by
  have hq' : (q : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  have hP0 : (0 : ℝ) ≤ 6 * q + 2 ^ 66 := by positivity
  have h1 : 37 * (6 * (q : ℝ) + 2 ^ 66) ≤ 2 ^ 96 := by linarith
  have h : epsQ (6 * q + clsCap) progCap ≤ ((6 * q + 2 ^ 66) / 2 ^ 208) ^ 2 := by
    refine (epsS_le_cube q).trans ?_
    have e1 : 37 * (6 * (q : ℝ) + 2 ^ 66) ^ 3 / 2 ^ 512 =
        37 * (6 * q + 2 ^ 66) * ((6 * q + 2 ^ 66) ^ 2 / 2 ^ 512) := by ring
    have e2 : ((6 * (q : ℝ) + 2 ^ 66) / 2 ^ 208) ^ 2 =
        2 ^ 96 * ((6 * q + 2 ^ 66) ^ 2 / 2 ^ 512) := by ring
    rw [e1, e2]
    gcongr
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (by positivity))

set_option exponentiation.threshold 1100 in
/-- `√epsQ ≤ 2^-117` for `q ≤ 2^88`. -/
theorem sqrt_epsS_le {q : ℕ} (hq : q ≤ 2 ^ 88) :
    √(epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 117 : ℝ)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  refine (sqrt_epsS_le_lin hq).trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem epsS_eq_sqrt_mul (q : ℕ) :
    epsQ (6 * q + clsCap) progCap =
      √(epsQ (6 * q + clsCap) progCap) * √(epsQ (6 * q + clsCap) progCap) :=
  (Real.mul_self_sqrt (epsQ_nonneg _ _)).symm

set_option exponentiation.threshold 1100 in
/-- `epsQ ≤ 2^-234` for `q ≤ 2^88`. -/
theorem epsS_le_two_pow {q : ℕ} (hq : q ≤ 2 ^ 88) :
    epsQ (6 * q + clsCap) progCap ≤ (2 ^ 234 : ℝ)⁻¹ := by
  have hr := sqrt_epsS_le hq
  have hr0 := Real.sqrt_nonneg (epsQ (6 * q + clsCap) progCap)
  rw [epsS_eq_sqrt_mul]
  calc _ ≤ (2 ^ 117 : ℝ)⁻¹ * (2 ^ 117 : ℝ)⁻¹ := mul_le_mul hr hr hr0 (by positivity)
    _ = (2 ^ 234 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 1100 in
/-- `2 √(6 epsQ) + 6 epsQ ≤ 5 · 2^-117` for `q ≤ 2^88`. -/
theorem sponge_rate_leS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    2 * √(6 * epsQ (6 * q + clsCap) progCap) + 6 * epsQ (6 * q + clsCap) progCap ≤
      5 / 2 ^ 117 := by
  have hr := sqrt_epsS_le hq
  have hr0 := Real.sqrt_nonneg (epsQ (6 * q + clsCap) progCap)
  have he := epsS_le_two_pow hq
  have h6 : √(6 * epsQ (6 * q + clsCap) progCap) ≤ 49 / 20 * (2 ^ 117 : ℝ)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num)]
    exact mul_le_mul sqrt_six_le hr hr0 (by norm_num)
  linarith

set_option exponentiation.threshold 1100 in
/-- The read rate `epsQ + 2/|X| + 2/|Z| + 2 √epsQ ≤ 2^-115` for `q ≤ 2^88`. -/
theorem read_rate_leS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    epsQ (6 * q + clsCap) progCap + (2 / Fintype.card X + 2 / Fintype.card Z) +
      2 * √(epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 115 : ℝ)⁻¹ := by
  have hr := sqrt_epsS_le hq
  have he := epsS_le_two_pow hq
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  linarith

set_option exponentiation.threshold 1100 in
/-- The read rate, linear in the grade: at most `2 (6q + 2^66) 2^-208 + 2^-233` for
`q ≤ 2^88`. -/
theorem read_rate_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    epsQ (6 * q + clsCap) progCap + (2 / Fintype.card X + 2 / Fintype.card Z) +
      2 * √(epsQ (6 * q + clsCap) progCap) ≤
        2 * ((6 * q + 2 ^ 66) / 2 ^ 208) + (2 ^ 233 : ℝ)⁻¹ := by
  have hl := sqrt_epsS_le_lin hq
  have he := epsS_le_two_pow hq
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  linarith

end grade

/-! ## The caps at `q ≤ 2^88` -/

section caps

set_option exponentiation.threshold 1100 in
/-- `kapS ≤ 5 · 2^-117 (6q + 2^66)` for `q ≤ 2^88`. -/
theorem kapS_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    kapS (6 * q + clsCap) progCap ≤ 5 / 2 ^ 117 * (6 * q + 2 ^ 66) := by
  have hb := sponge_rate_leS hq
  have hb0 : 0 ≤ 2 * √(6 * epsQ (6 * q + clsCap) progCap) + 6 * epsQ (6 * q + clsCap) progCap := by
    have := epsQ_nonneg (6 * q + clsCap) progCap
    positivity
  unfold kapS
  calc (potCap (6 * q + clsCap) progCap : ℝ) *
        (2 * √(6 * epsQ (6 * q + clsCap) progCap) + 6 * epsQ (6 * q + clsCap) progCap)
      ≤ (6 * q + 2 ^ 66) * (5 / 2 ^ 117) :=
        mul_le_mul (potCap_le_linS q) hb hb0 (by positivity)
    _ = _ := by ring

set_option exponentiation.threshold 1100 in
/-- `kapR6 ≤ (6q + 2^66) 2^-115 + 2^-1000` for `q ≤ 2^88`. -/
theorem kapR6_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    kapR6 (6 * q + clsCap) progCap ≤ (6 * q + 2 ^ 66) / 2 ^ 115 + (2 ^ 1000 : ℝ)⁻¹ := by
  have hb := read_rate_leS hq
  have hb0 : 0 ≤ epsQ (6 * q + clsCap) progCap + (2 / Fintype.card X + 2 / Fintype.card Z) +
      2 * √(epsQ (6 * q + clsCap) progCap) := by
    have := epsQ_nonneg (6 * q + clsCap) progCap
    positivity
  have hX6 : (6 : ℝ) / Fintype.card X ≤ (2 ^ 1000 : ℝ)⁻¹ := by
    rw [Quantum.Xmss.card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold kapR6
  calc (potCap (6 * q + clsCap) progCap : ℝ) * (epsQ (6 * q + clsCap) progCap +
        (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ (6 * q + clsCap) progCap)) +
        6 / (Fintype.card X : ℝ)
      ≤ (6 * q + 2 ^ 66) * (2 ^ 115 : ℝ)⁻¹ + (2 ^ 1000 : ℝ)⁻¹ :=
        add_le_add (mul_le_mul (potCap_le_linS q) hb hb0 (by positivity)) hX6
    _ = _ := by ring

set_option exponentiation.threshold 1100 in
/-- `kapRRAt ≤ 3 (6q + 2^66) 2^-208 + 2^-148` at the prefix's grade, for `q ≤ 2^88`. -/
theorem kapRRAt_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    kapRRAt (nW progCap + (6 * q + clsCap)) ≤ 3 / 2 ^ 208 * (6 * q + 2 ^ 66) + (2 ^ 148 : ℝ)⁻¹ := by
  have hl := sqrt_epsS_le_lin hq
  have he := epsS_le_two_pow hq
  have hr0 := Real.sqrt_nonneg (epsQ (6 * q + clsCap) progCap)
  have hX := two_div_card_X_le
  have hZ := two_div_card_Z_le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 : 0 ≤ (6 * (q : ℝ) + 2 ^ 66) / 2 ^ 208 := by positivity
  have hrr : √(epsQ (6 * q + clsCap) progCap) * √(epsQ (6 * q + clsCap) progCap) ≤
      ((6 * (q : ℝ) + 2 ^ 66) / 2 ^ 208) * ((6 * (q : ℝ) + 2 ^ 66) / 2 ^ 208) :=
    mul_le_mul hl hl hr0 hs0
  have e : rhoAt (nW progCap + (6 * q + clsCap)) =
      2 * epsQ (6 * q + clsCap) progCap + (2 ^ 301 : ℝ)⁻¹ := rfl
  have hs : √(rhoAt (nW progCap + (6 * q + clsCap))) ≤
      3 / 2 * ((6 * q + 2 ^ 66) / 2 ^ 208) + (2 ^ 150 : ℝ)⁻¹ := by
    refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
    rw [e, epsS_eq_sqrt_mul]
    nlinarith
  unfold kapRRAt
  rw [e]
  rw [e] at hs
  linarith

set_option exponentiation.threshold 1100 in
/-- `rjS ≤ 5 · 2^-74` for `q ≤ 2^88`. -/
theorem rjS_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) : rjS (6 * q + clsCap) progCap ≤ 5 / 2 ^ 74 := by
  have hb := sponge_rate_leS hq
  have hb0 : 0 ≤ 2 * √(6 * epsQ (6 * q + clsCap) progCap) + 6 * epsQ (6 * q + clsCap) progCap := by
    have := epsQ_nonneg (6 * q + clsCap) progCap
    positivity
  unfold rjS
  calc (rjN progCap : ℝ) *
        (2 * √(6 * epsQ (6 * q + clsCap) progCap) + 6 * epsQ (6 * q + clsCap) progCap)
      ≤ 2 ^ 43 * (5 / 2 ^ 117) := mul_le_mul rjN_le hb hb0 (by positivity)
    _ = 5 / 2 ^ 74 := by norm_num

set_option exponentiation.threshold 1100 in
/-- `rjR ≤ (6q + 2^66) 2^-164 + 2^-190` for `q ≤ 2^88`. -/
theorem rjR_le_linS {q : ℕ} (hq : q ≤ 2 ^ 88) :
    rjR (6 * q + clsCap) progCap ≤ (6 * q + 2 ^ 66) / 2 ^ 164 + (2 ^ 190 : ℝ)⁻¹ := by
  have hb := read_rate_le_linS hq
  have hb0 : 0 ≤ epsQ (6 * q + clsCap) progCap + (2 / Fintype.card X + 2 / Fintype.card Z) +
      2 * √(epsQ (6 * q + clsCap) progCap) := by
    have := epsQ_nonneg (6 * q + clsCap) progCap
    positivity
  unfold rjR
  calc (rjN progCap : ℝ) * (epsQ (6 * q + clsCap) progCap +
        (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ (6 * q + clsCap) progCap))
      ≤ 2 ^ 43 * (2 * ((6 * q + 2 ^ 66) / 2 ^ 208) + (2 ^ 233 : ℝ)⁻¹) :=
        mul_le_mul rjN_le hb hb0 (by positivity)
    _ = (6 * q + 2 ^ 66) / 2 ^ 164 + (2 ^ 190 : ℝ)⁻¹ := by ring

set_option exponentiation.threshold 1100 in
/-- The averaged target-free flips at the prefix's grade: `kfCapAt ≤ 2^-192` for `q ≤ 2^88`. -/
theorem kfCapAt_le {q : ℕ} (hq : q ≤ 2 ^ 88) :
    kfCapAt (nW progCap + (6 * q + clsCap)) ≤ ENNReal.ofReal (1 / 2 ^ 192) := by
  have he : ENNReal.ofReal (epsLev (nW progCap + (6 * q + clsCap)) 18) ≤
      ENNReal.ofReal (2 ^ 234 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (epsS_le_two_pow hq)
  have hp := progCap_le_sph
  unfold kfCapAt
  grw [he]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 ^ 234 : ℝ)⁻¹ * progCap ≤ (2 ^ 234 : ℝ)⁻¹ * (3 * 2 ^ 40) := by gcongr
    _ ≤ 1 / 2 ^ 192 := by norm_num

set_option exponentiation.threshold 1100 in
/-- `6q + clsCap ≤ 2^91` for `q ≤ 2^88`. -/
theorem clsGradeS_le {q : ℕ} (hq : q ≤ 2 ^ 88) : 6 * q + clsCap ≤ 2 ^ 91 := by
  have hq' : (q : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  have hc := clsCap_le_sph
  have h : ((6 * q + clsCap : ℕ) : ℝ) ≤ 2 ^ 91 := by
    push_cast
    linarith
  exact_mod_cast h

set_option exponentiation.threshold 1100 in
/-- The fresh constant below `2^91` cells: `cwFreshEps G ≤ 2^-320`. -/
theorem cwFreshEps_le_of_91 {G : ℕ} (hG : G ≤ 2 ^ 91) : cwFreshEps G ≤ 1 / 2 ^ 320 := by
  have hG' : (G : ℝ) ≤ 2 ^ 91 := by exact_mod_cast hG
  have h2 : (G : ℝ) * G ≤ 2 ^ 91 * 2 ^ 91 := mul_le_mul hG' hG' (Nat.cast_nonneg G) (by positivity)
  unfold cwFreshEps
  rw [card_Z]
  push_cast
  nlinarith

set_option exponentiation.threshold 1100 in
/-- **The flip-value recorded mass**: `flipCapS q cfEps ≤ 6q 2^-126 + 81 · 2^-68` for
`q ≤ 2^88` (BoundValue's `flipCapS_le`). -/
theorem flipCapS_le_88 {q : ℕ} (hq : q ≤ 2 ^ 88) :
    flipCapS q cfEps ≤ ENNReal.ofReal (6 * q / 2 ^ 126 + 81 / 2 ^ 68) := by
  have hf : ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) ≤ ENNReal.ofReal (1 / 2 ^ 320) :=
    ENNReal.ofReal_le_ofReal (cwFreshEps_le_of_91 (clsGradeS_le hq))
  have hc := clsCap_le_sph
  unfold flipCapS cwRevTau recBadCapS recConv cfEps
  rw [revFirstC_eq, card_Z]
  grw [hf]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [encodingAttemptLimit]
  push_cast
  linarith

end caps

/-! ## The classical costs -/

section cls

set_option exponentiation.threshold 4096 in
/-- **The Enc term of `clsBoundSD`** for `q ≤ 2^88`: at most `(636 · 2^-64)² q + (28 · 2^-94 q)² +
(9 · 2^-34)²` (the `q²` part is the `RecJ` weight times the program-jump factor). -/
theorem encInSD_le {q : ℕ} (hq : q ≤ 2 ^ 88) :
    encECAt (nW progCap + (6 * q + clsCap)) q + 2 * encBeta q * flipCapS q cfEps +
        2 * encGamma q * (kfCapAt (nW progCap + (6 * q + clsCap)) +
          recCapS q (kfCapAt (nW progCap + (6 * q + clsCap)))) ≤
      ENNReal.ofReal ((636 / 2 ^ 64) ^ 2 * q + (28 / 2 ^ 94 * q) ^ 2 + (9 / 2 ^ 34) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hS : ENNReal.ofReal (kapS (6 * q + clsCap) progCap) ≤
      ENNReal.ofReal (5 / 2 ^ 117 * (6 * q + 2 ^ 66)) :=
    ENNReal.ofReal_le_ofReal (kapS_le_linS hq)
  have hR6 : ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) ≤
      ENNReal.ofReal ((6 * q + 2 ^ 66) / 2 ^ 115 + (2 ^ 1000 : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal (kapR6_le_linS hq)
  have hRR : ENNReal.ofReal (kapRRAt (nW progCap + (6 * q + clsCap))) ≤
      ENNReal.ofReal (3 / 2 ^ 208 * (6 * q + 2 ^ 66) + (2 ^ 148 : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal (kapRRAt_le_linS hq)
  have hrS : ENNReal.ofReal (rjS (6 * q + clsCap) progCap) ≤ ENNReal.ofReal (5 / 2 ^ 74) :=
    ENNReal.ofReal_le_ofReal (rjS_le_linS hq)
  have hrR : ENNReal.ofReal (rjR (6 * q + clsCap) progCap) ≤
      ENNReal.ofReal ((6 * q + 2 ^ 66) / 2 ^ 164 + (2 ^ 190 : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal (rjR_le_linS hq)
  have hF := flipCapS_le_88 hq
  have hB := kfCapAt_le hq
  have hN : ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)) ≤
      ENNReal.ofReal (3 * (6 * q + 2 ^ 66)) :=
    ENNReal.ofReal_le_ofReal (by linarith [gradeS_le_lin q])
  have hP : (potCap (6 * q + clsCap) progCap : ℝ≥0∞) ≤ ENNReal.ofReal (6 * q + 2 ^ 66) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (potCap_le_linS q)
  have hc : (clsCap : ℝ≥0∞) ≤ ENNReal.ofReal (40 * 2 ^ 60) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal clsCap_le_sph
  have hn : (rjN progCap : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ 43) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal rjN_le
  have h6p : ((6 * q + progCap : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (6 * q + 3 * 2 ^ 40) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [progCap_le_sph]
  have h6 : ((6 * q : ℕ) : ℝ≥0∞) = ENNReal.ofReal (6 * q) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hZ2 : ENNReal.ofReal (2 / Fintype.card Z) = ENNReal.ofReal (2 / 2 ^ 512) := by
    rw [card_Z, Nat.cast_pow, Nat.cast_ofNat]
  unfold encECAt recCapS encE0 encBeta encGamma encDelta
  rw [h6, hZ2]
  grw [h6p, hS, hR6, hRR, hrS, hrR, hF, hB, hN, hP, hc, hn]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
  ring_nf
  ring_nf at hq2
  linarith

set_option exponentiation.threshold 1100 in
/-- **leanSPHINCS's depth-aware classical caps in closed form**: for `q ≤ 2^88`,
`√clsBoundSD q ≤ (641 √q + 7 · 2^-28 q + 19 · 2^30) / 2^64` (`b₁ = 636 + 4.9` from the Enc
linear term and the first disclosures, `e₁ = 28 · 2^-30` from the `RecJ` term, `c₁` from the Enc
and flip constants `9 · 2^30` each). -/
theorem clsBoundSD_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 88) :
    clsBoundSD q ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((641 * √(q : ℝ) + 7 / 2 ^ 28 * q + 19 * 2 ^ 30) / 2 ^ 64) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hE := rpow_inv_two_le_of_quad hq0 (by positivity) (by positivity) (by positivity)
    (encInSD_le hq)
  have hF := rpow_inv_two_le_ofReal (a := 49 / 20 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34)
    (by positivity) (flipCapS_le_88 hq) (by nlinarith)
  have hP := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 96) (by positivity) (kfCapAt_le hq)
    (by norm_num)
  unfold clsBoundSD clsBoundAt
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add hE hF) hP).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  ring_nf
  linarith

end cls

/-! ## The capacity rates of the depth event bound -/

section capRates

set_option exponentiation.threshold 1100 in
/-- **The adversary's capacity rate**: `capRateBound Z (progCap + 6q + clsCap + 1) 18 ≤
37 (6q + 2^66)³ / 2^512` for every `q`. -/
theorem capRateBound_le_cube (q : ℕ) :
    capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18 ≤
      ENNReal.ofReal (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512) := by
  have h7 : 2 ^ 7 ≤ progCap + (2 * q + 4 * q + clsCap + 1) :=
    two_pow_seven_le_progCap.trans (Nat.le_add_right _ _)
  have hB : ((progCap + (2 * q + 4 * q + clsCap + 1) : ℕ) : ℝ) ≤ 6 * q + 2 ^ 66 := by
    have hc := clsCap_le_sph
    have hp := progCap_le_sph
    push_cast
    linarith
  have hZ : (0 : ℝ) < Fintype.card Z := Nat.cast_pos.mpr Fintype.card_pos
  have key : ∀ N : ℕ, N ≤ capKJ (progCap + (2 * q + 4 * q + clsCap + 1)) 18 +
      capKJ' (progCap + (2 * q + 4 * q + clsCap + 1)) 18 →
      (N : ℝ≥0∞) / Fintype.card Z ≤ ENNReal.ofReal (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512) :=
    fun N hN ↦ by
      rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast (Fintype.card Z),
        ← ENNReal.ofReal_div_of_pos hZ]
      exact ENNReal.ofReal_le_ofReal (capCount_div_le h7 hN hB)
  unfold capRateBound
  exact max_le (key _ (Nat.le_add_right _ _)) (key _ (Nat.le_add_left _ _))

set_option exponentiation.threshold 1100 in
/-- **The verification's capacity rate**: `capRate (progCap + 6q + clsCap + 3 verifyBlocks + 1)
18 ≤ 37 (6q + 2^66)³ / 2^512` for every `q`. -/
theorem capRate_le_cube (q : ℕ) :
    capRate (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18 ≤
      ENNReal.ofReal (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512) := by
  have h7 : 2 ^ 7 ≤ progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) :=
    two_pow_seven_le_progCap.trans (Nat.le_add_right _ _)
  have hB : ((progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) : ℕ) : ℝ) ≤ 6 * q + 2 ^ 66 := by
    have hc := clsCap_le_sph
    have hp := progCap_le_sph
    rw [verifyBlocks_eq]
    push_cast
    linarith
  have hZ : (0 : ℝ) < Fintype.card Z := Nat.cast_pos.mpr Fintype.card_pos
  have key : ∀ N : ℕ, N ≤ capKJ (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18 +
      capKJ' (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18 →
      (N : ℝ≥0∞) / Fintype.card Z ≤ ENNReal.ofReal (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512) :=
    fun N hN ↦ by
      rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast (Fintype.card Z),
        ← ENNReal.ofReal_div_of_pos hZ]
      exact ENNReal.ofReal_le_ofReal (capCount_div_le h7 hN hB)
  unfold capRate
  exact max_le (key _ (Nat.le_add_right _ _)) (key _ (Nat.le_add_left _ _))

set_option exponentiation.threshold 1100 in
/-- `√(12 · 37 (6q + 2^66)³ / 2^512) ≤ (6q + 2^66) 2^-206` for `q ≤ 2^88`. -/
theorem rpow_twelve_cube_le {q : ℕ} (hq : q ≤ 2 ^ 88) {x : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512)) :
    (6 * (2 * x)) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal ((6 * q + 2 ^ 66) / 2 ^ 206) := by
  have hq' : (q : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  have hP0 : (0 : ℝ) ≤ 6 * q + 2 ^ 66 := by positivity
  have h1 : 444 * (6 * (q : ℝ) + 2 ^ 66) ≤ 2 ^ 100 := by linarith
  refine rpow_inv_two_le_ofReal (r := 12 * (37 * (6 * q + 2 ^ 66) ^ 3 / 2 ^ 512)) (by positivity)
    ?_ ?_
  · have e : (6 : ℝ≥0∞) * (2 * x) = ENNReal.ofReal 12 * x := by
      rw [← mul_assoc, ENNReal.ofReal_ofNat]
      norm_num
    rw [e, ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_of_nonneg_left hx zero_le
  · have e1 : 12 * (37 * (6 * (q : ℝ) + 2 ^ 66) ^ 3 / 2 ^ 512) =
        444 * (6 * q + 2 ^ 66) * ((6 * q + 2 ^ 66) ^ 2 / 2 ^ 512) := by ring
    have e2 : ((6 * (q : ℝ) + 2 ^ 66) / 2 ^ 206) ^ 2 =
        2 ^ 100 * ((6 * q + 2 ^ 66) ^ 2 / 2 ^ 512) := by ring
    rw [e1, e2]
    gcongr

/-- **The capacity residual's rate**: `√(6 · 2 capRateBound) ≤ (6q + 2^66) 2^-206` at the
adversary's grade, for `q ≤ 2^88`. -/
theorem rpow_capRateBound_le {q : ℕ} (hq : q ≤ 2 ^ 88) :
    (6 * (2 * capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18)) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((6 * q + 2 ^ 66) / 2 ^ 206) :=
  rpow_twelve_cube_le hq (capRateBound_le_cube q)

end capRates

end Quantum.Sphincs.Assembly

end
