module

public import Quantum.Sphincs.Assembly.Security
public import Quantum.Xmss.Assembly.BoundValue

@[expose] public section

/-!
# The size of the leanSPHINCS QRPM bound

Security's `sphincsQrpmBound q` in closed form for `q ≤ 2^64` (`sphincsQrpmBound_le`):
`sphincsQrpmBound q ≤ ((4611 q + 2^11 √q + 2^36) / 2^64)²`, about `2^-56.9` for small `q` and
`q² 2^-103.7` for large `q`. Each term is bounded by a real number separately:

* the adversary terms `advA q ≤ (15 q + 5418) 2^-64` (`advA_le`) and `√(advB q² covPS) ≤
  (4566 q + 2^20) 2^-64` (`advBcov_le`, the coverage price `2^16 rhoCov 2^-128`);
* the flip-value recorded mass `flipCapS q cfEps ≤ 6 q 2^-126 + 81 · 2^-68` (`flipCapS_le`), the Enc
  term at most `q 2^-109 + 84 · 2^-68` (`encInS_le`, from `encEC_le_sph`, `encBeta_le_sph`,
  `encGamma_le_sph`), hence `√(clsBoundS q cfEps + verLinS + 3 verifyBlocks covPS) ≤ √q 2^-54 +
  10 · 2^-34 + 3 √q 2^-63 + 9 · 2^-34 + 2^-49` (`clsVerS_rpow_le`);
* the verification's read error, the trial-hit mass, the conflict cap, `2 goodESCap`, `2^-777`,
  `winChgCap` and `stageCap` at most `2 · 2^-64` (`restSph_le`); the hybrid `hybTermS q kappaSph
  readCapS ≤ 30 q 2^-64 + 30 · 2^-34` (`hybTermSph_le`, `kappaSph ≤ 6.25 · 2^-128`,
  `readCapS ≤ 900 · 2^-68`) and `stageCap ≤ 2^-126` (`stageCap_le`).

At `q ≤ 2^30` the bound is at most `2^-43` (`sphincsQrpmBound_two_pow_30_le`), at `q ≤ 2^40` at most
`2^-23` (`sphincsQrpmBound_two_pow_40_le`).
-/

open scoped ENNReal

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (rpow_inv_two_le_ofReal sq_add_rpow_inv_two_le cwFreshEps_le_of kapRR_le
  pow_two_rpow_inv_two two_div_natCast_le card_Z cwFreshEps kapRR keepCost inv_two_pow_eq_ofReal)

namespace Quantum.Sphincs.Assembly

/-! ## Helpers -/

section helpers

theorem clsCap_le_sph : (clsCap : ℝ) ≤ 40 * 2 ^ 60 := by
  have h : clsCap ≤ 40 * 2 ^ 60 := by
    rw [clsCap_eq]
    norm_num [signatureLimit]
  exact_mod_cast h

theorem progCap_le_sph : (progCap : ℝ) ≤ 3 * 2 ^ 40 := by
  have h : progCap ≤ 3 * 2 ^ 40 := by
    rw [progCap_eq]
    norm_num [signatureLimit]
  exact_mod_cast h

theorem potCap_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    (potCap (6 * q + clsCap) progCap : ℝ) ≤ 2 ^ 68 + 2 := by
  have h : potCap (6 * q + clsCap) progCap ≤ 2 ^ 68 + 2 := by
    have := progCap_add_le hq
    unfold potCap nW
    omega
  exact_mod_cast h

theorem nWD_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ) ≤ 2 ^ 68 + 1 := by
  have h : nW progCap + (6 * q + clsCap) ≤ 2 ^ 68 + 1 := by
    have := progCap_add_le hq
    unfold nW
    omega
  exact_mod_cast h

set_option exponentiation.threshold 1100 in
/-- `kkEps ≤ 2^-250`. -/
theorem kkEps_le : kkEps ≤ ENNReal.ofReal (1 / 2 ^ 250) := by
  unfold kkEps
  rw [Quantum.Xmss.Hybrid.card_masterSeed, card_Z]
  grw [Quantum.Sphincs.Hybrid.seedEps_le_keccak]
  simp (disch := positivity) only [Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_div_of_pos,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- `stageCap ≤ 2^-126`. -/
theorem stageCap_le : stageCap ≤ ENNReal.ofReal (1 / 2 ^ 126) := by
  unfold stageCap
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end helpers

/-! ## The adversary terms -/

section adv

set_option exponentiation.threshold 1100 in
/-- **The price-free adversary term**: `advA q ≤ (15 q + 5418) 2^-64`. -/
theorem advA_le (q : ℕ) : advA q ≤ ENNReal.ofReal (15 * q / 2 ^ 64 + 5418 / 2 ^ 64) := by
  have h6 : (6 * freshK) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (5 / 2 ^ 65) := by
    refine rpow_inv_two_le_ofReal (r := 25 / 2 ^ 130) (by positivity) ?_ (by norm_num)
    unfold freshK
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : freshK ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2 / 2 ^ 64) := by
    refine rpow_inv_two_le_ofReal (r := 4 / 2 ^ 128) (by positivity) ?_ (by norm_num)
    unfold freshK
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  unfold advA
  rw [verifyBlocks_eq]
  grw [h6, h1]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The coverage term**: `√(advB q² covPS) ≤ (4566 q + 2^20) 2^-64`
(`√covPS ≤ 310.66 · 2^-64`). -/
theorem advBcov_le (q : ℕ) :
    (advB q ^ 2 * covPS) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (4566 * q / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) := by
  have h6 : (6 : ℝ≥0∞) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (24495 / 10000) :=
    rpow_inv_two_le_ofReal (r := 6) (by norm_num) (by rw [ENNReal.ofReal_ofNat]) (by norm_num)
  have hc : covPS ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (31066 / 100 / 2 ^ 64) := by
    refine rpow_inv_two_le_ofReal (r := 96509 / 2 ^ 128) (by positivity) ?_ (by norm_num)
    unfold covPS
    simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
      ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num [rhoCov])
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), pow_two_rpow_inv_two]
  unfold advB
  rw [verifyBlocks_eq]
  grw [h6, hc]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  linarith

end adv

/-! ## The prefix's classical costs -/

section enc

set_option exponentiation.threshold 4096 in
/-- `kapS ≤ 2^-78` at the prefix's sizes, for `q ≤ 2^64`. -/
theorem kapS_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    kapS (6 * q + clsCap) progCap ≤ (2 ^ 78 : ℝ)⁻¹ := by
  have he := epsQ_prefix_le hq
  have he0 := epsQ_nonneg (6 * q + clsCap) progCap
  have h6 : 6 * epsQ (6 * q + clsCap) progCap ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by
    calc 6 * epsQ (6 * q + clsCap) progCap ≤ 6 * (2 ^ 302 : ℝ)⁻¹ := by gcongr
      _ ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by norm_num
  have hs : √(6 * epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 149 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt h6).trans_eq (Real.sqrt_sq (by positivity))
  unfold kapS
  calc (potCap (6 * q + clsCap) progCap : ℝ) * (2 * √(6 * epsQ (6 * q + clsCap) progCap) +
        6 * epsQ (6 * q + clsCap) progCap)
      ≤ (2 ^ 68 + 2) * (2 * (2 ^ 149 : ℝ)⁻¹ + ((2 ^ 149 : ℝ)⁻¹) ^ 2) := by
        gcongr
        exact potCap_le_sph hq
    _ ≤ (2 ^ 78 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- `kapR6 ≤ 2^-79` at the prefix's sizes, for `q ≤ 2^64`. -/
theorem kapR6_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    kapR6 (6 * q + clsCap) progCap ≤ (2 ^ 79 : ℝ)⁻¹ := by
  have he := epsQ_prefix_le hq
  have he0 := epsQ_nonneg (6 * q + clsCap) progCap
  have he' : epsQ (6 * q + clsCap) progCap ≤ ((2 ^ 151 : ℝ)⁻¹) ^ 2 := he.trans_eq (by norm_num)
  have hs : √(epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 151 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt he').trans_eq (Real.sqrt_sq (by positivity))
  have hX : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [Quantum.Xmss.card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hZ : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_Z]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hX6 : (6 : ℝ) / Fintype.card X ≤ (2 ^ 1000 : ℝ)⁻¹ := by
    rw [Quantum.Xmss.card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold kapR6
  calc (potCap (6 * q + clsCap) progCap : ℝ) * (epsQ (6 * q + clsCap) progCap +
        (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ (6 * q + clsCap) progCap)) +
        6 / (Fintype.card X : ℝ)
      ≤ (2 ^ 68 + 2) * ((2 ^ 302 : ℝ)⁻¹ + ((2 ^ 511 : ℝ)⁻¹ + (2 ^ 511 : ℝ)⁻¹) +
          2 * (2 ^ 151 : ℝ)⁻¹) + (2 ^ 1000 : ℝ)⁻¹ := by
        gcongr
        exact potCap_le_sph hq
    _ ≤ (2 ^ 79 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 1100 in
/-- **The refined Enc constant**: `encE0 q ≤ 6 q 2^-113 + 41 · 2^-68` for `q ≤ 2^64`. -/
theorem encE0_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encE0 q ≤ ENNReal.ofReal (6 * q / 2 ^ 113 + 41 / 2 ^ 68) := by
  have hS : ENNReal.ofReal (kapS (6 * q + clsCap) progCap) ≤ ENNReal.ofReal (2 ^ 78 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (kapS_le_sph hq)
  have hR : ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) ≤ ENNReal.ofReal (2 ^ 79 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal (kapR6_le_sph hq)
  have hc := clsCap_le_sph
  have hp := progCap_le_sph
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  unfold encE0
  grw [hS, hR]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The prefix's linear charge constant**: `encEC q ≤ 12 q 2^-113 + 83 · 2^-68` for
`q ≤ 2^64`. -/
theorem encEC_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encEC q ≤ ENNReal.ofReal (12 * q / 2 ^ 113 + 83 / 2 ^ 68) := by
  have hR : ENNReal.ofReal kapRR ≤ ENNReal.ofReal (2 ^ 148 : ℝ)⁻¹ :=
    ENNReal.ofReal_le_ofReal kapRR_le
  have hc := clsCap_le_sph
  unfold encEC encDelta
  rw [card_Z]
  grw [encE0_le_sph hq, hR]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- `encBeta q ≤ 2^-43` for `q ≤ 2^64`. -/
theorem encBeta_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) : encBeta q ≤ ENNReal.ofReal (1 / 2 ^ 43) := by
  have hN := nWD_le_sph hq
  unfold encBeta
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- `encGamma q ≤ 2^-44` for `q ≤ 2^64`. -/
theorem encGamma_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) : encGamma q ≤ ENNReal.ofReal (1 / 2 ^ 44) := by
  have hP := potCap_le_sph hq
  unfold encGamma
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- **The flip-value recorded mass**: `flipCapS q cfEps ≤ 6 q 2^-126 + 81 · 2^-68` for
`q ≤ 2^64` (the first disclosures `6 q 2^-126`, the conversion `recConv ≤ 80 · 2^-68`). -/
theorem flipCapS_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    flipCapS q cfEps ≤ ENNReal.ofReal (6 * q / 2 ^ 126 + 81 / 2 ^ 68) := by
  have hf : ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) ≤ ENNReal.ofReal (1 / 2 ^ 370) :=
    ENNReal.ofReal_le_ofReal (cwFreshEps_le_of (le_add_self.trans (progCap_add_le hq)))
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

set_option exponentiation.threshold 1100 in
/-- The averaged fresh `k`, `k'` flips: `kfCapS ≤ 2^-259`. -/
theorem kfCapS_le : kfCapS ≤ ENNReal.ofReal (1 / 2 ^ 259) := by
  have hp := progCap_le_sph
  unfold kfCapS
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- **The Enc term of `clsBoundS`**: at most `q 2^-109 + 84 · 2^-68` for `q ≤ 2^64`. -/
theorem encInS_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    encEC q + 2 * encBeta q * flipCapS q cfEps + 2 * encGamma q * (kfCapS + recCapS q kfCapS) ≤
      ENNReal.ofReal (q / 2 ^ 109 + 84 / 2 ^ 68) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  grw [recCapS_le hq kfCapS, encEC_le_sph hq, encBeta_le_sph hq, flipCapS_le hq,
    encGamma_le_sph hq, kfCapS_le]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

set_option exponentiation.threshold 1100 in
/-- The price-free verification term and the verification's coverage part: at most `2^-100`. -/
theorem verS_le :
    verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS ≤ ENNReal.ofReal (1 / 2 ^ 100) := by
  have hX : (2 : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [Quantum.Xmss.card_X]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hZ : (2 : ℝ≥0∞) / (Fintype.card Z : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_Z]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hr : ((rhoCov : ℚ) : ℝ) = 7363 / 5000 := by norm_num [rhoCov]
  unfold verLinS keepCost covPS freshK
  rw [verifyBlocks_eq, hr]
  grw [hX, hZ]
  simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num

set_option exponentiation.threshold 1100 in
/-- **The prefix's classical costs and the verification's linear term, square-rooted**:
`≤ √q 2^-54 + 10 · 2^-34 + 3 √q 2^-63 + 9 · 2^-34 + 2^-49` for `q ≤ 2^64`. -/
theorem clsVerS_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    (clsBoundS q cfEps + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (√(q : ℝ) / 2 ^ 54 + 10 / 2 ^ 34 + (3 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34) +
        1 / 2 ^ 49) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hE := rpow_inv_two_le_ofReal (a := √(q : ℝ) / 2 ^ 54 + 10 / 2 ^ 34) (by positivity)
    (encInS_le hq) (by nlinarith)
  have hF := rpow_inv_two_le_ofReal (a := 3 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34) (by positivity)
    (flipCapS_le hq) (by nlinarith)
  have hR : kfCapS + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS) ≤
      ENNReal.ofReal (1 / 2 ^ 99) := by
    grw [kfCapS_le, verS_le]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hP := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 49) (by positivity) hR (by norm_num)
  unfold clsBoundS
  rw [add_assoc]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add hE hF) hP).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end enc

/-! ## The event term, the hybrid and the closed form -/

section closed

set_option exponentiation.threshold 1100 in
/-- **The rest of the event term**: the verification's read error, the trial-hit mass, the conflict
cap, `2 goodESCap`, `2^-777`, `winChgCap` and `stageCap`, at most `2 · 2^-64`. -/
theorem restSph_le :
    ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
        ENNReal.ofReal (1 / 2 ^ 189) + ENNReal.ofReal (hConflictCap signatureLimit) +
        2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) + winChgCap + stageCap ≤
      ENNReal.ofReal (2 / 2 ^ 64) := by
  have hh : ENNReal.ofReal (hConflictCap signatureLimit) ≤ ENNReal.ofReal (1 / 2 ^ 64) :=
    ENNReal.ofReal_le_ofReal hConflictCap_le
  grw [hh, goodESCap_le, stageCap_le]
  unfold readError winChgCap
  rw [Quantum.Xmss.card_X, card_Z, verifyBlocks_eq]
  simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- **The square-rooted event term**: `√eventTermSph q ≤ (15 q + 5418) 2^-64 + (4566 q + 2^20)
2^-64 + (√q 2^-54 + 10 · 2^-34 + 3 √q 2^-63 + 9 · 2^-34 + 2^-49) + 3 · 2^-33` for `q ≤ 2^64`. -/
theorem eventTermSph_rpow_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    eventTermSph q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (15 * q / 2 ^ 64 + 5418 / 2 ^ 64 +
      (4566 * q / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) + (√(q : ℝ) / 2 ^ 54 + 10 / 2 ^ 34 +
        (3 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34) + 1 / 2 ^ 49) + 3 / 2 ^ 33) := by
  have hs := rpow_inv_two_le_ofReal (a := 3 / 2 ^ 33) (by positivity) restSph_le (by norm_num)
  have e : eventTermSph q = (advA q + (advB q ^ 2 * covPS) ^ (2⁻¹ : ℝ) +
      (clsBoundS q cfEps + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 +
      (ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
        ENNReal.ofReal (1 / 2 ^ 189) + ENNReal.ofReal (hConflictCap signatureLimit) +
        2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) + winChgCap + stageCap) := by
    unfold eventTermSph eventTermS
    simp only [add_assoc]
  rw [e]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add (add_le_add (advA_le q)
    (advBcov_le q)) (clsVerS_rpow_le hq)) hs).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

set_option exponentiation.threshold 1100 in
/-- The masked hidden mass per sponge call: `kappaSph ≤ 6.25 · 2^-128`. -/
theorem kappaSph_le : kappaSph ≤ ENNReal.ofReal (25 / 4 / 2 ^ 128) := by
  unfold kappaSph kappaH chgRevCap
  rw [card_randomizer]
  grw [kkEps_le]
  simp (disch := positivity) only [Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_add]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 1100 in
/-- The masked hidden mass at the read ports: `readCapS ≤ 900 · 2^-68` (`21 clsCap 2^-128`). -/
theorem readCapS_le : readCapS ≤ ENNReal.ofReal (900 / 2 ^ 68) := by
  have hc := clsCap_le_sph
  unfold readCapS trialTau kappaH chgRevCap
  rw [card_randomizer, verifyBlocks_eq]
  grw [kkEps_le]
  simp (disch := positivity) only [Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

set_option exponentiation.threshold 1100 in
/-- **The hybrid term**: `hybTermS q kappaSph readCapS ≤ 30 q 2^-64 + 30 · 2^-34`
(`4 · 6q · 6q κ ≤ 900 q² 2^-128`). -/
theorem hybTermSph_le (q : ℕ) :
    hybTermS q kappaSph readCapS ≤ ENNReal.ofReal (30 * q / 2 ^ 64 + 30 / 2 ^ 34) := by
  have hq2 := sq_nonneg (q : ℝ)
  have hs : 4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaSph)) ≤
      ENNReal.ofReal (900 * (q : ℝ) ^ 2 / 2 ^ 128) := by
    grw [kappaSph_le]
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith
  unfold hybTermS
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (rpow_inv_two_le_ofReal (by positivity) hs (by nlinarith))
    (rpow_inv_two_le_ofReal (by positivity) readCapS_le (by norm_num))

/-- The arithmetic of the closed form: the sum of the term bounds is at most
`(4611 q + 2^11 √q + 2^36) / 2^64 - 2^-34`, which absorbs `stageCap`. -/
theorem root_sq_le_sph (q : ℕ) :
    (15 * q / 2 ^ 64 + 5418 / 2 ^ 64 + (4566 * q / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
      (√(q : ℝ) / 2 ^ 54 + 10 / 2 ^ 34 + (3 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34) + 1 / 2 ^ 49) +
      3 / 2 ^ 33 + (30 * q / 2 ^ 64 + 30 / 2 ^ 34)) ^ 2 + 1 / 2 ^ 126 ≤
      ((4611 * q + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64) ^ 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  set F := (4611 * (q : ℝ) + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64 with hF
  have h1 : 15 * (q : ℝ) / 2 ^ 64 + 5418 / 2 ^ 64 + (4566 * q / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
      (√(q : ℝ) / 2 ^ 54 + 10 / 2 ^ 34 + (3 * √(q : ℝ) / 2 ^ 63 + 9 / 2 ^ 34) + 1 / 2 ^ 49) +
      3 / 2 ^ 33 + (30 * q / 2 ^ 64 + 30 / 2 ^ 34) ≤ F - 1 / 2 ^ 34 := by
    rw [hF]
    linarith
  have h2 : 64 / 2 ^ 34 ≤ F := by
    rw [hF]
    linarith
  calc _ ≤ (F - 1 / 2 ^ 34) ^ 2 + 1 / 2 ^ 126 := by gcongr
    _ ≤ F ^ 2 := by nlinarith

/-- **The leanSPHINCS QRPM bound in closed form**: for `q ≤ 2^64`,
`sphincsQrpmBound q ≤ ((4611 q + 2^11 √q + 2^36) / 2^64)²`. -/
theorem sphincsQrpmBound_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    sphincsQrpmBound q ≤
      ENNReal.ofReal (((4611 * q + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermSph_rpow_le hq
  have h2 := hybTermSph_le q
  have h3 := stageCap_le
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (root_sq_le_sph q))
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold sphincsQrpmBound
  gcongr

set_option exponentiation.threshold 1100 in
/-- **At most `2^30` permutation calls**: `sphincsQrpmBound q ≤ 2^-43`. -/
theorem sphincsQrpmBound_two_pow_30_le {q : ℕ} (hq : q ≤ 2 ^ 30) :
    sphincsQrpmBound q ≤ (2 ^ 43 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 15 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 30 = (2 ^ 15) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (sphincsQrpmBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4611 * q + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64) ^ 2
      ≤ ((4611 * 2 ^ 30 + 2 ^ 11 * 2 ^ 15 + 2 ^ 36) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 43 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^40` permutation calls**: `sphincsQrpmBound q ≤ 2^-23`. -/
theorem sphincsQrpmBound_two_pow_40_le {q : ℕ} (hq : q ≤ 2 ^ 40) :
    sphincsQrpmBound q ≤ (2 ^ 23 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hq
  have hs : √(q : ℝ) ≤ 2 ^ 20 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 40 = (2 ^ 20) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  refine (sphincsQrpmBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4611 * q + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64) ^ 2
      ≤ ((4611 * 2 ^ 40 + 2 ^ 11 * 2 ^ 20 + 2 ^ 36) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 23 := by norm_num

end closed

end Quantum.Sphincs.Assembly

end
