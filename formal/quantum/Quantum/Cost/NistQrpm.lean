module

public import Quantum.Cost.Nist
public import Quantum.Cost.ParallelQrpm

@[expose] public section

/-!
# NIST category 1: leanXMSS in the QRPM against AES-128 key search

Nist's comparison for leanXMSS's depth-aware QRPM closed form
`((20.4 √(q · min d q) + 11 q / 2^28 + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`, valid for
`q ≤ 2^84` permutation calls (`Qrpm.leanXmss_qrpm_gateDepth_closed`). A call of the permutation
is one Keccak-f[1600] query: Nist's clean query circuits (`keccakQueryGatesLowDepth`,
`keccakQueryGatesInPlace`) are Keccak-f circuits, the per-call cost here.

* **The range** `q ≤ 2^84` is a hypothesis (`G / GK ≤ 2^84`): it does not follow from NIST's
  threshold, since `G · MD ≤ 2^157` and `MD ≥ 2^40` give only `G ≤ 2^117`, that is up to
  `2^95.7` (low-depth query) or `2^90.9` (in-place query) calls.
* **The linear term** `11 q / 2^92` is not absorbed into `μ`: from `q ≤ min (G / GK) 2^84`,
  `q ≤ √(G / GK · 2^84)` and `G ≤ 2^117 · G · MD / 2^157`, so the term is at most
  `11 √(2^17 / GK) · √(G · MD / 2^157)` (`linTermQrpm_le`), at most `2.49 √p` (low depth) and
  `0.477 √p` (in place), `p = G · MD / 2^157`.
* `leanXmss_qrpm_nist`: forging is at most
  `(μ √(G · MD / K) + 11 min (G / GK) 2^84 / 2^92 + 75 · 2^30 / 2^64)²`,
  `μ = mu 20.4 (21 · 2^14) K GK DK MD`.
* The factor against `2^157` on all of `MaxDepthRange` (`mu_xmssQrpm_lowDepth_le`,
  `mu_xmssQrpm_inPlace_le`): `μ ≤ 9.384` (low depth), `μ ≤ 1.2894` (in place).
* **Category 1** within `G · MD ≤ 2^157` and at most `2^84` permutation calls: forging succeeds
  with probability at most `141 · G · MD / 2^157 + 2^-23` with the low-depth query
  (`leanXmss_qrpm_cat1_lowDepth`, a loss of `141 = 2^7.14` against AES-128) and at most
  `3.13 · G · MD / 2^157 + 2^-25` with the in-place query (`leanXmss_qrpm_cat1_inPlace`, a loss
  of `3.13 = 2^1.65`): **not** category 1 with either circuit. Against `2^170`:
  `25641 · G · MD / 2^170 + 2^-25` (`leanXmss_qrpm_cat1_inPlace_2016`).
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Cost.Nist

open LeanXmss HashSig

/-! ## The linear term -/

/-- `min x y ≤ √(x y)`. -/
theorem min_le_sqrt_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : min x y ≤ √(x * y) :=
  (Real.sqrt_sq (le_min hx hy)).symm.le.trans (Real.sqrt_le_sqrt (by
    rw [sq]
    exact mul_le_mul (min_le_left x y) (min_le_right x y) (le_min hx hy) hx))

/-- **The QRPM linear term against the AES curve**: with `q ≤ G / GK`, `q ≤ 2^84` and
`MD ≥ 2^40`, `11 q / 2^92 ≤ E √(G · MD / 2^157)` once `121 · 2^17 / GK ≤ E²`. -/
theorem linTermQrpm_le {GK G MD q E : ℝ} (hGK : 0 < GK) (hG : 0 ≤ G) (hMD : 2 ^ 40 ≤ MD)
    (hq0 : 0 ≤ q) (hq : q ≤ G / GK) (hq84 : q ≤ 2 ^ 84) (hE : 121 * 2 ^ 17 / GK ≤ E ^ 2)
    (hE0 : 0 ≤ E) :
    11 * q / 2 ^ 92 ≤ E * √(aesCurve aesK2022 G MD) := by
  have hp : G / 2 ^ 117 ≤ aesCurve aesK2022 G MD := by
    unfold aesCurve aesK2022
    have h := mul_le_mul_of_nonneg_left hMD hG
    calc G / 2 ^ 117 = G * 2 ^ 40 / 2 ^ 157 := by ring
      _ ≤ G * MD / 2 ^ 157 := div_le_div_of_nonneg_right h (by positivity)
  have hqq : q * q ≤ G / GK * 2 ^ 84 := mul_le_mul hq hq84 hq0 (by positivity)
  have h2 : 121 / 2 ^ 184 * (G / GK * 2 ^ 84) = 121 * 2 ^ 17 / GK * (G / 2 ^ 117) := by
    field_simp
  have hsq : (11 * q / 2 ^ 92) ^ 2 ≤ E ^ 2 * aesCurve aesK2022 G MD := by
    calc (11 * q / 2 ^ 92) ^ 2 = 121 / 2 ^ 184 * (q * q) := by ring
      _ ≤ 121 / 2 ^ 184 * (G / GK * 2 ^ 84) := mul_le_mul_of_nonneg_left hqq (by positivity)
      _ = 121 * 2 ^ 17 / GK * (G / 2 ^ 117) := h2
      _ ≤ E ^ 2 * (G / 2 ^ 117) := mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ E ^ 2 * aesCurve aesK2022 G MD := mul_le_mul_of_nonneg_left hp (sq_nonneg E)
  calc 11 * q / 2 ^ 92 = √((11 * q / 2 ^ 92) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √(E ^ 2 * aesCurve aesK2022 G MD) := Real.sqrt_le_sqrt hsq
    _ = E * √(aesCurve aesK2022 G MD) := by
        rw [Real.sqrt_mul (sq_nonneg E), Real.sqrt_sq hE0]

/-- **Below the threshold, a multiple of the AES curve, with a `√p` term**: for `0 ≤ p ≤ 1`,
`μ ≤ M` and `t ≤ E √p`, `(μ √p + t + y)² ≤ m p + r` once `(M + E)² ≤ m` and
`2 (M + E) y + y² ≤ r`. -/
theorem sq_le_lin_of_le_one_sqrt {μ M E y m r p t : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ M) (hE : 0 ≤ E)
    (hy : 0 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : (M + E) ^ 2 ≤ m)
    (hr : 2 * (M + E) * y + y ^ 2 ≤ r) (ht0 : 0 ≤ t) (ht : t ≤ E * √p) :
    (μ * √p + t + y) ^ 2 ≤ m * p + r := by
  have hs0 := Real.sqrt_nonneg p
  have hs1 : √p ≤ 1 := (Real.sqrt_le_sqrt hp1).trans_eq Real.sqrt_one
  have hsq := Real.sq_sqrt hp0
  have hME : 0 ≤ M + E := by linarith
  have h1 : μ * √p ≤ M * √p := mul_le_mul_of_nonneg_right hμ hs0
  have hb : μ * √p + t + y ≤ (M + E) * √p + y := by linarith
  calc (μ * √p + t + y) ^ 2 ≤ ((M + E) * √p + y) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    _ = (M + E) ^ 2 * √p ^ 2 + 2 * (M + E) * y * √p + y ^ 2 := by ring
    _ ≤ m * p + r := by
        rw [hsq]
        have h3 : 2 * (M + E) * y * √p ≤ 2 * (M + E) * y :=
          mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) hME) hy) hs1
        have h4 : (M + E) ^ 2 * p ≤ m * p := mul_le_mul_of_nonneg_right hm hp0
        linarith

/-! ## The factors -/

set_option exponentiation.threshold 200 in
/-- **The leanXMSS QRPM factor at the low-depth Keccak-f query** against `2^157`: `μ ≤ 9.384`
on `MaxDepthRange`. -/
theorem mu_xmssQrpm_lowDepth_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu (102 / 5) (21 * 2 ^ 14) aesK2022 keccakQueryGatesLowDepth keccakQueryDepthLowDepth MD ≤
      9.384 := by
  have h1 : √(aesK2022 / ((keccakQueryGatesLowDepth : ℝ) * keccakQueryDepthLowDepth * 2 ^ 128))
      ≤ 0.22741 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    rw [keccakQueryGatesLowDepth_eq, keccakQueryDepthLowDepth_eq, aesK2022]
    norm_num
  have h2 : √(aesK2022 / ((keccakQueryGatesLowDepth : ℝ) * 2 ^ 128 * MD)) ≤ 1.3788e-5 := by
    refine sqrt_le_of_le_sq (by norm_num) ((div_le_div_maxDepth (by norm_num [aesK2022])
      (by norm_num [keccakQueryGatesLowDepth_eq]) hMD.1).trans ?_)
    rw [keccakQueryGatesLowDepth_eq, aesK2022]
    norm_num
  unfold mu
  nlinarith

set_option exponentiation.threshold 200 in
/-- **The leanXMSS QRPM factor at the in-place Keccak-f query** against `2^157`:
`μ ≤ 1.2894` on `MaxDepthRange`. -/
theorem mu_xmssQrpm_inPlace_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu (102 / 5) (21 * 2 ^ 14) aesK2022 keccakQueryGatesInPlace keccakQueryDepthInPlace MD ≤
      1.2894 := by
  have h1 : √(aesK2022 / ((keccakQueryGatesInPlace : ℝ) * keccakQueryDepthInPlace * 2 ^ 128))
      ≤ 0.018643 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    rw [keccakQueryGatesInPlace_eq, keccakQueryDepthInPlace_eq, aesK2022]
    norm_num
  have h2 : √(aesK2022 / ((keccakQueryGatesInPlace : ℝ) * 2 ^ 128 * MD)) ≤ 2.6421e-6 := by
    refine sqrt_le_of_le_sq (by norm_num) ((div_le_div_maxDepth (by norm_num [aesK2022])
      (by norm_num [keccakQueryGatesInPlace_eq]) hMD.1).trans ?_)
    rw [keccakQueryGatesInPlace_eq, aesK2022]
    norm_num
  unfold mu
  nlinarith

/-! ## leanXMSS in the QRPM against AES-128 -/

/-- **leanXMSS in the QRPM against AES-128**, for any per-call cost of `GK` gates and depth `DK`
per Keccak-f query: an adversary within `G` gates, depth charge `MD > 0` and at most `2^84`
permutation calls (`G / GK ≤ 2^84`) forges with probability at most
`(μ √(G · MD / K) + 11 min (G / GK) 2^84 / 2^92 + 75 · 2^30 / 2^64)²`,
`μ = mu 20.4 (21 · 2^14) K GK DK MD`. -/
theorem leanXmss_qrpm_nist {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) (Γ : GateSet)
    (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : Qrpm.XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (Qrpm.permGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (Qrpm.permDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)
    (hq : G / GK ≤ 2 ^ 84) (hMD : 0 < MD) {K : ℝ} (hK : 0 < K) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal ((mu (102 / 5) (21 * 2 ^ 14) K GK DK MD * √(aesCurve K G MD) +
        11 * min ((G : ℝ) / GK) (2 ^ 84) / 2 ^ 92 + 75 * 2 ^ 30 / 2 ^ 64) ^ 2) := by
  refine (Qrpm.leanXmss_qrpm_gateDepth_closed hGK hDK Γ δ G MD A hG hD hS hq).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Nat.cast_min]
  have hq0 : (0 : ℝ) ≤ ((G / GK : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqG : ((G / GK : ℕ) : ℝ) ≤ (G : ℝ) / GK := Nat.cast_div_le
  have hq84 : ((G / GK : ℕ) : ℝ) ≤ 2 ^ 84 := by exact_mod_cast hq
  have hmin : ((G / GK : ℕ) : ℝ) ≤ min ((G : ℝ) / GK) (2 ^ 84) := le_min hqG hq84
  have hμ := mu_nonneg (a := 102 / 5) (b := 21 * 2 ^ 14) (K := K) (GK := GK) (DK := DK)
    (MD := MD) (by norm_num) (by norm_num)
  have h := parBound_le_aesCurve (a := 102 / 5) (e := 0) (b := 21 * 2 ^ 14) (c := 75 * 2 ^ 30)
    (by norm_num) le_rfl (by norm_num) (by norm_num) hK (by exact_mod_cast hGK)
    (by exact_mod_cast hDK) (by exact_mod_cast hMD) hq0 (Nat.cast_nonneg (MD / DK)) hqG
    Nat.cast_div_le
  simp only [zero_mul, zero_div, add_zero] at h
  have hL := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have ht : 11 * ((G / GK : ℕ) : ℝ) / 2 ^ 92 ≤ 11 * min ((G : ℝ) / GK) (2 ^ 84) / 2 ^ 92 := by
    gcongr
  have e1 : (102 / 5 * √(((G / GK : ℕ) : ℝ) * min ((MD / DK : ℕ) : ℝ) ((G / GK : ℕ) : ℝ)) +
      11 * ((G / GK : ℕ) : ℝ) / 2 ^ 28 + 21 * 2 ^ 14 * √((G / GK : ℕ) : ℝ) + 75 * 2 ^ 30) /
        2 ^ 64 =
      (102 / 5 * √(((G / GK : ℕ) : ℝ) * min ((MD / DK : ℕ) : ℝ) ((G / GK : ℕ) : ℝ)) +
        21 * 2 ^ 14 * √((G / GK : ℕ) : ℝ) + 75 * 2 ^ 30) / 2 ^ 64 +
        11 * ((G / GK : ℕ) : ℝ) / 2 ^ 92 := by
    ring
  rw [e1]
  linarith

/-- The linear term `11 min (G / GK) 2^84 / 2^92` is nonnegative. -/
theorem minTerm_nonneg (G GK : ℝ) (hG : 0 ≤ G) (hGK : 0 ≤ GK) :
    0 ≤ 11 * min (G / GK) (2 ^ 84) / 2 ^ 92 := by
  have : 0 ≤ min (G / GK) (2 ^ 84) := le_min (div_nonneg hG hGK) (by positivity)
  positivity

set_option exponentiation.threshold 200 in
/-- **Category 1 at the low-depth Keccak-f query** (Song, Jang, Seo 2023): within NIST's 2022
threshold, `G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange` and at most `2^84` permutation
calls, forging succeeds with probability at most `141 · G · MD / 2^157 + 2^-23`. This is **not**
category 1: against the AES-128 success `G · MD / 2^157` it loses the factor `141 = 2^7.14`
(`μ ≤ 9.384`, linear term `2.49 √p`). -/
theorem leanXmss_qrpm_cat1_lowDepth (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesLowDepth)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthLowDepth)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)
    (hq : G / keccakQueryGatesLowDepth ≤ 2 ^ 84)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (141 * aesCurve aesK2022 G MD + (2 ^ 23)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  have hGK : (0 : ℝ) < keccakQueryGatesLowDepth := by norm_num [keccakQueryGatesLowDepth_eq]
  refine (leanXmss_qrpm_nist (by norm_num [cleanQueryGates, keccakfGatesLowDepth])
    (by norm_num [cleanQueryDepth, keccakfDepthLowDepth])
    Γ δ G MD A hG hD hS hq (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one_sqrt (mu_nonneg (by norm_num) (by norm_num))
    (mu_xmssQrpm_lowDepth_le hMD) (E := 2.49) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (minTerm_nonneg _ _ (Nat.cast_nonneg G) hGK.le) ?_
  refine linTermQrpm_le hGK (Nat.cast_nonneg G) hMD.1
    (le_min (div_nonneg (Nat.cast_nonneg G) hGK.le) (by positivity)) (min_le_left _ _)
    (min_le_right _ _) ?_ (by norm_num)
  rw [keccakQueryGatesLowDepth_eq]
  norm_num

set_option exponentiation.threshold 200 in
/-- **Category 1 at the in-place Keccak-f query** (Amy et al. 2016): within NIST's 2022
threshold, `G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange` and at most `2^84` permutation
calls, forging succeeds with probability at most `3.13 · G · MD / 2^157 + 2^-25`. This is
**not** category 1: it loses the factor `3.13 = 2^1.65` against AES-128 (`μ ≤ 1.2894`, linear
term `0.477 √p`). -/
theorem leanXmss_qrpm_cat1_inPlace (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)
    (hq : G / keccakQueryGatesInPlace ≤ 2 ^ 84)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (3.13 * aesCurve aesK2022 G MD + (2 ^ 25)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  have hGK : (0 : ℝ) < keccakQueryGatesInPlace := by norm_num [keccakQueryGatesInPlace_eq]
  refine (leanXmss_qrpm_nist (by norm_num [cleanQueryGates, keccakfGatesInPlace])
    (by norm_num [cleanQueryDepth, keccakfDepthInPlace])
    Γ δ G MD A hG hD hS hq (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one_sqrt (mu_nonneg (by norm_num) (by norm_num))
    (mu_xmssQrpm_inPlace_le hMD) (E := 0.477) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (minTerm_nonneg _ _ (Nat.cast_nonneg G) hGK.le) ?_
  refine linTermQrpm_le hGK (Nat.cast_nonneg G) hMD.1
    (le_min (div_nonneg (Nat.cast_nonneg G) hGK.le) (by positivity)) (min_le_left _ _)
    (min_le_right _ _) ?_ (by norm_num)
  rw [keccakQueryGatesInPlace_eq]
  norm_num

/-- **Against NIST's 2016 threshold** (`2^170 / MAXDEPTH`), the in-place query gives
`25641 · G · MD / 2^170 + 2^-25` within `G · MD ≤ 2^157` and at most `2^84` permutation
calls. -/
theorem leanXmss_qrpm_cat1_inPlace_2016 (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)
    (hq : G / keccakQueryGatesInPlace ≤ 2 ^ 84)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (25641 * aesCurve aesK2016 G MD + (2 ^ 25)⁻¹) := by
  refine (leanXmss_qrpm_cat1_inPlace Γ δ G MD A hG hD hS hq hMD hGM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ aesCurve aesK2016 G MD := by
    unfold aesCurve aesK2016
    positivity
  rw [aesCurve_aesK2022]
  nlinarith

end Quantum.Cost.Nist

end
