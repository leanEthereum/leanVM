module

public import Quantum.Cost.NistQrpm
public import Quantum.Cost.ParallelQrpmSphincs

@[expose] public section

/-!
# NIST category 1: leanSPHINCS in the QRPM against AES-128 key search

Nist's comparison for leanSPHINCS's depth-aware QRPM closed form
`((1566 √(q · min d q) + q / 2^25 + 641 √q + 57 · 2^30) / 2^64)²`, valid for `q ≤ 2^88`
permutation calls (`Qrpm.leanSphincs_qrpm_gateDepth_closed`); a permutation call is one
Keccak-f[1600] query, at Nist's clean query circuits.

* **The range** `q ≤ 2^88` is a hypothesis (`G / GK ≤ 2^88`): NIST's threshold
  `G · MD ≤ 2^157` with `MD ≥ 2^40` gives only `G ≤ 2^117`, up to `2^95.7` (low-depth query) or
  `2^90.9` (in-place query) calls.
* **The linear term** `q / 2^89`: from `q ≤ min (G / GK) 2^88 ≤ √(G / GK · 2^88)` and
  `G ≤ 2^117 · G · MD / 2^157`, at most `√(2^27 / GK) · √p` (`linTermQrpmS_le`), at most
  `7.229 √p` (low depth) and `1.3852 √p` (in place), `p = G · MD / 2^157`.
* `leanSphincs_qrpm_nist`: forging is at most
  `(μ √(G · MD / K) + min (G / GK) 2^88 / 2^89 + 57 · 2^30 / 2^64)²`,
  `μ = mu 1566 641 K GK DK MD`.
* The factor against `2^157` on all of `MaxDepthRange` (`mu_sphincsQrpm_lowDepth_le`,
  `mu_sphincsQrpm_inPlace_le`): `μ ≤ 356.14` (low depth), `μ ≤ 29.197` (in place).
* **Category 1** within `G · MD ≤ 2^157` and at most `2^88` permutation calls: forging succeeds
  with probability at most `132040 · G · MD / 2^157 + 2^-18` with the low-depth query
  (`leanSphincs_qrpm_cat1_lowDepth`, a loss of `2^17.01` against AES-128) and at most
  `935.4 · G · MD / 2^157 + 2^-22` with the in-place query (`leanSphincs_qrpm_cat1_inPlace`, a
  loss of `2^9.87`): **not** category 1 with either circuit. Against `2^170`:
  `7662797 · G · MD / 2^170 + 2^-22` (`leanSphincs_qrpm_cat1_inPlace_2016`).
-/

open IPFunctor
open scoped ENNReal
open _root_.Sphincs

namespace Quantum.Cost.Nist

/-- **The leanSPHINCS QRPM linear term against the AES curve**: with `q ≤ G / GK`, `q ≤ 2^88` and
`MD ≥ 2^40`, `q / 2^89 ≤ E √(G · MD / 2^157)` once `2^27 / GK ≤ E²`. -/
theorem linTermQrpmS_le {GK G MD q E : ℝ} (hGK : 0 < GK) (hG : 0 ≤ G) (hMD : 2 ^ 40 ≤ MD)
    (hq0 : 0 ≤ q) (hq : q ≤ G / GK) (hq88 : q ≤ 2 ^ 88) (hE : 2 ^ 27 / GK ≤ E ^ 2)
    (hE0 : 0 ≤ E) :
    q / 2 ^ 89 ≤ E * √(aesCurve aesK2022 G MD) := by
  have hp : G / 2 ^ 117 ≤ aesCurve aesK2022 G MD := by
    unfold aesCurve aesK2022
    have h := mul_le_mul_of_nonneg_left hMD hG
    calc G / 2 ^ 117 = G * 2 ^ 40 / 2 ^ 157 := by ring
      _ ≤ G * MD / 2 ^ 157 := div_le_div_of_nonneg_right h (by positivity)
  have hqq : q * q ≤ G / GK * 2 ^ 88 := mul_le_mul hq hq88 hq0 (by positivity)
  have h2 : 1 / 2 ^ 178 * (G / GK * 2 ^ 88) = 2 ^ 27 / GK * (G / 2 ^ 117) := by
    field_simp
  have hsq : (q / 2 ^ 89) ^ 2 ≤ E ^ 2 * aesCurve aesK2022 G MD := by
    calc (q / 2 ^ 89) ^ 2 = 1 / 2 ^ 178 * (q * q) := by ring
      _ ≤ 1 / 2 ^ 178 * (G / GK * 2 ^ 88) := mul_le_mul_of_nonneg_left hqq (by positivity)
      _ = 2 ^ 27 / GK * (G / 2 ^ 117) := h2
      _ ≤ E ^ 2 * (G / 2 ^ 117) := mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ E ^ 2 * aesCurve aesK2022 G MD := mul_le_mul_of_nonneg_left hp (sq_nonneg E)
  calc q / 2 ^ 89 = √((q / 2 ^ 89) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √(E ^ 2 * aesCurve aesK2022 G MD) := Real.sqrt_le_sqrt hsq
    _ = E * √(aesCurve aesK2022 G MD) := by
        rw [Real.sqrt_mul (sq_nonneg E), Real.sqrt_sq hE0]

set_option exponentiation.threshold 200 in
/-- **The leanSPHINCS QRPM factor at the low-depth Keccak-f query** against `2^157`:
`μ ≤ 356.14` on `MaxDepthRange`. -/
theorem mu_sphincsQrpm_lowDepth_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 1566 641 aesK2022 keccakQueryGatesLowDepth keccakQueryDepthLowDepth MD ≤ 356.14 := by
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
/-- **The leanSPHINCS QRPM factor at the in-place Keccak-f query** against `2^157`:
`μ ≤ 29.197` on `MaxDepthRange`. -/
theorem mu_sphincsQrpm_inPlace_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 1566 641 aesK2022 keccakQueryGatesInPlace keccakQueryDepthInPlace MD ≤ 29.197 := by
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

/-- **leanSPHINCS in the QRPM against AES-128**, for any per-call cost of `GK` gates and depth
`DK` per Keccak-f query: an adversary within `G` gates, depth charge `MD > 0` and at most `2^88`
permutation calls forges with probability at most
`(μ √(G · MD / K) + min (G / GK) 2^88 / 2^89 + 57 · 2^30 / 2^64)²`,
`μ = mu 1566 641 K GK DK MD`. -/
theorem leanSphincs_qrpm_nist {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) (Γ : GateSet)
    (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : Qrpm.SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (Qrpm.permGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (Qrpm.permDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq : G / GK ≤ 2 ^ 88) (hMD : 0 < MD) {K : ℝ} (hK : 0 < K) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal ((mu 1566 641 K GK DK MD * √(aesCurve K G MD) +
        min ((G : ℝ) / GK) (2 ^ 88) / 2 ^ 89 + 57 * 2 ^ 30 / 2 ^ 64) ^ 2) := by
  refine (Qrpm.leanSphincs_qrpm_gateDepth_closed hGK hDK Γ δ G MD A hG hD hS hq).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Nat.cast_min]
  have hq0 : (0 : ℝ) ≤ ((G / GK : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqG : ((G / GK : ℕ) : ℝ) ≤ (G : ℝ) / GK := Nat.cast_div_le
  have hq88 : ((G / GK : ℕ) : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  have hmin : ((G / GK : ℕ) : ℝ) ≤ min ((G : ℝ) / GK) (2 ^ 88) := le_min hqG hq88
  have hμ := mu_nonneg (a := 1566) (b := 641) (K := K) (GK := GK) (DK := DK)
    (MD := MD) (by norm_num) (by norm_num)
  have h := parBound_le_aesCurve (a := 1566) (e := 0) (b := 641) (c := 57 * 2 ^ 30)
    (by norm_num) le_rfl (by norm_num) (by norm_num) hK (by exact_mod_cast hGK)
    (by exact_mod_cast hDK) (by exact_mod_cast hMD) hq0 (Nat.cast_nonneg (MD / DK)) hqG
    Nat.cast_div_le
  simp only [zero_mul, zero_div, add_zero] at h
  have hL := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have ht : ((G / GK : ℕ) : ℝ) / 2 ^ 89 ≤ min ((G : ℝ) / GK) (2 ^ 88) / 2 ^ 89 := by
    gcongr
  have e1 : (1566 * √(((G / GK : ℕ) : ℝ) * min ((MD / DK : ℕ) : ℝ) ((G / GK : ℕ) : ℝ)) +
      ((G / GK : ℕ) : ℝ) / 2 ^ 25 + 641 * √((G / GK : ℕ) : ℝ) + 57 * 2 ^ 30) / 2 ^ 64 =
      (1566 * √(((G / GK : ℕ) : ℝ) * min ((MD / DK : ℕ) : ℝ) ((G / GK : ℕ) : ℝ)) +
        641 * √((G / GK : ℕ) : ℝ) + 57 * 2 ^ 30) / 2 ^ 64 + ((G / GK : ℕ) : ℝ) / 2 ^ 89 := by
    ring
  rw [e1]
  linarith

set_option exponentiation.threshold 200 in
/-- **Category 1 at the low-depth Keccak-f query** (Song, Jang, Seo 2023): within NIST's 2022
threshold, `G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange` and at most `2^88` permutation
calls, forging succeeds with probability at most `132040 · G · MD / 2^157 + 2^-18`. This is
**not** category 1: it loses the factor `132040 = 2^17.01` against AES-128 (`μ ≤ 356.14`, linear
term `7.229 √p`). -/
theorem leanSphincs_qrpm_cat1_lowDepth (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesLowDepth)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthLowDepth)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq : G / keccakQueryGatesLowDepth ≤ 2 ^ 88)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (132040 * aesCurve aesK2022 G MD + (2 ^ 18)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  have hGK : (0 : ℝ) < keccakQueryGatesLowDepth := by norm_num [keccakQueryGatesLowDepth_eq]
  have hmin0 : 0 ≤ min ((G : ℝ) / keccakQueryGatesLowDepth) (2 ^ 88) :=
    le_min (div_nonneg (Nat.cast_nonneg G) hGK.le) (by positivity)
  refine (leanSphincs_qrpm_nist (by norm_num [cleanQueryGates, keccakfGatesLowDepth])
    (by norm_num [cleanQueryDepth, keccakfDepthLowDepth])
    Γ δ G MD A hG hD hS hq (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one_sqrt (mu_nonneg (by norm_num) (by norm_num))
    (mu_sphincsQrpm_lowDepth_le hMD) (E := 7.229) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (by positivity) ?_
  refine linTermQrpmS_le hGK (Nat.cast_nonneg G) hMD.1 hmin0 (min_le_left _ _)
    (min_le_right _ _) ?_ (by norm_num)
  rw [keccakQueryGatesLowDepth_eq]
  norm_num

set_option exponentiation.threshold 200 in
/-- **Category 1 at the in-place Keccak-f query** (Amy et al. 2016): within NIST's 2022
threshold, `G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange` and at most `2^88` permutation
calls, forging succeeds with probability at most `935.4 · G · MD / 2^157 + 2^-22`. This is
**not** category 1: it loses the factor `935.4 = 2^9.87` against AES-128 (`μ ≤ 29.197`, linear
term `1.3852 √p`). -/
theorem leanSphincs_qrpm_cat1_inPlace (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq : G / keccakQueryGatesInPlace ≤ 2 ^ 88)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (935.4 * aesCurve aesK2022 G MD + (2 ^ 22)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  have hGK : (0 : ℝ) < keccakQueryGatesInPlace := by norm_num [keccakQueryGatesInPlace_eq]
  have hmin0 : 0 ≤ min ((G : ℝ) / keccakQueryGatesInPlace) (2 ^ 88) :=
    le_min (div_nonneg (Nat.cast_nonneg G) hGK.le) (by positivity)
  refine (leanSphincs_qrpm_nist (by norm_num [cleanQueryGates, keccakfGatesInPlace])
    (by norm_num [cleanQueryDepth, keccakfDepthInPlace])
    Γ δ G MD A hG hD hS hq (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one_sqrt (mu_nonneg (by norm_num) (by norm_num))
    (mu_sphincsQrpm_inPlace_le hMD) (E := 1.3852) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (by positivity) ?_
  refine linTermQrpmS_le hGK (Nat.cast_nonneg G) hMD.1 hmin0 (min_le_left _ _)
    (min_le_right _ _) ?_ (by norm_num)
  rw [keccakQueryGatesInPlace_eq]
  norm_num

/-- **Against NIST's 2016 threshold** (`2^170 / MAXDEPTH`), the in-place query gives
`7662797 · G · MD / 2^170 + 2^-22` within `G · MD ≤ 2^157` and at most `2^88` permutation
calls. -/
theorem leanSphincs_qrpm_cat1_inPlace_2016 (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : Qrpm.SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrpm.permGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrpm.permDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq : G / keccakQueryGatesInPlace ≤ 2 ^ 88)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (7662797 * aesCurve aesK2016 G MD + (2 ^ 22)⁻¹) := by
  refine (leanSphincs_qrpm_cat1_inPlace Γ δ G MD A hG hD hS hq hMD hGM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ aesCurve aesK2016 G MD := by
    unfold aesCurve aesK2016
    positivity
  rw [aesCurve_aesK2022]
  nlinarith

end Quantum.Cost.Nist

end
