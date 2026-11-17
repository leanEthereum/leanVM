module

public import Quantum.Cost.Nist
public import Quantum.Cost.ParallelSphincs

@[expose] public section

/-!
# NIST category 1: leanSPHINCS in the QROM against AES-128 key search

Nist's comparison (`parBound_le_aesCurve`) applied to leanSPHINCS's depth-aware QROM closed form
`((5.86 √(q · min d q) + 2^-55 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`
(`leanSphincs_qrom_gateDepth_closed`):

* `leanSphincs_qrom_nist`: forging is at most
  `(μ √(G · MD / K) + 2^-55 G / (GK 2^64) + 1.818 · 2^32 / 2^64)²` for every per-call cost.
* The factor against `2^157` on all of `MaxDepthRange` (`mu_sphincs_lowDepth_le`,
  `mu_sphincs_inPlace_le`): `μ ≤ 1.337` with the low-depth Keccak query (Song, Jang, Seo 2023)
  and `μ ≤ 0.11` with the in-place query (Amy et al. 2016).
* **Category 1** within NIST's 2022 threshold `G · MD ≤ 2^157`: with the low-depth query forging
  succeeds with probability at most `1.79 · G · MD / 2^157 + 2^-29`
  (`leanSphincs_qrom_cat1_lowDepth`), which is **not** category 1 (a loss of the factor
  `1.79 = 2^0.84` against AES-128); with the in-place query at most
  `0.0122 · G · MD / 2^157 + 2^-32` (`leanSphincs_qrom_cat1_inPlace`), which is. Against the
  2016 threshold `2^170` the in-place query gives `100 · G · MD / 2^170 + 2^-32`
  (`leanSphincs_qrom_cat1_inPlace_2016`), not category 1 in the 2016 metric.
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Cost.Nist

set_option exponentiation.threshold 200 in
/-- **The leanSPHINCS factor at the low-depth query** against `2^157`: `μ ≤ 1.337` on
`MaxDepthRange`. -/
theorem mu_sphincs_lowDepth_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 5.86 257.3 aesK2022 keccakQueryGatesLowDepth keccakQueryDepthLowDepth MD ≤ 1.337 := by
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
/-- **The leanSPHINCS factor at the in-place query** against `2^157`: `μ ≤ 0.11` on
`MaxDepthRange`. -/
theorem mu_sphincs_inPlace_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 5.86 257.3 aesK2022 keccakQueryGatesInPlace keccakQueryDepthInPlace MD ≤ 0.11 := by
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

/-- A parallel gate-set adversary against leanSPHINCS in the QROM. -/
abbrev SphincsParGateAdversary (Γ : GateSet) :=
  Qrom.ParGateAdversary Γ PublicKey Message (Option Signature) Forgery

/-- **leanSPHINCS in the QROM against AES-128**, for any per-call cost of `GK` gates and depth
`DK`: an adversary within `G` gates and depth charge `MD > 0` forges with probability at most
`(μ √(G · MD / K) + 2^-55 G / (GK 2^64) + 1.818 · 2^32 / 2^64)²`,
`μ = mu 5.86 257.3 K GK DK MD`. -/
theorem leanSphincs_qrom_nist {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) (Γ : GateSet)
    (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (Qrom.hashGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (Qrom.hashDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) signatureLimit)
    (hMD : 0 < MD) {K : ℝ} (hK : 0 < K) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Sphincs.sphincsRom A.toAdversary ≤
      ENNReal.ofReal ((mu 5.86 257.3 K GK DK MD * √(aesCurve K G MD) +
        (2 ^ 55)⁻¹ * (G / GK) / 2 ^ 64 + 1.818 * 2 ^ 32 / 2 ^ 64) ^ 2) := by
  refine (Qrom.leanSphincs_qrom_gateDepth_closed hGK hDK Γ δ G MD A hG hD hS).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Nat.cast_min]
  exact parBound_le_aesCurve (by norm_num) (by positivity) (by positivity) (by positivity) hK
    (by exact_mod_cast hGK) (by exact_mod_cast hDK) (by exact_mod_cast hMD) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) Nat.cast_div_le Nat.cast_div_le

set_option exponentiation.threshold 200 in
/-- **Category 1 at the low-depth Keccak query** (Song, Jang, Seo 2023): within NIST's 2022
threshold, `G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange`, forging succeeds with probability
at most `1.79 · G · MD / 2^157 + 2^-29`. This is **not** category 1: against the AES-128 success
`G · MD / 2^157` it loses the factor `1.79 = 2^0.84` (`μ ≤ 1.337`). -/
theorem leanSphincs_qrom_cat1_lowDepth (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesLowDepth)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthLowDepth)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) signatureLimit)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Sphincs.sphincsRom A.toAdversary ≤
      ENNReal.ofReal (1.79 * aesCurve aesK2022 G MD + (2 ^ 29)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  refine (leanSphincs_qrom_nist (by norm_num [cleanQueryGates, keccakfGatesLowDepth])
    (by norm_num [cleanQueryDepth, keccakfDepthLowDepth])
    Γ δ G MD A hG hD hS (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one (mu_nonneg (by norm_num) (by norm_num))
    (mu_sphincs_lowDepth_le hMD) (E := 1e-6) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (by positivity) (linTerm_le_aesCurve (by norm_num)
      (by norm_num [keccakQueryGatesLowDepth_eq]) (Nat.cast_nonneg G) hMD.1 ?_)
  rw [keccakQueryGatesLowDepth_eq]
  norm_num

set_option exponentiation.threshold 200 in
/-- **Category 1 at the in-place Keccak query** (Amy et al. 2016): within NIST's 2022 threshold,
`G · MD ≤ 2^157`, for every `MD` in `MaxDepthRange`, forging succeeds with probability at most
`0.0122 · G · MD / 2^157 + 2^-32`, below the AES-128 success `G · MD / 2^157` up to `2^-32`
(`μ ≤ 0.11`). -/
theorem leanSphincs_qrom_cat1_inPlace (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) signatureLimit)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Sphincs.sphincsRom A.toAdversary ≤
      ENNReal.ofReal (0.0122 * aesCurve aesK2022 G MD + (2 ^ 32)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  refine (leanSphincs_qrom_nist (by norm_num [cleanQueryGates, keccakfGatesInPlace])
    (by norm_num [cleanQueryDepth, keccakfDepthInPlace])
    Γ δ G MD A hG hD hS (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one (mu_nonneg (by norm_num) (by norm_num))
    (mu_sphincs_inPlace_le hMD) (E := 1e-6) (by norm_num) (by positivity) hp.1 hp.2
    (by norm_num) (by norm_num) (by positivity) (linTerm_le_aesCurve (by norm_num)
      (by norm_num [keccakQueryGatesInPlace_eq]) (Nat.cast_nonneg G) hMD.1 ?_)
  rw [keccakQueryGatesInPlace_eq]
  norm_num

/-- **Against NIST's 2016 threshold** (`2^170 / MAXDEPTH`), the in-place query gives only
`100 · G · MD / 2^170 + 2^-32` within `G · MD ≤ 2^157`: not category 1 in the 2016 metric. -/
theorem leanSphincs_qrom_cat1_inPlace_2016 (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) signatureLimit)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Sphincs.sphincsRom A.toAdversary ≤
      ENNReal.ofReal (100 * aesCurve aesK2016 G MD + (2 ^ 32)⁻¹) := by
  refine (leanSphincs_qrom_cat1_inPlace Γ δ G MD A hG hD hS hMD hGM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ aesCurve aesK2016 G MD := by
    unfold aesCurve aesK2016
    positivity
  rw [aesCurve_aesK2022]
  nlinarith

end Quantum.Cost.Nist

end
