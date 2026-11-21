module

public import Quantum.Sphincs.Assembly.Depth.Security
public import Quantum.Sphincs.Assembly.Depth.TermsValue
public import Quantum.Sphincs.Assembly.Depth.CapsValue

@[expose] public section

/-!
# The size of the depth-aware leanSPHINCS QRPM bound

Security's `sphincsQrpmDepthBound q d` in closed form for `q ≤ 2^88`, `d' = min d q`
(`sphincsQrpmDepthBound_le`):
`((1566 √(q d') + q / 2^25 + 2^10 √q + 2^36) / 2^64)²`.

* `a = 1566`: the `h` rounds `√(24 · 2^-128) ≤ 4.9`, the coverage Half event
  `√(24 · 2^16 rhoCov · 2^-128) ≤ 1522` (TermsValue's `advBDcov_le`) and the hybrid
  `√(4 · 10 · 6 · 6.25 · 2^-128) ≤ 39` (`hybTermSD_le`);
* `e`: CapsValue's classical cap (the `RecJ` term, growing like `q^1.75`, absorbed linearly up to
  `2^88`) and the capacity residual `capTermSD q ≤ q 2^-111` (`capTermSD_le` at `M = 2^46`);
* `b`, `c`: CapsValue's classical cap, the verification's reads `2711`, the coverage constant
  `2^20`, the rest of the event term `3 · 2^31` and the hybrid's read mass `30 · 2^30`.

At `q ≤ 2^64` calls in `d ≤ 2^40` rounds the bound is at most `1/6`
(`sphincsQrpmDepthBound_two_pow_64_40_le`).
-/

open scoped ENNReal

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (rpow_inv_two_le_ofReal sq_add_rpow_inv_two_le pow_two_rpow_inv_two
  inv_two_pow_eq_ofReal)

namespace Quantum.Sphincs.Assembly

section closed

set_option exponentiation.threshold 1100 in
/-- **The price-free adversary amplitude at depth `d`** for `q ≤ 2^88`: `advAD q d ≤
(4.899 √(q d') + 2711) 2^-64 + q 2^-111`. -/
theorem advAD_le {q d : ℕ} (hq : q ≤ 2 ^ 88) :
    advAD q d ≤ ENNReal.ofReal (4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 +
      q / 2 ^ 111 + 2711 / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hsq := Real.sq_sqrt hX
  have hq' : (q : ℝ) ≤ 2 ^ 88 := by exact_mod_cast hq
  have hx : 6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (24 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) := by
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    ring
  have hh := rpow_inv_two_le_ofReal (a := 4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64)
    (by positivity) hx (by
      rw [div_pow, mul_pow, hsq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith)
  have hc := capTermSD_le (q := q) (M := 2 ^ 46) (by positivity) (by
    rw [show ((2 : ℝ) ^ 46) ^ 2 = 2 ^ 92 by norm_num]
    linarith)
  have hc' : ENNReal.ofReal (4 * q * (26 * (2 ^ 46 : ℝ) ^ 3 / 2 ^ 256)) ≤
      ENNReal.ofReal (q / 2 ^ 111) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [show 4 * (q : ℝ) * (26 * (2 ^ 46 : ℝ) ^ 3 / 2 ^ 256) = q * (104 / 2 ^ 118) by ring]
    rw [div_eq_mul_one_div (q : ℝ)]
    exact mul_le_mul_of_nonneg_left (by norm_num) hq0
  unfold advAD
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (add_le_add hh (hc.trans hc')) (verReadD_le (hq.trans (by norm_num)))

set_option exponentiation.threshold 1100 in
/-- **The square-rooted event term at depth `d`**, for `q ≤ 2^88` and any real bound
`√clsBoundSD q ≤ K` (`K ≥ 0`): `√eventTermSphD q d ≤ (4.899 √(q d') + 2711) 2^-64 + q 2^-111 +
(1522 √(q d') + 2^20) 2^-64 + K + 2^-49 + 3 · 2^-33`. -/
theorem eventTermSphD_rpow_le {q d : ℕ} (hq : q ≤ 2 ^ 88) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : clsBoundSD q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal K) :
    eventTermSphD q d ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal
      (4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 111 + 2711 / 2 ^ 64 +
        (1522 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
        (K + 1 / 2 ^ 49) + 3 / 2 ^ 33) := by
  have hs := rpow_inv_two_le_ofReal (a := 3 / 2 ^ 33) (by positivity) restSph_le (by norm_num)
  have hv := rpow_inv_two_le_ofReal (a := 1 / 2 ^ 49) (by positivity)
    (verSD_le (hq.trans (by norm_num))) (by norm_num)
  have hcv : (clsBoundSD q + (verLinSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^
      (2⁻¹ : ℝ) ≤ ENNReal.ofReal (K + 1 / 2 ^ 49) := by
    rw [ENNReal.ofReal_add hK0 (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hK hv)
  have e : eventTermSphD q d = (advAD q d + (advBD q d ^ 2 * covPS) ^ (2⁻¹ : ℝ) +
      (clsBoundSD q + (verLinSD q + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 +
      (ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
        ENNReal.ofReal (1 / 2 ^ 189) + ENNReal.ofReal (hConflictCap signatureLimit) +
        2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) + winChgCap + stageCap) := by
    unfold eventTermSphD eventTermSphG eventTermG
    simp only [add_assoc]
  rw [e]
  refine (sq_add_rpow_inv_two_le _ _).trans ((add_le_add (add_le_add (add_le_add (advAD_le hq)
    (advBDcov_le q d)) hcv) hs).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **The closed form from a real bound on the classical cap**: for `q ≤ 2^88`, if
`√clsBoundSD q ≤ K` and the term bounds sum to at most `F - 2^-34`, then
`sphincsQrpmDepthBound q d ≤ F²`. -/
theorem sphincsQrpmDepthBound_le_of {q d : ℕ} (hq : q ≤ 2 ^ 88) {K F : ℝ} (hK0 : 0 ≤ K)
    (hK : clsBoundSD q ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal K)
    (hF : 4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 111 + 2711 / 2 ^ 64 +
        (1522 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
        (K + 1 / 2 ^ 49) + 3 / 2 ^ 33 +
        (39 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 30 / 2 ^ 34) ≤ F - 1 / 2 ^ 34) :
    sphincsQrpmDepthBound q d ≤ ENNReal.ofReal (F ^ 2) := by
  have h1 := eventTermSphD_rpow_le (d := d) hq hK0 hK
  have h2 := hybTermSD_le q d
  have h3 := stageCap_le
  have hm := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : (4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 111 + 2711 / 2 ^ 64 +
        (1522 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
        (K + 1 / 2 ^ 49) + 3 / 2 ^ 33 +
        (39 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 30 / 2 ^ 34)) ^ 2 + 1 / 2 ^ 126 ≤ F ^ 2 := by
    have h0 : (0 : ℝ) ≤ 4899 / 1000 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 111 +
        2711 / 2 ^ 64 + (1522 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 2 ^ 20 / 2 ^ 64) +
        (K + 1 / 2 ^ 49) + 3 / 2 ^ 33 +
        (39 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 30 / 2 ^ 34) := by positivity
    calc _ ≤ (F - 1 / 2 ^ 34) ^ 2 + 1 / 2 ^ 126 := by gcongr
      _ ≤ F ^ 2 := by nlinarith
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hsq)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold sphincsQrpmDepthBound
  gcongr

/-- **The depth-aware leanSPHINCS QRPM bound in closed form**: for `q ≤ 2^88` and every `d`,
with `d' = min d q`,
`sphincsQrpmDepthBound q d ≤ ((1566 √(q d') + q / 2^25 + 641 √q + 57 · 2^30) / 2^64)²`. -/
theorem sphincsQrpmDepthBound_le {q d : ℕ} (hq : q ≤ 2 ^ 88) :
    sphincsQrpmDepthBound q d ≤ ENNReal.ofReal (((1566 * √((q : ℝ) * (min d q : ℕ)) +
      q / 2 ^ 25 + 641 * √(q : ℝ) + 57 * 2 ^ 30) / 2 ^ 64) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hm0 := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  refine sphincsQrpmDepthBound_le_of hq (by positivity) (clsBoundSD_rpow_le hq) ?_
  have h1 : (q : ℝ) / 2 ^ 111 + 7 / 2 ^ 28 * q / 2 ^ 64 ≤ q / 2 ^ 25 / 2 ^ 64 := by
    have e3 : (q : ℝ) / 2 ^ 111 + 7 / 2 ^ 28 * q / 2 ^ 64 = q * (1 / 2 ^ 111 + 7 / 2 ^ 92) := by
      ring
    have e4 : (q : ℝ) / 2 ^ 25 / 2 ^ 64 = q * (1 / 2 ^ 89) := by ring
    rw [e3, e4]
    exact mul_le_mul_of_nonneg_left (by norm_num) hq0
  have e : (1566 * √((q : ℝ) * (min d q : ℕ)) + q / 2 ^ 25 + 641 * √(q : ℝ) + 57 * 2 ^ 30) /
      2 ^ 64 = 1566 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + q / 2 ^ 25 / 2 ^ 64 +
        641 * √(q : ℝ) / 2 ^ 64 + 57 * 2 ^ 30 / 2 ^ 64 := by ring
  have e2 : (641 * √(q : ℝ) + 7 / 2 ^ 28 * q + 19 * 2 ^ 30) / 2 ^ 64 =
      641 * √(q : ℝ) / 2 ^ 64 + 7 / 2 ^ 28 * q / 2 ^ 64 + 19 * 2 ^ 30 / 2 ^ 64 := by ring
  rw [e, e2]
  linarith

set_option exponentiation.threshold 1100 in
/-- **At most `2^64` permutation calls in at most `2^40` rounds**: `sphincsQrpmDepthBound q d ≤
1/6`. -/
theorem sphincsQrpmDepthBound_two_pow_64_40_le {q d : ℕ} (hq : q ≤ 2 ^ 64) (hd : d ≤ 2 ^ 40) :
    sphincsQrpmDepthBound q d ≤ (6 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hm : ((min d q : ℕ) : ℝ) ≤ 2 ^ 40 := by exact_mod_cast (min_le_left d q).trans hd
  have hs : √(q : ℝ) ≤ 2 ^ 32 :=
    (Real.sqrt_le_sqrt hq').trans_eq (by rw [show (2 : ℝ) ^ 64 = (2 ^ 32) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  have hsm : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 52 :=
    (Real.sqrt_le_sqrt (mul_le_mul hq' hm (Nat.cast_nonneg _) (by positivity))).trans_eq
      (by rw [show (2 : ℝ) ^ 64 * 2 ^ 40 = (2 ^ 52) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  refine (sphincsQrpmDepthBound_le (hq.trans (by norm_num))).trans ?_
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((1566 * √((q : ℝ) * (min d q : ℕ)) + q / 2 ^ 25 + 641 * √(q : ℝ) + 57 * 2 ^ 30) /
        2 ^ 64) ^ 2
      ≤ ((1566 * 2 ^ 52 + 2 ^ 64 / 2 ^ 25 + 641 * 2 ^ 32 + 57 * 2 ^ 30) / 2 ^ 64) ^ 2 := by
        gcongr
    _ ≤ 6⁻¹ := by norm_num

/-- **leanSPHINCS against a depth-limited parallel adversary, in closed form**: a parallel
adversary of total width `q ≤ 2^88`, at most `d` rounds and at most `signatureLimit` signing
requests forges with probability at most
`((1566 √(q min(d, q)) + q / 2^25 + 641 √q + 57 · 2^30) / 2^64)²`. -/
theorem winProbPar_le_closedForm (Ap : SAdversaryPar) {q d : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.widthCharge) q)
    (hd : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.roundCharge) d)
    (hs : ∀ pk, IPFunctor.IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq88 : q ≤ 2 ^ 88) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Quantum.Xmss.keccakStateEquiv
        Ap ≤ ENNReal.ofReal (((1566 * √((q : ℝ) * (min d q : ℕ)) + q / 2 ^ 25 +
          641 * √(q : ℝ) + 57 * 2 ^ 30) / 2 ^ 64) ^ 2) :=
  (winProbPar_le_sphincsQrpmDepthBound Ap hq hd hs).trans (sphincsQrpmDepthBound_le hq88)

end closed

end Quantum.Sphincs.Assembly

end
