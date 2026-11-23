module

public import Quantum.StdModel.Qrom.XmssCpre
public import Quantum.StdModel.Qrom.SphincsCpre

@[expose] public section

/-!
# The CPRE bounds in closed form

The constants of the QROM CPRE bound at 128-bit chain values, 256-bit hash outputs and truncation
fibers of `2^128` digests:

* `kappaC_le`: the mass per call is at most `2^-128`;
* `sqrt_gradeEta_le`: `√(gradeEta 2^128) ≤ (3 + 2^-64) / 2^64`;
* `cpre_closed_le`: the bound of `probAvg_cpre_slRed_le` at `v` reduction and decision reads is at
  most `((5.001 n + b) / 2^64)²` whenever `v (3 + 2^-64) + √v ≤ b`.

At leanXMSS B3 (`v = 873`) the CPRE success is at most `((5.001 n + 2650) / 2^64)²`; at
leanSPHINCS B5 (`v = 1203`), `((5.001 n + 3645) / 2^64)²`, for an adversary of `n` hash calls.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

set_option synthInstance.maxSize 2000

namespace Quantum.StdModel.Qrom.CpreQ

open HashSig (HashOutput)

theorem card_hashOutput_eq : Fintype.card HashOutput = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem natCast_inv_eq_ofReal (k : ℕ) (hk : 0 < k) :
    ((k : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / k) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hk), ENNReal.ofReal_natCast]

/-- **The mass per call** at `2^128` chain values and fibers of `2^128` digests: `2^-128`. -/
theorem kappaC_le {Val : Type} [Fintype Val] (hV : Fintype.card Val = 2 ^ 128) :
    kappaC Val (2 ^ 128) ≤ ENNReal.ofReal (1 / 2 ^ 128) := by
  unfold kappaC
  rw [hV, card_hashOutput_eq, natCast_inv_eq_ofReal (2 ^ 128) (by positivity),
    natCast_inv_eq_ofReal (2 ^ 256) (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  exact max_le (ENNReal.ofReal_le_ofReal (by norm_num)) (ENNReal.ofReal_le_ofReal (by norm_num))

/-- **The price of a read of a step cell** at fibers of `2^128` digests:
`√(gradeEta 2^128) ≤ (3 + 2^-64) / 2^64`. -/
theorem sqrt_gradeEta_le : √(gradeEta HashOutput (2 ^ 128)) ≤ (3 + 1 / 2 ^ 64) / 2 ^ 64 := by
  have hH : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by exact_mod_cast card_hashOutput_eq
  unfold gradeEta
  rw [Real.sqrt_sq (by positivity), hH]
  push_cast
  have h1 : √((2 : ℝ) ^ 128 / 2 ^ 256) ≤ 1 / 2 ^ 64 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by norm_num⟩
  have h2 : √(((2 : ℝ) ^ 128 + 2) / 2 ^ 256) ≤ (1 + 1 / 2 ^ 64) / 2 ^ 64 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by norm_num⟩
  linarith

theorem ofReal_rpow_inv_two (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal x ^ (2⁻¹ : ℝ) = ENNReal.ofReal √x := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow, one_div]

/-- **The CPRE bound in closed form**: at `2^128` chain values, `n` adversary hash calls and `v`
reduction and decision reads of step cells, the bound of `probAvg_cpre_slRed_le` is at most
`((5.001 n + b) / 2^64)²` for `v (3 + 2^-64) + √v ≤ b`. -/
theorem cpre_closed_le {Val : Type} [Fintype Val] (hV : Fintype.card Val = 2 ^ 128) (n v : ℕ)
    {b : ℝ} (hb : (v : ℝ) * (3 + 1 / 2 ^ 64) + √(v : ℝ) ≤ b) :
    (((n + v : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
        (4 * (n * (n * kappaC Val (2 ^ 128)))) ^ (2⁻¹ : ℝ) +
        ((v : ℝ≥0∞) * kappaC Val (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ENNReal.ofReal (((5.001 * n + b) / 2 ^ 64) ^ 2) := by
  have hκ := kappaC_le hV
  refine (pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hκ zero_le) zero_le) zero_le) (by norm_num)))
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hκ zero_le) (by norm_num))) 2).trans ?_
  have e1 : ((n + v : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (((n + v : ℕ) : ℝ) * √(gradeEta HashOutput (2 ^ 128))) := by
    rw [ofReal_rpow_inv_two _ (gradeEta_nonneg _ _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  have e2 : (4 * ((n : ℝ≥0∞) * (n * ENNReal.ofReal (1 / 2 ^ 128)))) =
      ENNReal.ofReal (4 * (n * (n * (1 / 2 ^ 128)))) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have e3 : (v : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 128) = ENNReal.ofReal (v * (1 / 2 ^ 128)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [e1, e2, e3, ofReal_rpow_inv_two _ (by positivity), ofReal_rpow_inv_two _ (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
  have hk : √(4 * ((n : ℝ) * (n * (1 / 2 ^ 128)))) ≤ 2 * n / 2 ^ 64 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, le_of_eq (by ring)⟩
  have hv : √((v : ℝ) * (1 / 2 ^ 128)) ≤ √(v : ℝ) / 2 ^ 64 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact le_of_eq (by ring)⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ((n + v : ℕ) : ℝ) * √(gradeEta HashOutput (2 ^ 128)) +
          √(4 * ((n : ℝ) * (n * (1 / 2 ^ 128)))) + √((v : ℝ) * (1 / 2 ^ 128))
      ≤ ((n + v : ℕ) : ℝ) * ((3 + 1 / 2 ^ 64) / 2 ^ 64) + 2 * n / 2 ^ 64 +
          √(v : ℝ) / 2 ^ 64 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left sqrt_gradeEta_le (Nat.cast_nonneg _))
          hk) hv
    _ = ((n : ℝ) * (5 + 1 / 2 ^ 64) + ((v : ℝ) * (3 + 1 / 2 ^ 64) + √(v : ℝ))) / 2 ^ 64 := by
        push_cast
        ring
    _ ≤ (5.001 * n + b) / 2 ^ 64 :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)

end Quantum.StdModel.Qrom.CpreQ

namespace Quantum.StdModel.Xmss

open HashSig HashSig.OverPermutation LeanXmss
open Quantum.StdModel Props
open Quantum.StdModel.Qrom.CpreQ (cpre_closed_le)

/-- **The leanXMSS CPRE game in the QROM (B3), in closed form**: for an adversary of `n` hash
calls, `probAvg ≤ ((5.001 n + 2650) / 2^64)²`. -/
theorem probAvg_cpreRed_le_closed
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery) {n k : ℕ}
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hk : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) k) :
    romWorld.probAvg ((cpre romWorld xmssChains noEval).game (cpreRed romWorld A)) ≤
      ENNReal.ofReal (((5.001 * n + 2650) / 2 ^ 64) ^ 2) := by
  have hs : √(873 : ℝ) ≤ 30 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb : ((873 : ℕ) : ℝ) * (3 + 1 / 2 ^ 64) + √((873 : ℕ) : ℝ) ≤ 2650 := by
    push_cast
    norm_num
    linarith
  exact (probAvg_cpreRed_le A hn hk).trans (cpre_closed_le (card_bitVec_eq 128) n 873 hb)

end Quantum.StdModel.Xmss

namespace Quantum.StdModel.Qrom.SphInst

open HashSig hiding PublicKey
open _root_.Sphincs hiding HashDomain
open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.StdModel.Qrom.CpreQ (cpre_closed_le)

/-- **The leanSPHINCS CPRE game in the QROM (B5), in closed form**: for an adversary of `n` hash
calls, `probAvg ≤ ((5.001 n + 3645) / 2^64)²`. -/
theorem probAvg_cpreRed_le_closed (A : SAdv romWorld) {n k : ℕ}
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hk : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) k) :
    romWorld.probAvg ((cpre romWorld cpreChains slotColl).game (cpreRed romWorld A)) ≤
      ENNReal.ofReal (((5.001 * n + 3645) / 2 ^ 64) ^ 2) := by
  have hs : √(1203 : ℝ) ≤ 35 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb : ((1203 : ℕ) : ℝ) * (3 + 1 / 2 ^ 64) + √((1203 : ℕ) : ℝ) ≤ 3645 := by
    push_cast
    norm_num
    linarith
  have hD : Fintype.card Digest = 2 ^ 128 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    rfl
  exact (probAvg_cpreRed_le A hn hk).trans (cpre_closed_le hD n 1203 hb)

end Quantum.StdModel.Qrom.SphInst

end
