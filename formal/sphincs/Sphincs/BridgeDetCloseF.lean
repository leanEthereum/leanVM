import Sphincs.BridgeSampleBoundF
import Sphincs.BridgeRoutes
import Sphincs.BridgeSatWRoutes
import Sphincs.BridgeDetMemo

/-! **The deterministic signer of the forest at 127 bits.** Small budgets (`q - keygenCost ≤ qh`):
the sample bound averaged over the prepared samples, in closed form from one rational check
`checkSmallF` at the right end `qh`. Large budgets: the weighted one-coin bound from a checked chain
of covers of the budgets above `qh`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### The closed form -/

/-- The coefficient of the failing share. -/
noncomputable def smallFailF (q : ℕ) : ℝ≥0∞ :=
  (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) * (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit)

/-- The sample-independent part of the small-budget bound. -/
noncomputable def smallMainFF (ρ : ℝ) (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) + ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

omit [Params] in
theorem ofReal_natCast_invF {n : ℕ} (hn : 0 < n) : ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]

theorem one_le_keygenCostF : 1 ≤ keygenCost := by
  unfold keygenCost
  have : 1 ≤ 2 ^ subtreeHeight := Nat.one_le_two_pow
  omega

/-- The cap term at the start is below `2^-201`. -/
theorem lam_start_leF (q : ℕ) : lam (H0.LmaxOf q) 0 q ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
  refine le_trans (H0.lam_start q) ?_
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2 : ℝ) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) = ((64 / 65 : ℝ) ^ 64) ^ 512 := by rw [← pow_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) ^ 512 := pow_le_pow_left₀ (by norm_num) (by norm_num) 512
    _ ≤ (1 / 2 : ℝ) ^ 201 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)

omit [Params] in
/-- The real inequality behind the closed form. The coin term is `2^-128 · (x^2 / 2) (2 − 1/M) 2^-128`
(a unit of budget is a contact attempt or a digest query, so the pairs are counted once); the
two cap terms, each at most `2^-201`, are paid by the `2^-60` slack like the failing shares. -/
theorem small_realFF (x qh q N ρ B c M : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (_hB : 0 ≤ B) (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hcheck : ρ + 2 ^ 128 * B + (2 * M - 1) * qh / (M * 2 ^ 129) + qh * c + 1 / 2 ^ 60 ≤ 2) :
    ρ * x / 2 ^ 128 + x * B + (2 ^ 128)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (1 / 2) ^ 201 + 2 * (q / 2 ^ 256) ≤
      q / 2 ^ 127 := by
  have hM0 : M ≠ 0 := by linarith
  have hr0 : 0 ≤ (2 - 1 / M) / 2 ^ 129 := by
    apply div_nonneg _ (by positivity)
    have : 1 / M ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have e : (2 * M - 1) * qh / (M * 2 ^ 129) = qh * ((2 - 1 / M) / 2 ^ 129) := by
    field_simp
  have e0 : (2 ^ 128 : ℝ)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) =
      x * (2 ^ 128)⁻¹ * (x * ((2 - 1 / M) / 2 ^ 129)) := by
    ring
  rw [e] at hcheck
  rw [e0]
  generalize (2 - 1 / M) / 2 ^ 129 = r at hr0 hcheck ⊢
  have h1 : x * r ≤ qh * r := mul_le_mul_of_nonneg_right hxq hr0
  have h2 : x * c ≤ qh * c := mul_le_mul_of_nonneg_right hxq hc
  have hbr : ρ + 2 ^ 128 * B + x * r + x * c ≤ 2 - 1 / 2 ^ 60 := by linarith
  have hmain : ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (x * r) + x * (2 ^ 128)⁻¹ * (x * c) =
      x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) := by
    field_simp
  have hmain' : x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) ≤
      x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) := mul_le_mul_of_nonneg_left hbr (by positivity)
  have hx1 : x * (2 ^ 128 : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  have hfail : ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 ≤ (x + N) * 2 * (1 / 2) ^ 201 := by
    have : x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ x + N := by
      calc x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ 1 * (x + N) := mul_le_mul_of_nonneg_right hx1 (by positivity)
        _ = x + N := one_mul _
    have hp : (0 : ℝ) ≤ (1 / 2) ^ 201 := by positivity
    nlinarith
  have hq0 : 0 ≤ q := by linarith
  have e201 : ((1 : ℝ) / 2) ^ 201 = 1 / 2 ^ 201 := by rw [div_pow, one_pow]
  rw [hmain]
  rw [e201] at hfail ⊢
  have hxq' : x ≤ 2 ^ 127 := le_trans hxq hqh
  have key : x * (2 ^ 128)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
      2 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
    have ex : x * (2 ^ 128 : ℝ)⁻¹ * (2 - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
        2 * (q / 2 ^ 256) = (x * (2 ^ 128 - 2 ^ 67) + (x + N) * 2 ^ 55 + 2 ^ 55 + q) / 2 ^ 255 := by
      field_simp
    have ey : q / (2 : ℝ) ^ 127 = q * 2 ^ 128 / 2 ^ 255 := by
      field_simp
    rw [ex, ey]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The small-budget bound in closed form**, with the two cap terms of the scan signer. -/
theorem small_closeFF (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
        qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2) :
    smallMainFF ρ q B c + smallFailF q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCostF
  have hq'1 : q' + 1 ≤ q := by omega
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hM : (1 : ℝ) ≤ (H0.scanM : ℝ) := by exact_mod_cast H0.scanM_pos
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hreal := small_realFF (q' : ℝ) qh q signatureLimit ρ B c (H0.scanM : ℝ) (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' hM hcheck
  have hr0 : (0 : ℝ) ≤ (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 := by
    apply div_nonneg _ (by positivity)
    have : 1 / (H0.scanM : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hq127 : (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  refine le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_right (lam_start_leF q') 2)) le_rfl) ?_
  have hC : ((Nat.choose q' 2 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((q' : ℝ) * q' / 2) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Nat.cast_choose_two]
    have h0 : (0 : ℝ) ≤ (q' : ℝ) := Nat.cast_nonneg _
    nlinarith
  unfold smallMainFF smallFailF
  rw [← hq'def]
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul' le_rfl (mul_le_mul' hC le_rfl))) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  rw [rateS_eqF, hhalf, hq256, hq127, ν_eq_ofReal, hnat q', hnat signatureLimit, h2]
  generalize (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 = r at hr0 hreal ⊢
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The seed-free bound and the deterministic signer -/

section Close

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win.** -/
theorem small_seedFree_boundF (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      (smallMainFF ρ q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost)) + smallFailF q * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q) ?_
  set A := smallMainFF ρ q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
    2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) with hA
  set C := smallFailF q with hC
  have hκ1R : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ1
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
        A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared known hk
    refine le_trans (sample_boundF hb adversary hnr q hq parameterOutput fixed highs remaining prepared
      hprepared known hk ρ hN (κ : ℝ) hκ hκ1R b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr) (le_of_eq ?_)
    rw [hA, hC]
    unfold smallMainFF smallFailF
    rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.2 hκ0)]
    ring
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table :
    ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  refine tsum_bound_le _ _ A C _ fun prepared hprepared => ?_
  refine le_trans (tsum_bound_le _ _ A C (fun _ => failMass (failSet prepared.1))
    fun known hk => hsample parameterOutput fixed highs remaining prepared hprepared known hk) ?_
  refine add_le_add le_rfl (mul_le_mul_right ?_ _)
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- **Small budgets, deterministic signer.** -/
theorem det_smallF (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 256)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Det.forgeAdvantageDet adversary ≤
      smallMainFF ρ q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) + smallFailF q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) (add_le_add ?_ le_rfl)
  refine le_trans (small_seedFree_boundF hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q hq ρ hN
    κ hκ0 hκ1 hκ b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr) ?_
  rw [add_right_comm]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_right expectedFail_le _)) le_rfl

end Close

/-! ### The rational check -/

/-- The rational small-route check at the right end `qh` of the small budgets: the coin term is
`(2 M − 1) qh / (M 2^129)` with `M = 2^(26 − b)` (the creation rate of the scan signer), the near term
is multiplied by `κ = 2 - ρ + qh / 2^128 + N · 123 / (2^b 2^15)`. -/
def checkSmallF (b N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) * 123 / (2 ^ b * 2 ^ 15) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (2 * (H0.scanMb b : ℚ) - 1) * (qh : ℚ) / ((H0.scanMb b : ℚ) * 2 ^ 129) +
      (2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15)) * qh * c + 1 / 2 ^ 60 ≤ 2)

omit [Params] in
theorem checkSmallF_sound {b N qh : ℕ} {ρ cthr B c : ℚ} (h : checkSmallF b N qh ρ cthr B c = true) :
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) ≤ (ρ : ℝ) - 1 - (qh : ℝ) / 2 ^ 128 ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanMb b : ℝ) - 1) * (qh : ℝ) / ((H0.scanMb b : ℝ) * 2 ^ 129) +
        (2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) * 123 / (2 ^ b * 2 ^ 15)) * qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
  simp only [checkSmallF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have r1 := (Rat.cast_le (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have r4 := (Rat.cast_le (K := ℝ)).mpr h4
  have r5 := (Rat.cast_le (K := ℝ)).mpr h5
  have r8 := (Rat.cast_le (K := ℝ)).mpr h8
  have r11 := (Rat.cast_le (K := ℝ)).mpr h11
  have r12 := (Rat.cast_le (K := ℝ)).mpr h12
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at r1 r2 r3 r4 r5 r8 r11 r12
  exact ⟨⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, r11, r12⟩

/-! ### A chain of covers -/

/-- A chain of covers of the large budgets: `qstart` is one past the last covered budget, each cover
is checked from there to its own `qtop`, and the chain ends once every budget `q'` with
`q' + keygenCost < 2^127` is covered. -/
def checkCovers (b N : ℕ) : ℕ → List H0.CoverW → Bool
  | qstart, [] => decide (2 ^ 127 ≤ qstart + (226 * 2 ^ b + 2 * (26 - b)))
  | qstart, c :: rest => H0.checkCoverW b N qstart c && checkCovers b N (c.qtop + 1) rest

omit [Params] in
/-- Every budget from `qstart` on with `q' + keygenCost < 2^127` lies in a checked cover of the chain. -/
theorem checkCovers_sound (b N : ℕ) : ∀ (covers : List H0.CoverW) (qstart : ℕ),
    checkCovers b N qstart covers = true → ∀ q', qstart ≤ q' → q' + (226 * 2 ^ b + 2 * (26 - b)) < 2 ^ 127 →
      ∃ c ∈ covers, ∃ qs, H0.checkCoverW b N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop
  | [], qstart, h, q', h0, h1 => by
      simp only [checkCovers, decide_eq_true_eq] at h
      omega
  | c :: rest, qstart, h, q', h0, h1 => by
      simp only [checkCovers, Bool.and_eq_true] at h
      by_cases hq : q' ≤ c.qtop
      · exact ⟨c, List.mem_cons_self .., qstart, h.1, h0, hq⟩
      · obtain ⟨c', hc', hrest⟩ := checkCovers_sound b N rest (c.qtop + 1) h.2 q' (by omega) h1
        exact ⟨c', List.mem_cons_of_mem _ hc', hrest⟩

/-! ### Both routes -/

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer of the forest**, from the small-route check at `qh` (with
a table whose rate is checked at `qh`) and a checked chain of covers of the large budgets from
`qh + 1` up to `2^127 − 1 − keygenCost`. -/
theorem det_bitsF (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate b N qh t = true) (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true)
    (hsmall : checkSmallF b N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (covers : List H0.CoverW) (hcov : checkCovers b N (qh + 1) covers = true) :
    Det.HasClassicalSecurityBitsDet 127 := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallF_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set c : ℚ := (2 ^ b * on.En : ℚ) / 2 with hcdef
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by
      rw [hκR]
      linarith
    exact_mod_cast hR
  have hc2 : (0 : ℚ) ≤ κ * c := mul_nonneg hκ0 hc
  have hcheck' : (ρ : ℝ) + 2 ^ 128 * (o.B : ℝ) +
      (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
      qh * ((κ * c : ℚ) : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
    rw [Rat.cast_mul, hκR, ← H0.scanMb_eq b hb]
    refine le_of_eq_of_le ?_ hcheck
    ring
  have hkg : keygenCost = 226 * 2 ^ b + 2 * (26 - b) := by rw [← hb]; rfl
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_monoF hnum hx (by positivity)
    have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
        (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ) := by
      have he : (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) =
          (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
        rw [hb, hN]
        field_simp
      rw [hκR, he]
      linarith
    refine le_trans (det_smallF hb0 adversary q hbound (by omega) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq b N hb hN t o on
      hpt qh hrt hs ho hon hcthr) ?_
    exact small_closeFF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'
  · have hK : keygenCost ≤ q := by omega
    obtain ⟨cover, -, qs, hcv, hqs, hqt⟩ := checkCovers_sound b N covers (qh + 1) hcov (q - keygenCost)
      (by omega) (by rw [← hkg]; omega)
    have hcovb := H0.h0W_bound_of_cover b N qs cover hcv hb hN (q - keygenCost) hqs hqt
    have hfairq := H0.fair_of_cover b N qs cover hcv hb (q - keygenCost) hqt
    have h := det_largeW hb0 hN70' adversary q hbound hq127 hK hfairq (by
      have e1 : (q - keygenCost) + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) = q - keygenCost + keygenCost :=
        rfl
      rw [e1] at hcovb
      exact hcovb)
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]

end Sphincs.Security.ForsPotential
