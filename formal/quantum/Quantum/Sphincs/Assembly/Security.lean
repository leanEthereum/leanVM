module

public import Quantum.Sphincs.Assembly.ChgRevAvg
public import Quantum.Sphincs.Assembly.HStaticFrac
public import Quantum.Sphincs.Game

@[expose] public section

/-!
# leanSPHINCS is quantum SUF-CMA secure in the QRPM

The assembly of the chain (`Quantum.Sphincs.Hybrid.Masked`'s `winProb_le_masked`): G0 is runtime 1
with the full table, the masked graded hybrid against runtime 2 on the canonical game at `msgPol`
with the masses masked by `FullG (SrcS SphStatic)` (Masses' `hcov_sph`, HmsgCoversMass' `hS_sph'`,
`hRd_sph'`), the table average of runtime 2 moved to the template data (the win's mismatch term
`winChgAvg`) and the event side over `FullES` (`eventTermS q cfEps`, `2 goodESCap`, `2^-777`). The
bad fraction of the mask is `stageFrac (SrcS SphStatic) ≤ 2^-197 + 2^-400 + 2^-277 + staticFrac`
(GoodTables).

* **The mismatch terms and the static fraction**: the masses' `chgRevAvg ≤ 2^-200`
  (ChgRevAvg's `chgRevAvg_le_cap`), the win's `winChgAvg ≤ 2^-90` (`winChgAvg_le_cap`) and
  `staticFrac ≤ 2^-127` (HStaticFrac's `staticFrac_le`).
* **The bound** (`sphincsQrpmBound q = (√eventTermSph q + hybTermS q kappaSph readCapS)² +
  stageCap`) with `eventTermSph q = eventTermS q cfEps + 2 goodESCap + 2^-777 + 2^-90 + stageCap`,
  `kappaSph = 2^-128 + kkEps + kappaH + 2^-200`, `readCapS = trialTau (2 clsCap) + 2^-128 · 3
  verifyBlocks + clsCap (kkEps + kappaH + 2^-200)` and `stageCap = 2^-197 + 2^-400 + 2^-277 +
  2^-127`. For `q > 2^64` the bound is at least `1` (`one_le_sphincsQrpmBound`).
* **The theorems**: `winProb_le_sphincsQrpmBound` (one adversary, `q ≤ 2^64`) and
  `leanSphincs_qrpm_security : LeanSphincsQrpmSecurity sphincsQrpmBound`.
-/

open IPFunctor
open scoped ENNReal

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common Common.SufCma
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtimeR)
open Quantum.Sphincs.Hybrid (uavg_le_one_of_le)

namespace Quantum.Sphincs.Assembly

/-! ## The constants and the bound -/

section bound

/-- The bound on the masses' mismatch term `chgRevAvg`: `2^-200`. -/
noncomputable def chgRevCap : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 200)

/-- The bound on the win's mismatch term `winChgAvg`: `2^-90`. -/
noncomputable def winChgCap : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 90)

/-- The bound on the masked hybrid's bad fraction: ReparamFull's `2^-197 + 2^-400`, SrcBad's
`2^-277` and the static fraction's `2^-127`. -/
noncomputable def stageCap : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 ^ 197) + ENNReal.ofReal (1 / 2 ^ 400) + ENNReal.ofReal (1 / 2 ^ 277) +
    ENNReal.ofReal (1 / 2 ^ 127)

/-- The masked hidden mass per sponge call (`hS_sph'`): `2^-128 + kkEps + kappaH + chgRevCap`. -/
noncomputable def kappaSph : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + kkEps + kappaH + chgRevCap

/-- The masked hidden mass at the read ports (`hRd_sph'`): `trialTau (2 clsCap) + 2^-128 · 3
verifyBlocks + clsCap (kkEps + kappaH + chgRevCap)`. -/
noncomputable def readCapS : ℝ≥0∞ :=
  trialTau (2 * clsCap) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
    clsCap * kkEps + clsCap * kappaH + clsCap * chgRevCap

/-- The bound on runtime 2's table average: the event side, the bad permutations, the win's
mismatch term and the bad fraction. -/
noncomputable def eventTermSph (q : ℕ) : ℝ≥0∞ :=
  eventTermS q cfEps + 2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) + winChgCap + stageCap

/-- **The leanSPHINCS QRPM bound**: `(√eventTermSph q + hybTermS q kappaSph readCapS)² +
stageCap`. -/
noncomputable def sphincsQrpmBound (q : ℕ) : ℝ≥0∞ :=
  (eventTermSph q ^ (2⁻¹ : ℝ) + hybTermS q kappaSph readCapS) ^ 2 + stageCap

end bound

/-! ## The proof -/

section proof

theorem hybTermS_mono (q : ℕ) {κ κ' ν ν' : ℝ≥0∞} (hκ : κ ≤ κ') (hν : ν ≤ ν') :
    hybTermS q κ ν ≤ hybTermS q κ' ν' := by
  unfold hybTermS
  exact add_le_add (ENNReal.rpow_le_rpow (by gcongr) (by norm_num))
    (ENNReal.rpow_le_rpow hν (by norm_num))

/-- The masked hybrid's bad fraction: at most `stageCap`. -/
theorem stageFrac_le_stageCap : stageFrac (SrcS SphStatic) ≤ stageCap :=
  stageFrac_sphStatic_le.trans (add_le_add le_rfl staticFrac_le)

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The leanSPHINCS bound for one adversary** (`winProb_le_masked` with Masses' `hcov_sph`,
HmsgCoversMass' `hS_sph'`, `hRd_sph'` at the static condition `SphStatic`, and the mismatch
terms' caps). -/
theorem winProb_le_sphincsQrpmBound (hq : q ≤ 2 ^ 64) :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A ≤ sphincsQrpmBound q := by
  have hw := winProb_le_masked hperm hsign hq (SrcS SphStatic) (fun t ↦ fullCovH (tabOf t))
    (fun t ↦ fullCovK (tabOf t)) (fun t ↦ fullCovK' (tabOf t)) hcov_sph _ _
    (hS_sph' A hperm hsign SphStatic fun _ _ h ↦ h.1)
    (hRd_sph' A hperm hsign SphStatic (fun _ _ h ↦ h.1) fun _ _ h ↦ h.2.1)
  have hst := stageFrac_le_stageCap
  have hc : chgRevAvg A initR SphStatic ≤ chgRevCap := chgRevAvg_le_cap A hsign
  have hwc : winChgAvg A (SrcS SphStatic) ≤ winChgCap := winChgAvg_le_cap A hsign
  refine hw.trans (add_le_add (pow_le_pow_left₀ zero_le (add_le_add
    (ENNReal.rpow_le_rpow ?_ (by norm_num)) (hybTermS_mono q ?_ ?_)) 2) hst)
  · unfold eventTermSph
    exact add_le_add (add_le_add le_rfl hwc) hst
  · unfold kappaSph
    exact add_le_add le_rfl hc
  · unfold readCapS
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc zero_le)

omit hperm hsign in
/-- The win probability is at most `1`. -/
theorem winProb_le_one_sph (A : SAdversary) :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A ≤ 1 := by
  rw [winProb_eq_uavg_p1R]
  exact uavg_le_one_of_le fun _ ↦ QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _

omit hperm hsign in
/-- **Above `2^64` permutation calls the bound is trivial**: the sponge-port hybrid term alone is
`√(4 · 6q · 6q κ) ≥ 12 q 2^-64 ≥ 1`. -/
theorem one_le_sphincsQrpmBound (hq : 2 ^ 64 < q) : 1 ≤ sphincsQrpmBound q := by
  have h6 : (2 : ℝ≥0∞) ^ 64 ≤ ((6 * q : ℕ) : ℝ≥0∞) := by
    have h : 2 ^ 64 ≤ 6 * q := hq.le.trans (by omega)
    exact_mod_cast h
  have hk : (2 ^ 128 : ℝ≥0∞)⁻¹ ≤ kappaSph := by
    unfold kappaSph
    exact (le_self_add.trans le_self_add).trans le_self_add
  have h1 : (1 : ℝ≥0∞) ≤ ((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaSph) :=
    calc (1 : ℝ≥0∞) = 2 ^ 64 * (2 ^ 64 * (2 ^ 128)⁻¹) := by
          rw [← mul_assoc, ← pow_add, show 64 + 64 = 128 from rfl,
            ENNReal.mul_inv_cancel (by simp) (by simp)]
      _ ≤ _ := by gcongr
  have h2 : 1 ≤ hybTermS q kappaSph readCapS := by
    unfold hybTermS
    refine le_trans ?_ le_self_add
    calc (1 : ℝ≥0∞) = 1 ^ (2⁻¹ : ℝ) := (ENNReal.one_rpow _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow (h1.trans (le_mul_of_one_le_left zero_le (by norm_num)))
          (by norm_num)
  unfold sphincsQrpmBound
  exact (one_le_pow₀ (h2.trans le_add_self)).trans le_self_add

omit hperm hsign in
/-- **leanSPHINCS is quantum SUF-CMA secure in the QRPM** with bound `sphincsQrpmBound`: an
adversary making at most `q` permutation calls and at most `signatureLimit` signing requests
forges with probability at most `sphincsQrpmBound q`; above `2^64` calls the bound is at least
`1`. -/
theorem leanSphincs_qrpm_security : LeanSphincsQrpmSecurity sphincsQrpmBound := by
  intro q A hq hs
  by_cases hle : q ≤ 2 ^ 64
  · exact winProb_le_sphincsQrpmBound hq hs hle
  · exact (winProb_le_one_sph A).trans (one_le_sphincsQrpmBound (not_le.mp hle))

end proof

end Quantum.Sphincs.Assembly

end
