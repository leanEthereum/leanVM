module

public import Quantum.StdModel.Xmss.PropsIn
public import Quantum.StdModel.Xmss.Costs
public import Quantum.StdModel.Qrom.XmssInst
public import Quantum.Qrom.Xmss.BoundValue

@[expose] public section

/-!
# leanXMSS in the QROM from the four properties

Theorem 1 with SM-TCR-C restricted to in-kind targets (`xmss_suf_le_props_in`) holds at every
table of `romWorld`; the QROM winning probability is the average over the tables
(`winProb_qrom_eq_avg`), so it is at most the averaged property terms (`winProb_xmssRom_le_avg`):
the averaged KIM-PRF advantage of B1, and the QROM successes of B2, B3 and B4.
-/

open IPFunctor OracleComp OracleSpec HashSig LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

/-! ## Averaging Theorem 1 -/

theorem probAt_ne_top (W : OracleWorld) (tab : W.Tab)
    (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) : W.probAt tab x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probAt_le_one W tab x)

theorem inv_card_tab_ne_top (W : OracleWorld) : (Fintype.card W.Tab : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)

/-- **The probability over a uniform table, as a real**, is the average of the fixed-table
probabilities. -/
theorem toReal_probAvg (W : OracleWorld) (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    (W.probAvg x).toReal =
      ∑ tab, ((Fintype.card W.Tab : ℝ≥0∞)⁻¹).toReal * (W.probAt tab x).toReal := by
  rw [OracleWorld.probAvg_eq_sum, ENNReal.toReal_sum fun tab _ ↦
    ENNReal.mul_ne_top (inv_card_tab_ne_top W) (probAt_ne_top W tab x)]
  exact Finset.sum_congr rfl fun _ _ ↦ ENNReal.toReal_mul

theorem winProbAt_ne_top (W : OracleWorld)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) (tab : W.Tab) :
    winProbAt W (xmssScheme W) tab A ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.mul_ne_top (prEvent_ne_top _) (probAt_ne_top W tab _)

/-- **Theorem 1 averaged over the QROM tables**: the QROM winning probability of a leanXMSS
adversary is at most the averaged KIM-PRF advantage of B1 plus the QROM successes of B2, B3
and B4, each reduction running the relabelled adversary `ofQrom A`. -/
theorem winProb_xmssRom_le_avg (A : Qrom.Xmss.Adversary) :
    (Qrom.SufCma.winProb Qrom.Xmss.xmssRom A).toReal ≤
      ((romWorld.probAvg ((prfReal romWorld
          (derivedKimFn romWorld seedTag prfSeedBytes prfKey prfFmt prfTrunc)).game
            (prfRed romWorld (ofQrom A)))).toReal -
        (romWorld.probAvg ((prfIdeal romWorld prfTrunc).game
          (prfRed romWorld (ofQrom A)))).toReal) +
        (romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
          (encRed romWorld (ofQrom A)))).toReal +
        (romWorld.probAvg ((cpre romWorld xmssChains noEval).game
          (cpreRed romWorld (ofQrom A)))).toReal +
        (romWorld.probAvg ((smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind).game
          (tcrRed romWorld (ofQrom A)))).toReal := by
  have h : Qrom.SufCma.winProb Qrom.Xmss.xmssRom A =
      ∑ H, (Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹ *
        winProbAt romWorld (xmssScheme romWorld) H (ofQrom A) :=
    winProb_qrom_eq_avg _ A
  rw [h, ENNReal.toReal_sum fun H _ ↦
    ENNReal.mul_ne_top (inv_card_tab_ne_top romWorld) (winProbAt_ne_top romWorld (ofQrom A) H)]
  calc ∑ H, ((Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹ *
          winProbAt romWorld (xmssScheme romWorld) H (ofQrom A)).toReal
      ≤ ∑ H, ((Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹).toReal *
          (xmssPrfAdv romWorld H (prfRed romWorld (ofQrom A)) +
            (encTcrSaltSucc romWorld xmssEnc H (encRed romWorld (ofQrom A))).toReal +
            (cpreSucc romWorld xmssChains noEval H (cpreRed romWorld (ofQrom A))).toReal +
            (smTcrInSucc romWorld xmssTcrC xmssTcrD TcrInKind H
              (tcrRed romWorld (ofQrom A))).toReal) :=
        Finset.sum_le_sum fun H _ ↦ by
          rw [ENNReal.toReal_mul]
          exact mul_le_mul_of_nonneg_left
            (xmss_suf_le_props_in romWorld romWorld_coinsFair H (ofQrom A))
            ENNReal.toReal_nonneg
    _ = _ := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          toReal_probAvg, xmssPrfAdv, derivedKimPrfAdv, prfAdv, Experiment.succAt]

/-! ## The relabelled adversary's budgets -/

theorem isChargeBound_ofQrom_hash {A : Qrom.Xmss.Adversary} {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (pk : PublicKey) : IFreeM.IsChargeBound (ofQrom A pk) (cmdCharge hashCharge) q :=
  isChargeBound_ofQrom A hashCharge pk (by rw [hashCharge_comp_qromPort]; exact hq pk)

theorem isChargeBound_ofQrom_call {A : Qrom.Xmss.Adversary} {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    (pk : PublicKey) : IFreeM.IsChargeBound (ofQrom A pk) (cmdCharge callCharge) m :=
  isChargeBound_ofQrom A callCharge pk (by rw [callCharge_comp_qromPort]; exact hm pk)

/-- The requests of leaf `ℓ` on the generic ports: one per request of `ℓ`. -/
def worldLeafCharge (ℓ : LeafIndex) : Port Unit SigningRequest → ℕ
  | .hash _ => 0
  | .call r => if r.leafIndex = ℓ then 1 else 0

theorem worldLeafCharge_comp_qromPort (ℓ : LeafIndex) :
    worldLeafCharge ℓ ∘ qromPort = Qrom.Xmss.leafCharge ℓ :=
  funext fun i ↦ by cases i <;> rfl

/-- **No leaf reuse, relabelled**: on every path of `ofQrom (refuse A)` each leaf is requested
at most once. -/
theorem isChargeBound_ofQrom_refuse_leaf (A : Qrom.Xmss.Adversary) (pk : PublicKey)
    (ℓ : LeafIndex) :
    IFreeM.IsChargeBound (ofQrom (Qrom.Xmss.refuse A) pk) (cmdCharge (worldLeafCharge ℓ)) 1 :=
  isChargeBound_ofQrom _ _ pk (by
    rw [worldLeafCharge_comp_qromPort]
    exact Qrom.Xmss.noLeafReuse_refuse A pk ℓ)

/-! ## B1: KIM-PRF -/

/-- **B1's averaged KIM-PRF advantage**: for an adversary with `q` hash calls and `m` signing
requests, B1 makes `q + 8624537563 m + 11534719` hash calls (`isChargeBound_prfRed_rom`), so its
advantage is at most `4 (q + 8624537563 m + 11534719) √(2 / 2^256)`. -/
theorem abs_avg_prfRed_le (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m) :
    |(romWorld.probAvg ((prfReal romWorld
          (derivedKimFn romWorld seedTag prfSeedBytes prfKey prfFmt prfTrunc)).game
            (prfRed romWorld (ofQrom A)))).toReal -
        (romWorld.probAvg ((prfIdeal romWorld prfTrunc).game
          (prfRed romWorld (ofQrom A)))).toReal| ≤
      4 * ((q + 8624537563 * m + 11534719 : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256) := by
  refine le_of_eq_of_le ?_ (abs_avg_xmssPrfAdv_le (prfRed romWorld (ofQrom A))
    (isChargeBound_prfRed_rom (ofQrom A) (isChargeBound_ofQrom_hash hq)
      (isChargeBound_ofQrom_call hm)))
  rw [toReal_probAvg, toReal_probAvg, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, xmssPrfAdv, derivedKimPrfAdv, prfAdv, Experiment.succAt,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-! ## The combination -/

theorem probAvg_ne_top (W : OracleWorld) (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAvg x ≠ ⊤ := by
  rw [OracleWorld.probAvg_eq_sum]
  exact ENNReal.sum_ne_top.mpr fun tab _ ↦
    ENNReal.mul_ne_top (inv_card_tab_ne_top W) (probAt_ne_top W tab x)

/-- **The QROM win from the property bounds**: if the QROM successes of B2, B3 and B4 against
`A` are at most `e`, `c` and `t`, then `A` wins with probability at most
`4 (q + 8624537563 m + 11534719) √(2 / 2^256) + e + c + t`. -/
theorem winProb_xmssRom_le_of (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    {e c t : ℝ≥0∞}
    (he : romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game (encRed romWorld (ofQrom A))) ≤ e)
    (hc : romWorld.probAvg ((cpre romWorld xmssChains noEval).game
      (cpreRed romWorld (ofQrom A))) ≤ c)
    (ht : romWorld.probAvg ((smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind).game
      (tcrRed romWorld (ofQrom A))) ≤ t) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      ENNReal.ofReal (4 * ((q + 8624537563 * m + 11534719 : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256)) +
        e + c + t := by
  have hw : Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≠ ⊤ := by
    rw [winProb_qrom_eq_avg]
    exact ENNReal.sum_ne_top.mpr fun H _ ↦ ENNReal.mul_ne_top (inv_card_tab_ne_top romWorld)
      (winProbAt_ne_top romWorld (ofQrom A) H)
  have hr := (winProb_xmssRom_le_avg A).trans (add_le_add (add_le_add (add_le_add
    ((le_abs_self _).trans (abs_avg_prfRed_le A hq hm)) le_rfl) le_rfl) le_rfl)
  rw [← ENNReal.ofReal_toReal hw]
  refine (ENNReal.ofReal_le_ofReal hr).trans ?_
  rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (probAvg_ne_top _ _), ENNReal.ofReal_toReal (probAvg_ne_top _ _),
    ENNReal.ofReal_toReal (probAvg_ne_top _ _)]
  gcongr

/-- **The combination through no leaf reuse**: `A` wins at most as often as `refuse A`
(`winProb_le_winProb_refuse`), which keeps `A`'s budgets and requests every leaf at most once;
the property bounds are then needed only for the reductions run on `refuse A`. -/
theorem winProb_xmssRom_le_of_refuse (A : Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge Qrom.SufCma.signCharge) m)
    {e c t : ℝ≥0∞}
    (he : romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
      (encRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤ e)
    (hc : romWorld.probAvg ((cpre romWorld xmssChains noEval).game
      (cpreRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤ c)
    (ht : romWorld.probAvg ((smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind).game
      (tcrRed romWorld (ofQrom (Qrom.Xmss.refuse A)))) ≤ t) :
    Qrom.SufCma.winProb Qrom.Xmss.xmssRom A ≤
      ENNReal.ofReal (4 * ((q + 8624537563 * m + 11534719 : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256)) +
        e + c + t :=
  (Qrom.Xmss.winProb_le_winProb_refuse A).trans (winProb_xmssRom_le_of (Qrom.Xmss.refuse A)
    (fun pk ↦ Qrom.Xmss.isChargeBound_refuse (hq pk))
    (fun pk ↦ Qrom.Xmss.isChargeBound_refuse (hm pk)) he hc ht)

/-! ## The KIM-PRF term in closed form -/

/-- **B1's term at most `lifetime` requests**: `4 (q + 8624537563 m + 11534719) √(2 / 2^256) ≤
(6 q + 2^68) / 2^128`. -/
theorem prfTerm_le (q : ℕ) {m : ℕ} (hm : m ≤ 2 ^ 32) :
    4 * ((q + 8624537563 * m + 11534719 : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256) ≤
      (6 * q + 2 ^ 68) / 2 ^ 128 := by
  have hs : Real.sqrt (2 / 2 ^ 256) ≤ 1.5 / 2 ^ 128 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by norm_num⟩
  have hm' : (m : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  calc 4 * ((q : ℝ) + 8624537563 * m + 11534719) * Real.sqrt (2 / 2 ^ 256)
      ≤ 4 * ((q : ℝ) + 8624537563 * 2 ^ 32 + 11534719) * (1.5 / 2 ^ 128) := by gcongr
    _ ≤ (6 * q + 2 ^ 68) / 2 ^ 128 := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      norm_num
      linarith

end Quantum.StdModel.Xmss

end
