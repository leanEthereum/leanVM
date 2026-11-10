module

public import Qrom.Sphincs.HidingStep
public import Qrom.Sphincs.Bound.BadEnc
public import Qrom.Sphincs.Bound.Cover

@[expose] public section

/-!
# leanSPHINCS in the QROM

An adversary given the public key, making at most `n` calls in all (hash queries, quantum or
classical, and signing queries), forges with probability at most
`(√ε_hid + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`, where `ε_hid` is the weight of a win in the
hidden game: a protected read, a hit, an encoding collision of the data, or a covered digest
(`Qrom.Sphincs.winProb_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The search factor of an adversary making at most `n` calls. -/
def searchK (n : ℕ) : ℝ := (√6 * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2

/-- The probability bound of an encoding collision of the data. -/
def badB : ℝ := 2 ^ totalHeight * numLayers * 2 ^ counterBits * (2 : ℝ)⁻¹ ^ 128

/-- **The weight of a win in the hidden game.** -/
def epsHid (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) +
    ENNReal.ofReal badB + lamCov * ENNReal.ofReal (searchK n)) * ENNReal.ofReal t

theorem sum_inv_card (α : Type) [Fintype α] [Nonempty α] : ∑ _ : α, (Fintype.card α : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (card_ne_zero_enn _) (ENNReal.natCast_ne_top _)]

open Classical in
theorem avg_hid_le {A : QReg} (adv : Adversary A) {n : ℕ} (hadv : ∀ pk, (adv pk).IsTotalQueryBound n)
    (ρ : SubState A) :
    OvGame.avgSide hidGame .instruments (gameProg adv) ρ (fun _ _ p s ↦ win p.2.2 s) ≤
      epsHid n ρ.matrix.trace.re := by
  set cD := (Fintype.card Data : ℝ≥0∞)
  set cG := (Fintype.card (Input → HashOutput) : ℝ≥0∞)
  set T := ENNReal.ofReal ρ.matrix.trace.re
  have hinv : (cD * cG)⁻¹ = cD⁻¹ * cG⁻¹ :=
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))
  have hD : cD⁻¹ * cD = 1 := ENNReal.inv_mul_cancel (card_ne_zero_enn _) (ENNReal.natCast_ne_top _)
  set T1 := fun d G ↦ OvGame.sideW (hidGame d) G .instruments (gameProg adv) ρ
    (fun p s ↦ evProt d s p.2.2.2)
  set T2 := fun d G ↦ OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
    evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2)))
  set T3 := fun d G ↦ if evBad d then OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ
    (fun _ _ ↦ true) else 0
  set T4 := fun d G ↦ OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ
    (fun p s ↦ evCov d s G p.2.2.2)
  have hsplit : OvGame.avgSide hidGame .instruments (gameProg adv) ρ (fun _ _ p s ↦ win p.2.2 s) ≤
      ∑ d, ∑ G, (cD * cG)⁻¹ * T1 d G + ∑ d, ∑ G, (cD * cG)⁻¹ * T2 d G +
        (∑ d, ∑ G, (cD * cG)⁻¹ * T3 d G + ∑ d, ∑ G, (cD * cG)⁻¹ * T4 d G) := by
    unfold OvGame.avgSide
    simp only [← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun d _ ↦ Finset.sum_le_sum fun G _ ↦
      mul_le_mul_right (sideW_win_le d G adv ρ) _
  refine hsplit.trans ?_
  -- protected reads
  have h1 : ∑ d, ∑ G, (cD * cG)⁻¹ * T1 d G ≤ ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * T := by
    calc ∑ d, ∑ G, (cD * cG)⁻¹ * T1 d G = ∑ G, cG⁻¹ * (cD⁻¹ * ∑ d, T1 d G) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun G _ ↦ ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [hinv]; ring
      _ ≤ ∑ G : Input → HashOutput, cG⁻¹ * (cD⁻¹ *
            (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * (cD * T))) :=
          Finset.sum_le_sum fun G _ ↦ mul_le_mul_right (mul_le_mul_right (sum_prot_le G adv ρ) _) _
      _ = ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * T := by
          rw [← Finset.sum_mul, sum_inv_card, one_mul]
          calc cD⁻¹ * (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * (cD * T)) =
              (cD⁻¹ * cD) * (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * T) := by ring
            _ = _ := by rw [hD, one_mul]
  -- hits
  have h2 : ∑ d, ∑ G, (cD * cG)⁻¹ * T2 d G ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) * T := by
    calc ∑ d, ∑ G, (cD * cG)⁻¹ * T2 d G = ∑ d, cD⁻¹ * ∑ G, cG⁻¹ * T2 d G := by
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun G _ ↦ ?_
          rw [hinv]; ring
      _ ≤ ∑ _d : Data, cD⁻¹ * (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) * T) :=
          Finset.sum_le_sum fun d _ ↦ mul_le_mul_right (sum_hit_le d adv hadv ρ) _
      _ = _ := by rw [← Finset.sum_mul, sum_inv_card, one_mul]
  -- encoding collisions
  have h3 : ∑ d, ∑ G, (cD * cG)⁻¹ * T3 d G ≤ ENNReal.ofReal badB * T := by
    have hT3 : ∀ d G, T3 d G ≤ if evBad d then T else 0 := fun d G ↦ by
      simp only [T3]
      split_ifs
      · exact OvGame.sideW_true_le _ G _ _ ρ
      · exact le_rfl
    calc ∑ d, ∑ G, (cD * cG)⁻¹ * T3 d G ≤ ∑ d, ∑ _G : Input → HashOutput,
          (cD * cG)⁻¹ * (if evBad d then T else 0) :=
          Finset.sum_le_sum fun d _ ↦ Finset.sum_le_sum fun G _ ↦ mul_le_mul_right (hT3 d G) _
      _ = ∑ d, cD⁻¹ * (if evBad d then T else 0) := by
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          simp only [hinv]
          rw [← Finset.sum_mul, ← Finset.mul_sum, sum_inv_card, mul_one]
      _ = cD⁻¹ * ((Finset.univ.filter BadEnc).card * T) := by
          rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul]
          congr 3
      _ ≤ ENNReal.ofReal badB * T := by
          have hc := card_badEnc_le
          have hc' : ((Finset.univ.filter BadEnc).card : ℝ≥0∞) ≤ ENNReal.ofReal badB * cD := by
            rw [← ENNReal.ofReal_natCast, show cD = ENNReal.ofReal (Fintype.card Data) from
              (ENNReal.ofReal_natCast _).symm, ← ENNReal.ofReal_mul (by unfold badB; positivity)]
            exact ENNReal.ofReal_le_ofReal hc
          calc cD⁻¹ * ((Finset.univ.filter BadEnc).card * T) ≤ cD⁻¹ * (ENNReal.ofReal badB * cD * T) :=
                mul_le_mul_right (mul_le_mul_left hc' _) _
            _ = (cD⁻¹ * cD) * (ENNReal.ofReal badB * T) := by ring
            _ = _ := by rw [hD, one_mul]
  -- covered digests
  have h4 := avg_cov_le adv hadv ρ
  calc _ ≤ ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) * T +
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) * T +
        (ENNReal.ofReal badB * T + lamCov * ENNReal.ofReal (searchK n) * T) :=
        add_le_add (add_le_add h1 h2) (add_le_add h3 h4)
    _ = epsHid n ρ.matrix.trace.re := by unfold epsHid; ring

/-- **leanSPHINCS is secure in the QROM.** An adversary from the register `A` in the state `ρ`,
making at most `n` calls in all, forges with probability at most
`(√ε_hid + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`. -/
theorem winProb_le {A : QReg} (adv : Adversary A) {n : ℕ} (hadv : ∀ pk, (adv pk).IsTotalQueryBound n)
    (ρ : SubState A) :
    winProb adv ρ ≤ (epsHid n ρ.matrix.trace.re ^ (2⁻¹ : ℝ) + ((1 + n + verifyQueries : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hb : (gameProg adv).IsTotalQueryBound (1 + n + verifyQueries) :=
    OvGame.isTotalQueryBound_withVerifier (isTotalQueryBound_withKey hadv) isTotalQueryBound_verifier
  have hh := hiding_step (gameProg adv) (1 + n + verifyQueries) hb ρ (fun _ _ p s ↦ win p.2.2 s)
  rw [← winProb_eq] at hh
  have hle : winProb adv ρ ^ (2⁻¹ : ℝ) ≤ epsHid n ρ.matrix.trace.re ^ (2⁻¹ : ℝ) +
      ((1 + n + verifyQueries : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
    hh.trans (add_le_add_left (ENNReal.rpow_le_rpow (avg_hid_le adv hadv ρ) (by norm_num)) _)
  have hsq : winProb adv ρ = (winProb adv ρ ^ (2⁻¹ : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hsq]
  exact pow_le_pow_left₀ bot_le hle 2

end Qrom.Sphincs
