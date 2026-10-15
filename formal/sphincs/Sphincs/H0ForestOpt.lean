import Sphincs.H0ForestCert
import Sphincs.H0PTab
import Sphincs.H0Fair

/-! **One option of the forest H-term certificate.** An option fixes the cap `c1`, the Chernoff
parameter `θ` and the threshold `cthr`, and carries the leaf tables `ḡ` (the excess part) and
`h̄ - 1` (the Chernoff factor), checked against the moment tables, with their Poisson means `Eg`,
`Ee` and the resulting bound `B ≥ L Eg + A (1 + Ee)^L` of the H-term. -/

open ENNReal NNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice SphincsFors.Security.H0 SphincsFors.Security.Domination H0Avg

set_option linter.unusedSectionVars false

/-- The per-index weight `2^-26` of the cover probability. -/
def κQ : ℚ := 1 / 2 ^ 26

/-- One option of the certificate. -/
structure OptF where
  c1 : ℚ
  θ : ℚ
  cthr : ℚ
  s : ℕ
  eC : ℚ
  A2 : ℚ
  gt : List ℚ
  Jg : ℚ
  ht : List ℚ
  Jh : ℚ
  Eg : ℚ
  Ee : ℚ
  B : ℚ

/-- The excess part bound at `n` from the moment tables. -/
def gBound (o : OptF) (n : ℕ) : ℚ :=
  min (κQ * P1tab.getD n 0 ^ 8) (κQ ^ 2 * P2tab.getD n 0 ^ 8 / (4 * o.c1))

/-- The Chernoff factor bound (minus one) at `n` from the moment tables. -/
def hBound (o : OptF) (n : ℕ) : ℚ :=
  min (o.eC - 1) (o.θ * κQ * P1tab.getD n 0 ^ 8 + o.A2 * κQ ^ 2 * P2tab.getD n 0 ^ 8)

/-- The check of an option against a Poisson table, for subtree height `b`. -/
def checkOptF (b : ℕ) (t : PoisT) (o : OptF) : Bool :=
  decide (0 < o.c1) && decide (0 < o.θ) && decide (0 ≤ o.cthr) && decide (o.θ * o.c1 < 2 ^ o.s) &&
    decide (expUp (o.θ * o.c1) o.s t.P ≤ o.eC) &&
    decide ((o.eC - 1 - o.θ * o.c1) / o.c1 ^ 2 ≤ o.A2) &&
    decide (t.n1 ≤ 150) && decide (o.gt.length = t.n1 + 1) && decide (o.ht.length = t.n1 + 1) &&
    checkLeaf o.gt o.Jg && checkLeaf o.ht o.Jh &&
    decide (∀ n < t.n1 + 1, gBound o n ≤ o.gt.getD n 0) &&
    decide (∀ n < t.n1 + 1, hBound o n ≤ o.ht.getD n 0) &&
    decide (κQ ≤ o.gt.getD t.n1 0 + o.Jg) && decide (o.eC - 1 ≤ o.ht.getD t.n1 0 + o.Jh) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.gt.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.gt.getD t.n1 0 / (1 - t.r) + o.Jg / (1 - t.r) ^ 2)) ≤ o.Eg) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.ht.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.ht.getD t.n1 0 / (1 - t.r) + o.Jh / (1 - t.r) ^ 2)) ≤ o.Ee) &&
    decide (2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B) &&
    decide (0 ≤ o.Eg) && decide (0 ≤ o.Ee)


theorem checkOptF_parts {b : ℕ} {t : PoisT} {o : OptF} (h : checkOptF b t o = true) :
    0 < o.c1 ∧ 0 < o.θ ∧ 0 ≤ o.cthr ∧ o.θ * o.c1 < 2 ^ o.s ∧ expUp (o.θ * o.c1) o.s t.P ≤ o.eC ∧
      (o.eC - 1 - o.θ * o.c1) / o.c1 ^ 2 ≤ o.A2 ∧ t.n1 ≤ 150 ∧ o.gt.length = t.n1 + 1 ∧ o.ht.length = t.n1 + 1 ∧
      checkLeaf o.gt o.Jg = true ∧ checkLeaf o.ht o.Jh = true ∧
      (∀ n < t.n1 + 1, gBound o n ≤ o.gt.getD n 0) ∧ (∀ n < t.n1 + 1, hBound o n ≤ o.ht.getD n 0) ∧
      κQ ≤ o.gt.getD t.n1 0 + o.Jg ∧ o.eC - 1 ≤ o.ht.getD t.n1 0 + o.Jh ∧
      (((List.range (t.n1 + 1)).map fun n => t.pb n * o.gt.getD n 0).sum +
        t.pb (t.n1 + 1) * (o.gt.getD t.n1 0 / (1 - t.r) + o.Jg / (1 - t.r) ^ 2)) ≤ o.Eg ∧
      (((List.range (t.n1 + 1)).map fun n => t.pb n * o.ht.getD n 0).sum +
        t.pb (t.n1 + 1) * (o.ht.getD t.n1 0 / (1 - t.r) + o.Jh / (1 - t.r) ^ 2)) ≤ o.Ee ∧
      2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B ∧
      0 ≤ o.Eg ∧ 0 ≤ o.Ee := by
  simp only [checkOptF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩,
    h17⟩, h18⟩, h19⟩, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

theorem leafQ_of_lt {tab : List ℚ} {J : ℚ} {n : ℕ} (h : n < tab.length) : leafQ tab J n = tab.getD n 0 := by
  unfold leafQ; rw [if_pos h]

theorem leafQ_ge_end {tab : List ℚ} {J : ℚ} (hl : checkLeaf tab J = true) {n : ℕ} (hn : tab.length ≤ n) :
    tab.getD (tab.length - 1) 0 + J ≤ leafQ tab J n := by
  obtain ⟨h2, -⟩ := checkLeaf_parts hl
  have hm := leafQ_mono hl hn
  have he : leafQ tab J tab.length = tab.getD (tab.length - 1) 0 + J := by
    unfold leafQ
    rw [if_neg (lt_irrefl _), show tab.length - (tab.length - 1) = 1 by omega]
    push_cast
    ring
  rw [he] at hm
  exact hm

theorem SepGood.one_add {g : ℕ → ℝ≥0∞} (hg : SepGood g) : SepGood (fun n => 1 + g n) where
  mono := fun a b hab => add_le_add le_rfl (hg.mono hab)
  convex := fun n => by
    have := hg.convex n
    calc 1 + g (n + 1) + (1 + g (n + 1)) = (1 + 1) + (g (n + 1) + g (n + 1)) := by ring
      _ ≤ (1 + 1) + (g (n + 2) + g n) := add_le_add le_rfl this
      _ = _ := by ring
  growth := by
    obtain ⟨C, hC⟩ := hg.growth
    refine ⟨1 + C, fun n => ?_⟩
    have h1 : (1 : ℝ≥0∞) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc 1 + g n ≤ 2 ^ n + C * 2 ^ n := add_le_add h1 (hC n)
      _ = _ := by push_cast; ring

theorem poisMean_one_add (μ : ℝ≥0) (g : ℕ → ℝ≥0∞) : poisMean μ (fun n => 1 + g n) = 1 + poisMean μ g := by
  unfold poisMean
  simp only [mul_add, mul_one, ENNReal.tsum_add, poisW_tsum]

variable [Params]

theorem κE_toReal (b : ℕ) (hb : subtreeHeight = b) : κE.toReal = (κQ : ℝ) := by
  unfold κE κQ
  rw [landing_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin]
  have hb26 : b ≤ 26 := hb ▸ subtree_le_26
  rw [hb]
  have h26 : (2 : ℝ) ^ 26 = 2 ^ (26 - b) * 2 ^ b := by rw [← pow_add]; congr 1; omega
  push_cast
  rw [h26]
  field_simp

/-- **The excess part is dominated by the `ḡ` table.** -/
theorem avgN_gS_le {b : ℕ} (hb : subtreeHeight = b) {t : PoisT} {o : OptF} (ho : checkOptF b t o = true) (n : ℕ) :
    avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ) := by
  obtain ⟨hc1, -, -, -, -, -, h150, hgl, -, hlg, -, hgb, -, hgend, -⟩ := checkOptF_parts ho
  have hc1' : (0 : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hc1
  have hκ := κE_toReal b hb
  by_cases hn : n < t.n1 + 1
  · rw [leafQ_of_lt (by omega)]
    have hP1 := Ψ1R_le_tab n (by omega)
    have hP2 := Ψ2R_le_tab n (by omega)
    have hΨ1 : 0 ≤ Ψ1R n := by
      have := avgN_φF n
      exact (avgNR_nonneg coverAvg_nonneg n 0)
    have hΨ2 : 0 ≤ Ψ2R n := avgNR_nonneg (fun X => sq_nonneg _) n 0
    have hlin : avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((κQ * P1tab.getD n 0 ^ 8 : ℚ) : ℝ) := by
      calc avgN (gS (o.c1 : ℝ)) n 0 ≤ avgN (fun Ms => ENNReal.ofReal κE.toReal * yM Ms) n 0 :=
            avgN_mono (fun Ms => gS_le_lin _ hc1' Ms) n 0
        _ = ENNReal.ofReal κE.toReal * ENNReal.ofReal (Ψ1R n) ^ 8 := by rw [avgN_const_mul, avgN_yM]
        _ ≤ _ := by
            rw [← ENNReal.ofReal_pow hΨ1, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
            apply ENNReal.ofReal_le_ofReal
            rw [hκ]
            push_cast
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΨ1 hP1 8) (by unfold κQ; positivity)
    have hsq : avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((κQ ^ 2 * P2tab.getD n 0 ^ 8 / (4 * o.c1) : ℚ) : ℝ) := by
      calc avgN (gS (o.c1 : ℝ)) n 0 ≤ avgN (fun Ms => ENNReal.ofReal (κE.toReal ^ 2 / (4 * o.c1)) * yM Ms ^ 2) n 0 :=
            avgN_mono (fun Ms => gS_le_sq _ hc1' Ms) n 0
        _ = ENNReal.ofReal (κE.toReal ^ 2 / (4 * o.c1)) * ENNReal.ofReal (Ψ2R n) ^ 8 := by
            rw [avgN_const_mul, avgN_yM_sq]
        _ ≤ _ := by
            rw [← ENNReal.ofReal_pow hΨ2, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [hκ]
            push_cast
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΨ2 hP2 8) (by unfold κQ; positivity)
    have hmin : avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((gBound o n : ℚ) : ℝ) := by
      unfold gBound
      rcases min_choice (κQ * P1tab.getD n 0 ^ 8) (κQ ^ 2 * P2tab.getD n 0 ^ 8 / (4 * o.c1)) with h | h <;>
        rw [h]
      · exact hlin
      · exact hsq
    exact le_trans hmin (ENNReal.ofReal_le_ofReal (by exact_mod_cast hgb n hn))
  · have hcap : avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal (κQ : ℝ) := by
      calc avgN (gS (o.c1 : ℝ)) n 0 ≤ avgN (fun _ => ENNReal.ofReal κE.toReal) n 0 :=
            avgN_mono (fun Ms => le_trans (gS_le_lin _ hc1' Ms)
              (mul_le_of_le_one_right' (yM_le_one Ms))) n 0
        _ = _ := by rw [avgN_const, hκ]
    refine le_trans hcap (ENNReal.ofReal_le_ofReal ?_)
    have h := leafQ_ge_end hlg (n := n) (by omega)
    rw [hgl, show t.n1 + 1 - 1 = t.n1 by omega] at h
    exact_mod_cast le_trans hgend h

theorem opt_exp_le {b : ℕ} {t : PoisT} {o : OptF} (ho : checkOptF b t o = true) :
    Real.exp ((o.θ : ℝ) * o.c1) ≤ (o.eC : ℝ) := by
  obtain ⟨hc1, hθ, -, hs, heC, -⟩ := checkOptF_parts ho
  have h := exp_le_expUp (o.θ * o.c1) o.s t.P (by positivity) hs
  have h' : ((expUp (o.θ * o.c1) o.s t.P : ℚ) : ℝ) ≤ (o.eC : ℝ) := by exact_mod_cast heC
  push_cast at h
  linarith

/-- **The Chernoff factor is dominated by `1 + h̄`.** -/
theorem avgN_hS_le {b : ℕ} (hb : subtreeHeight = b) {t : PoisT} {o : OptF} (ho : checkOptF b t o = true) (n : ℕ) :
    avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ) := by
  obtain ⟨hc1, hθ, -, hs, heC, hA2, h150, -, hhl, -, hlh, -, hhb, -, hhend, -⟩ := checkOptF_parts ho
  have hc1' : (0 : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hc1
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hκ := κE_toReal b hb
  have hexp := opt_exp_le ho
  have hκ0 : (0 : ℝ) ≤ (κQ : ℝ) := by unfold κQ; positivity
  -- the cap
  have hcap : avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal ((o.eC - 1 : ℚ) : ℝ) := by
    calc avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ avgN (fun _ => ENNReal.ofReal (Real.exp ((o.θ : ℝ) * o.c1))) n 0 :=
          avgN_mono (fun Ms => hS_le_cap _ _ hθ' Ms) n 0
      _ = ENNReal.ofReal (Real.exp ((o.θ : ℝ) * o.c1)) := avgN_const _ n 0
      _ ≤ ENNReal.ofReal (1 + ((o.eC - 1 : ℚ) : ℝ)) := ENNReal.ofReal_le_ofReal (by push_cast; linarith)
      _ = _ := by
          have : (0 : ℝ) ≤ ((o.eC - 1 : ℚ) : ℝ) := by
            have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ (o.θ : ℝ) * o.c1)
            push_cast; linarith
          rw [ENNReal.ofReal_add zero_le_one this, ENNReal.ofReal_one]
  by_cases hn : n < t.n1 + 1
  · rw [leafQ_of_lt (by omega)]
    have hP1 := Ψ1R_le_tab n (by omega)
    have hP2 := Ψ2R_le_tab n (by omega)
    have hΨ1 : 0 ≤ Ψ1R n := avgNR_nonneg coverAvg_nonneg n 0
    have hΨ2 : 0 ≤ Ψ2R n := avgNR_nonneg (fun X => sq_nonneg _) n 0
    set A2r : ℝ := (Real.exp ((o.θ : ℝ) * o.c1) - 1 - (o.θ : ℝ) * o.c1) / (o.c1 : ℝ) ^ 2 with hA2r
    have hA2r0 : 0 ≤ A2r := by
      have := Real.add_one_le_exp ((o.θ : ℝ) * o.c1)
      exact div_nonneg (by linarith) (by positivity)
    have hA2le : A2r ≤ (o.A2 : ℝ) := by
      have h' : (((o.eC - 1 - o.θ * o.c1) / o.c1 ^ 2 : ℚ) : ℝ) ≤ (o.A2 : ℝ) := by exact_mod_cast hA2
      push_cast at h'
      refine le_trans ?_ h'
      rw [hA2r]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hquad : avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤
        1 + ENNReal.ofReal ((o.θ * κQ * P1tab.getD n 0 ^ 8 + o.A2 * κQ ^ 2 * P2tab.getD n 0 ^ 8 : ℚ) : ℝ) := by
      calc avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ avgN (fun Ms => 1 + ENNReal.ofReal ((o.θ : ℝ) * κE.toReal) * yM Ms +
            ENNReal.ofReal (A2r * κE.toReal ^ 2) * yM Ms ^ 2) n 0 :=
            avgN_mono (fun Ms => hS_le_quad _ _ hc1' hθ' Ms) n 0
        _ = 1 + ENNReal.ofReal ((o.θ : ℝ) * κE.toReal) * ENNReal.ofReal (Ψ1R n) ^ 8 +
            ENNReal.ofReal (A2r * κE.toReal ^ 2) * ENNReal.ofReal (Ψ2R n) ^ 8 := by
            rw [avgN_add, avgN_add, avgN_const, avgN_const_mul, avgN_const_mul, avgN_yM, avgN_yM_sq]
        _ ≤ _ := by
            rw [add_assoc]
            refine add_le_add le_rfl ?_
            rw [← ENNReal.ofReal_pow hΨ1, ← ENNReal.ofReal_pow hΨ2, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [hκ]
            push_cast
            have h1 := pow_le_pow_left₀ hΨ1 hP1 8
            have h2 := pow_le_pow_left₀ hΨ2 hP2 8
            have hP20 : (0 : ℝ) ≤ Ψ2R n ^ 8 := by positivity
            apply add_le_add
            · rw [mul_assoc, mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hκ0) hθ'.le
            · calc A2r * (κQ : ℝ) ^ 2 * Ψ2R n ^ 8 ≤ (o.A2 : ℝ) * (κQ : ℝ) ^ 2 * Ψ2R n ^ 8 := by gcongr
                _ ≤ _ := by
                    have hA20 : (0 : ℝ) ≤ (o.A2 : ℝ) := le_trans hA2r0 hA2le
                    gcongr
    have hmin : avgN (hS (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal ((hBound o n : ℚ) : ℝ) := by
      unfold hBound
      rcases min_choice (o.eC - 1) (o.θ * κQ * P1tab.getD n 0 ^ 8 + o.A2 * κQ ^ 2 * P2tab.getD n 0 ^ 8) with h | h <;>
        rw [h]
      · exact hcap
      · exact hquad
    exact le_trans hmin (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (by exact_mod_cast hhb n hn)))
  · refine le_trans hcap (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    have h := leafQ_ge_end hlh (n := n) (by omega)
    rw [hhl, show t.n1 + 1 - 1 = t.n1 by omega] at h
    exact_mod_cast le_trans hhend h

omit [Params] in
/-- The Chernoff prefactor at a threshold. -/
theorem pref_le (θ cthr : ℚ) (J P : ℕ) (hθ : 0 < θ) (hc : 0 ≤ cthr) :
    Real.exp (-(θ : ℝ) * cthr) / (Real.exp 1 * θ) ≤ ((1 / (expLow (θ * cthr) J P * eLowQ * θ) : ℚ) : ℝ) := by
  have hθ' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hE := expLow_le (θ * cthr) J P (by positivity)
  have hE1 : (1 : ℝ) ≤ (expLow (θ * cthr) J P : ℝ) := by exact_mod_cast one_le_expLow (θ * cthr) J P (by positivity)
  have he := eLowQ_le
  have he0 : (0 : ℝ) < (eLowQ : ℝ) := by unfold eLowQ; norm_num
  push_cast at hE ⊢
  rw [neg_mul, Real.exp_neg, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [one_mul, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
  calc (expLow (θ * cthr) J P : ℝ) * eLowQ * θ ≤ Real.exp ((θ : ℝ) * cthr) * Real.exp 1 * θ := by gcongr
    _ = _ := by ring

/-- **One option bounds the forest H-term**: `H ≤ B` whenever the rate `N / 2^b + q λ w / 2^b` is
below the table rate and the base `b0` is at least the threshold `cthr`. -/
theorem hTermO_le_optF {b : ℕ} (hb : subtreeHeight = b) (t : PoisT) (o : OptF) (ht : checkPT t = true)
    (ho : checkOptF b t o = true) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ)
    (hrate : (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b ≤ (t.mu : ℝ))
    (b0 : ℝ≥0∞) (hb0 : ENNReal.ofReal (o.cthr : ℝ) ≤ b0) :
    hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0) ≤ ENNReal.ofReal (o.B : ℝ) := by
  obtain ⟨hc1, hθ, hcthr, -, -, -, -, hgl, hhl, hlg, hlh, -, -, -, -, hEg, hEe, hB, hEg0, hEe0⟩ := checkOptF_parts ho
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hlw : lam * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' hlam hw)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin, hb]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (lam * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, hγdef, hαdef]
    push_cast
    calc (N : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((lam * w).toReal / 2 ^ b)
        = (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b := by ring
      _ ≤ _ := hrate
  have hmain := hTermO_forest_le w lam hw hlam N q b0 (o.cthr : ℝ) (o.c1 : ℝ) (o.θ : ℝ) hb0 hθ'
    (fun n => ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ)) (fun n => 1 + ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ))
    (leaf_sepGood hlg) (SepGood.one_add (leaf_sepGood hlh)) (avgN_gS_le hb ho) (avgN_hS_le hb ho) α γ hα hγ μ hμ
  rw [poisMean_one_add] at hmain
  have hg := poisMean_leaf_le ht hlg hgl
  have hh := poisMean_leaf_le ht hlh hhl
  rw [← hμdef] at hg hh
  have hEg' : poisMean μ (fun n => ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ)) ≤ ENNReal.ofReal (o.Eg : ℝ) :=
    le_trans hg (ENNReal.ofReal_le_ofReal (Rat.cast_le.2 hEg))
  have hEe' : poisMean μ (fun n => ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ)) ≤ ENNReal.ofReal (o.Ee : ℝ) :=
    le_trans hh (ENNReal.ofReal_le_ofReal (Rat.cast_le.2 hEe))
  have hp := pref_le o.θ o.cthr t.J t.P hθ hcthr
  set prefQ : ℚ := 1 / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) with hprefQ
  have hpref0 : 0 ≤ prefQ := by
    rw [hprefQ]
    have := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
    have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
    positivity
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  rw [hL, hcard] at hmain
  calc hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0)
      ≤ (2 : ℝ≥0∞) ^ b * ENNReal.ofReal (o.Eg : ℝ) +
          ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by
        refine le_trans hmain (add_le_add (mul_le_mul_left' hEg' _) (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) ?_))
        refine pow_le_pow_left' ?_ _
        rw [show ((1 + o.Ee : ℚ) : ℝ) = 1 + (o.Ee : ℝ) by push_cast; ring, ENNReal.ofReal_add zero_le_one
          (by exact_mod_cast hEe0), ENNReal.ofReal_one]
        exact add_le_add le_rfl hEe'
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ b * o.Eg) + ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal (sqUp t.P b (1 + o.Ee) : ℝ) := by
        gcongr
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        · exact ofReal_pow_le_sqUp t.P b (1 + o.Ee)
    _ = ENNReal.ofReal (((2 : ℚ) ^ b * o.Eg + sqUp t.P b (1 + o.Ee) * prefQ : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_mul (by exact_mod_cast hpref0), ← ENNReal.ofReal_add (by
          have : (0 : ℝ) ≤ (o.Eg : ℝ) := by exact_mod_cast hEg0
          positivity) (mul_nonneg (by exact_mod_cast hpref0) (by exact_mod_cast hsq0))]
        push_cast
        ring_nf
    _ ≤ ENNReal.ofReal (o.B : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        have h8' : ((2 : ℚ) ^ b * o.Eg + sqUp t.P b (1 + o.Ee) * prefQ) ≤ o.B := by
          rw [hprefQ, mul_one_div]
          exact hB
        exact_mod_cast h8'
end Sphincs.Security.H0
