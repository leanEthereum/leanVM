import FORS.CoverBound.MomentTable
import FORS.SmallBudget.Contact.NearWitness
import FORS.LargeBudget.Covers

/-! **The near H-term certificate.** The per-index near value is dominated by a convex increasing
table `n̄` (extended linearly beyond `n1`) above `k κ Ψ1(n)^(k-1)` and the cap `k κ`; the near
H-term at every budget is then at most `2^b E_μ[n̄]`. -/

open ENNReal NNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.H0 FORS.Base.Domination H0Avg ForsPotential

set_option linter.unusedSectionVars false

/-- The near bound at `n` from the moment table: the free tree contributes a factor one. -/
def nBound (H k a n : ℕ) : ℚ := k * κQ H * (P1tab a).getD n 0 ^ (k - 1)

/-- A near certificate: the table, its extension slope, and its Poisson mean. -/
structure OptN where
  nt : List ℚ
  Jn : ℚ
  En : ℚ

/-- The check of a near certificate against a Poisson table. -/
def checkOptN (H k a : ℕ) (t : PoisT) (o : OptN) : Bool :=
  decide (t.n1 ≤ 150) && decide (o.nt.length = t.n1 + 1) && checkLeaf o.nt o.Jn &&
    decide (∀ n < t.n1 + 1, nBound H k a n ≤ o.nt.getD n 0) &&
    decide ((k : ℚ) * κQ H ≤ o.nt.getD t.n1 0 + o.Jn) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.nt.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.nt.getD t.n1 0 / (1 - t.r) + o.Jn / (1 - t.r) ^ 2)) ≤ o.En)

theorem checkOptN_parts {H k a : ℕ} {t : PoisT} {o : OptN} (h : checkOptN H k a t o = true) :
    t.n1 ≤ 150 ∧ o.nt.length = t.n1 + 1 ∧ checkLeaf o.nt o.Jn = true ∧
      (∀ n < t.n1 + 1, nBound H k a n ≤ o.nt.getD n 0) ∧ (k : ℚ) * κQ H ≤ o.nt.getD t.n1 0 + o.Jn ∧
      (((List.range (t.n1 + 1)).map fun n => t.pb n * o.nt.getD n 0).sum +
        t.pb (t.n1 + 1) * (o.nt.getD t.n1 0 / (1 - t.r) + o.Jn / (1 - t.r) ^ 2)) ≤ o.En := by
  simp only [checkOptN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem SepGood.one : SepGood (fun _ : ℕ => (1 : ℝ≥0∞)) where
  mono := fun _ _ _ => le_rfl
  convex := fun _ => le_rfl
  growth := ⟨1, fun n => by
    simp only [ENNReal.coe_one, one_mul]
    exact one_le_pow₀ (by norm_num)⟩


/-- **The near value is dominated by the table.** -/
theorem avgN_near_le {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) {t : PoisT} {o : OptN}
    (ho : checkOptN H k a t o) (n : ℕ) :
    avgN (fun Ms => κE * yN Ms) n 0 ≤ ENNReal.ofReal (leafQ o.nt o.Jn n : ℝ) := by
  subst hk
  subst ha
  obtain ⟨h150, hl, hleaf, hnb, hend, -⟩ := checkOptN_parts ho
  have hκ := κE_toReal H b hH hb
  have hκ0 : (0 : ℝ) ≤ (κQ H : ℝ) := by unfold κQ; positivity
  have hκE : κE = ENNReal.ofReal (κQ H : ℝ) := by
    rw [← hκ, ENNReal.ofReal_toReal κE_ne_top]
  have hcard : ∀ c : ℝ≥0∞, ∑ _κ : FTree, c = (forsTrees : ℝ≥0∞) * c := fun c => by
    simp only [Finset.sum_const, Finset.card_univ, card_ftree, nsmul_eq_mul]
  by_cases hn : n < t.n1 + 1
  · rw [leafQ_of_lt (by omega), avgN_const_mul, avgN_yN, hcard]
    have hP1 := Ψ1R_le_tab n (by omega)
    have hΨ1 : 0 ≤ Ψ1R n := avgNR_nonneg coverAvg_nonneg n 0
    have hterm : ENNReal.ofReal (Ψ1R n) ^ (forsTrees - 1) ≤
        ENNReal.ofReal ((((P1tab forsHeight).getD n 0 ^ (forsTrees - 1) : ℚ)) : ℝ) := by
      rw [← ENNReal.ofReal_pow hΨ1]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      exact pow_le_pow_left₀ hΨ1 hP1 (forsTrees - 1)
    calc κE * ((forsTrees : ℝ≥0∞) * ENNReal.ofReal (Ψ1R n) ^ (forsTrees - 1))
        ≤ κE * ((forsTrees : ℝ≥0∞) *
            ENNReal.ofReal ((((P1tab forsHeight).getD n 0 ^ (forsTrees - 1) : ℚ)) : ℝ)) :=
          mul_le_mul_right (mul_le_mul_right hterm _) _
      _ = ENNReal.ofReal ((nBound H forsTrees forsHeight n : ℚ) : ℝ) := by
          rw [hκE, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hκ0]
          congr 1
          unfold nBound
          push_cast
          ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by exact_mod_cast hnb n hn)
  · have hcap : avgN (fun Ms => κE * yN Ms) n 0 ≤
        ENNReal.ofReal (((forsTrees : ℚ) * κQ H : ℚ) : ℝ) := by
      calc avgN (fun Ms => κE * yN Ms) n 0 ≤ avgN (fun _ => κE * (forsTrees : ℝ≥0∞)) n 0 :=
            avgN_mono (fun Ms => mul_le_mul_right (yN_le Ms) _) n 0
        _ = κE * (forsTrees : ℝ≥0∞) := avgN_const _ n 0
        _ = _ := by
            rw [hκE, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hκ0]
            congr 1
            push_cast
            ring
    refine le_trans hcap (ENNReal.ofReal_le_ofReal ?_)
    have h := leafQ_ge_end hleaf (n := n) (by omega)
    rw [hl, show t.n1 + 1 - 1 = t.n1 by omega] at h
    exact_mod_cast le_trans hend h

/-- **The near H-term** through a separable majorant. -/
theorem hTermO_near_le (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) (gbar : ℕ → ℝ≥0∞)
    (hgG : SepGood gbar) (hg : ∀ n, avgN (fun Ms => κE * yN Ms) n 0 ≤ gbar n)
    (α γ : ℝ≥0) (hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO (Finset.univ : Finset View) w lam N q (priceW witnessNear) ≤
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * poisMean μ gbar := by
  have hdom : Dominated (priceW witnessNear) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (e.count l)) :=
    dominated_of_split (fun Ms => κE * yN Ms) (fun _ => 1) 0
      (fun d => by rw [priceNear_decomp, zero_mul, add_zero]) gbar (fun _ => 1) hg
      (fun n => le_of_eq (avgN_const 1 n 0))
  refine le_trans (hTermO_le_of_dominated w lam N q hdom) ?_
  have hcnt : (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (e.count l)) =
      fun e => (fun k : Fin (2 ^ subtreeHeight) → ℕ => ∑ l, gbar (k l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (k l))
        (cnt id e) := by
    funext e
    simp only [cnt_id]
  rw [hcnt]
  refine le_trans (hTermO_le_poisIID_of_le id Finset.univ uniformIndex_id
    (sep_countGood hgG SepGood.one 0 ENNReal.zero_ne_top) w lam hw hlam α γ hα hγ N q μ hμ) (le_of_eq ?_)
  rw [poisIID_sep μ gbar (fun _ => 1) 0, zero_mul, add_zero]

/-- The near H-term at budget `q`: the start value of the near potential's new-pair forecast. -/
noncomputable def hNearOf (q : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ (wbarOf q)
    (excessW witnessNear 0) signatureLimit I 0) q []

theorem hNearOf_eq (q : ℕ) :
    hNearOf q = hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q (priceW witnessNear) := by
  unfold hNearOf hTermO excessW
  simp only [tsub_zero]

/-- **The near H-term for every budget `q ≤ qtop`, from a checked table and certificate.** -/
theorem hNearOf_le (H b k a N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N)
    (t : PoisT) (o : OptN) (hr : checkRate H b N qtop t = true) (ht : checkPT t = true)
    (ho : checkOptN H k a t o = true) (q : ℕ)
    (hq : q ≤ qtop) : hNearOf q ≤ ENNReal.ofReal ((2 ^ b * o.En : ℚ) : ℝ) := by
  obtain ⟨-, hl, hleaf, -, -, hEn⟩ := checkOptN_parts ho
  set w := wbarOf q with hwdef
  have hw1 : w ≤ 1 := wbar_le_one q (fair_of_rate H b N qtop t hr hH hb q hq)
  have hlw : landing * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' ForsPrice.landing_le_one hw1)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin, hb]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (landing * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = landing * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (signatureLimit : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, hγdef, hαdef]
    push_cast
    calc (signatureLimit : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((landing * w).toReal / 2 ^ b)
        = (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * w).toReal / 2 ^ b := by ring
      _ ≤ _ := rate_le_tableF H b N qtop t hr hH hb hN q hq
  rw [hNearOf_eq]
  refine le_trans (hTermO_near_le w landing hw1 ForsPrice.landing_le_one signatureLimit q
    (fun n => ENNReal.ofReal (leafQ o.nt o.Jn n : ℝ)) (leaf_sepGood hleaf)
    (avgN_near_le hH hb hk ha ho) α γ hα hγ μ hμ) ?_
  have hpm := poisMean_leaf_le ht hleaf hl
  rw [← hμdef] at hpm
  have hpm' : poisMean μ (fun n => ENNReal.ofReal (leafQ o.nt o.Jn n : ℝ)) ≤ ENNReal.ofReal (o.En : ℝ) :=
    le_trans hpm (ENNReal.ofReal_le_ofReal (Rat.cast_le.2 hEn))
  rw [hL]
  calc (2 : ℝ≥0∞) ^ b * poisMean μ (fun n => ENNReal.ofReal (leafQ o.nt o.Jn n : ℝ))
      ≤ (2 : ℝ≥0∞) ^ b * ENNReal.ofReal (o.En : ℝ) := mul_le_mul_right hpm' _
    _ = ENNReal.ofReal ((2 ^ b * o.En : ℚ) : ℝ) := by
        by_cases hE : (0 : ℝ) ≤ (o.En : ℝ)
        · rw [show ((2 ^ b * o.En : ℚ) : ℝ) = (2 : ℝ) ^ b * (o.En : ℝ) by push_cast; ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        · push Not at hE
          rw [ENNReal.ofReal_of_nonpos hE.le, mul_zero, ENNReal.ofReal_of_nonpos]
          push_cast
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hE.le

end FORS.Security.H0
