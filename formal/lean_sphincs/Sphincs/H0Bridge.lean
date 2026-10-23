import Sphincs.H0Tables
import Sphincs.BridgeForestPrice
import Sphincs.BridgeForsPotential
import SphincsFors.H0Split

/-! **From the forest price to per-index moments.** The cover price of a multiset of disclosed views
is a sum over the indices of the probability that a uniform mark is covered by the marks at the
index, a product over the 8 trees of the per-tree cover fraction `φ`. The excess over a threshold
splits pointwise (as for FORS) into per-index functions of the marks; their mark averages are
bounded by the first and second moments `E[y | n] = Ψ1(n)^8`, `E[y^2 | n] = Ψ2(n)^8`. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice SphincsFors.Security.Domination H0Avg

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### A quadratic bound of the exponential -/

theorem exp_quad (z z1 : ℝ) (hz : 0 ≤ z) (hzz : z ≤ z1) (hz1 : 0 < z1) :
    Real.exp z ≤ 1 + z + (Real.exp z1 - 1 - z1) * (z / z1) ^ 2 := by
  have hser : ∀ x : ℝ, Real.exp x = 1 + x + ∑' n : ℕ, x ^ (n + 2) / (n + 2).factorial := by
    intro x
    have he : Real.exp x = ∑' n : ℕ, x ^ n / n.factorial := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hs := Real.summable_pow_div_factorial x
    rw [he, ← hs.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ]
  rw [hser z, hser z1]
  have hsz := (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial z)
  have hsz1 := (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial z1)
  have hle : ∑' n : ℕ, z ^ (n + 2) / (n + 2).factorial ≤ (z / z1) ^ 2 * ∑' n : ℕ, z1 ^ (n + 2) / (n + 2).factorial := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) hsz (hsz1.mul_left _)
    have hzn : z ^ n ≤ z1 ^ n := pow_le_pow_left₀ hz hzz n
    have hfac : (0 : ℝ) < (n + 2).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right hfac]
    calc z ^ (n + 2) = z ^ 2 * z ^ n := by ring
      _ ≤ z ^ 2 * z1 ^ n := by gcongr
      _ = z ^ 2 / z1 ^ 2 * z1 ^ (n + 2) := by field_simp; ring
  linarith [hle]

/-- The quadratic bound of the capped exponential. -/
theorem exp_min_le (θ c1 x : ℝ) (hθ : 0 < θ) (hc1 : 0 < c1) (hx : 0 ≤ x) :
    Real.exp (θ * min x c1) ≤ 1 + θ * x + (Real.exp (θ * c1) - 1 - θ * c1) / c1 ^ 2 * x ^ 2 := by
  have hz1 : 0 < θ * c1 := mul_pos hθ hc1
  have hA : 0 ≤ Real.exp (θ * c1) - 1 - θ * c1 := by linarith [Real.add_one_le_exp (θ * c1)]
  rcases le_total x c1 with h | h
  · rw [min_eq_left h]
    have := exp_quad (θ * x) (θ * c1) (by positivity) (by nlinarith) hz1
    calc Real.exp (θ * x) ≤ 1 + θ * x + (Real.exp (θ * c1) - 1 - θ * c1) * (θ * x / (θ * c1)) ^ 2 := this
      _ = _ := by field_simp
  · rw [min_eq_right h]
    have hx2 : c1 ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hc1.le h 2
    calc Real.exp (θ * c1) = 1 + θ * c1 + (Real.exp (θ * c1) - 1 - θ * c1) / c1 ^ 2 * c1 ^ 2 := by
          field_simp; ring
      _ ≤ _ := by
          gcongr

/-! ### The per-tree cover fraction -/

/-- Every chain the target field needs is opened deep enough by a disclosed field. -/
def CoverF (t : FieldVal) (Xs : Multiset FieldVal) : Prop :=
  ∀ j i, chainNeed t j i = 0 ∨ ∃ x ∈ Xs, KeyCovers x t j i

open Classical in
/-- The per-tree cover fraction of a multiset of disclosed fields. -/
noncomputable def φF (Xs : Multiset FieldVal) : ℝ≥0∞ :=
  freshAvg Finset.univ fun t : FieldVal => if CoverF t Xs then 1 else 0

/-- The cover probability of a multiset of disclosed marks at one index. -/
noncomputable def yM (Ms : Multiset (Coord → FieldVal)) : ℝ≥0∞ := ∏ c, φF (Ms.map fun m => m c)

theorem coverF_iff (t : FieldVal) (Xs : Multiset FieldVal) :
    CoverF t Xs ↔ CoverT (fieldMT t) (Xs.map fieldMT) := by
  unfold CoverF CoverT
  simp only [Multiset.mem_map]
  constructor
  · intro h j i
    rcases h j i with h0 | ⟨x, hx, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨fieldMT x, ⟨x, hx, rfl⟩, hk⟩
  · intro h j i
    rcases h j i with h0 | ⟨_, ⟨x, hx, rfl⟩, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨x, hx, hk⟩

/-! ### The price at an index -/

variable [Params]

theorem mem_marks_map (l : Fin (2 ^ subtreeHeight)) (d : Multiset View) (c : Coord) (x : FieldVal) :
    x ∈ (marksAt l d).map (fun m => m c) ↔ ∃ v ∈ d, v.1 = l ∧ v.2 c = x := by
  unfold marksAt
  simp only [Multiset.map_map, Multiset.mem_map, Multiset.mem_filter, Function.comp]
  constructor
  · rintro ⟨v, ⟨hv, hl⟩, rfl⟩; exact ⟨v, hv, hl, rfl⟩
  · rintro ⟨v, hv, hl, rfl⟩; exact ⟨v, ⟨hv, hl⟩, rfl⟩

theorem coverAll_iff (l : Fin (2 ^ subtreeHeight)) (τ : Coord → FieldVal) (d : Multiset View) :
    CoverAll (l, τ) d ↔ ∀ c, CoverF (τ c) ((marksAt l d).map fun m => m c) := by
  unfold CoverAll ChainCovered CoverF
  simp only [mem_marks_map]
  constructor
  · intro h c j i
    rcases h c j i with h0 | ⟨v, hv, hl, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨v.2 c, ⟨v, hv, hl, rfl⟩, hk⟩
  · intro h c j i
    rcases h c j i with h0 | ⟨_, ⟨v, hv, hl, rfl⟩, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨v, hv, hl, hk⟩

/-- **The price is a sum over the indices.** -/
theorem price_decomp (d : Multiset View) :
    price d = ∑ l : Fin (2 ^ subtreeHeight), (landing * (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞)⁻¹) *
      yM (marksAt l d) := by
  classical
  unfold price
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (Coord → FieldVal)))
    from rfl, freshAvg_prod]
  have hw : ∀ (l : Fin (2 ^ subtreeHeight)) (τ : Coord → FieldVal), witness (l, τ) d =
      ∏ c, if CoverF (τ c) ((marksAt l d).map fun m => m c) then 1 else 0 := by
    intro l τ
    unfold witness
    by_cases h : CoverAll (l, τ) d
    · rw [ite_eq_left h]
      exact (Finset.prod_eq_one fun c _ => ite_eq_left ((coverAll_iff l τ d).1 h c)).symm
    · rw [ite_eq_right h]
      rw [coverAll_iff] at h
      push Not at h
      obtain ⟨c, hc⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ c) (ite_eq_right hc)).symm
  simp only [hw]
  have hy : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg Finset.univ fun τ : Coord → FieldVal =>
      ∏ c, if CoverF (τ c) ((marksAt l d).map fun m => m c) then (1 : ℝ≥0∞) else 0) = yM (marksAt l d) := by
    intro l
    rw [freshAvg_pi_prod (fun c (t : FieldVal) => if CoverF t ((marksAt l d).map fun m => m c) then (1 : ℝ≥0∞) else 0)]
    rfl
  simp only [hy]
  unfold freshAvg
  rw [Finset.mul_sum, Finset.mul_sum, Finset.card_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring


/-! ### The per-tree moments as mark averages -/

omit [Params] in
theorem freshAvg_ofReal {α : Type} [Fintype α] [Nonempty α] (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    freshAvg (Finset.univ : Finset α) (fun a => ENNReal.ofReal (g a)) = ENNReal.ofReal (avgR g) := by
  unfold freshAvg avgR
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun a _ => hg a), Finset.card_univ,
    ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]

omit [Params] in
theorem avgNR_nonneg {α : Type} [Fintype α] {φ : Multiset α → ℝ} (hφ : ∀ X, 0 ≤ φ X) :
    ∀ n X, 0 ≤ avgNR φ n X
  | 0, X => hφ X
  | n + 1, X => by
      unfold avgNR avgR
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun x _ => avgNR_nonneg hφ n (X + {x}))

omit [Params] in
theorem coverR_nonneg (t : MT) (X : Multiset MT) : 0 ≤ coverR t X := by
  unfold coverR; split_ifs <;> norm_num

omit [Params] in
theorem coverAvg_nonneg (X : Multiset MT) : 0 ≤ avgR fun t : MT => coverR t X := by
  unfold avgR
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun t _ => coverR_nonneg t X)

omit [Params] in
/-- Mark averages over fields are averages over tuples. -/
theorem avgN_field (F : Multiset FieldVal → ℝ≥0∞) (R : Multiset MT → ℝ) (hR : ∀ X, 0 ≤ R X)
    (hF : ∀ Xs, F Xs = ENNReal.ofReal (R (Xs.map fieldMT))) :
    ∀ n X0, avgN F n X0 = ENNReal.ofReal (avgNR R n (X0.map fieldMT))
  | 0, X0 => hF X0
  | n + 1, X0 => by
      simp only [avgN, avgN_field F R hR hF n, Multiset.map_add, Multiset.map_singleton]
      rw [freshAvg_ofReal (fun v : FieldVal => avgNR R n (X0.map fieldMT + {fieldMT v}))
        (fun v => avgNR_nonneg hR n _),
        show avgNR R (n + 1) (X0.map fieldMT) = avgR (fun x => avgNR R n (X0.map fieldMT + {x})) from rfl]
      refine congrArg ENNReal.ofReal ?_
      rw [avgR_equiv fieldMT]
      simp only [Equiv.apply_symm_apply]

omit [Params] in
theorem φF_eq (Xs : Multiset FieldVal) :
    φF Xs = ENNReal.ofReal (avgR fun t : MT => coverR t (Xs.map fieldMT)) := by
  classical
  unfold φF
  have hpt : ∀ t : FieldVal, (if CoverF t Xs then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (coverR (fieldMT t) (Xs.map fieldMT)) := by
    intro t
    unfold coverR
    by_cases h : CoverF t Xs
    · rw [ite_eq_left h, ite_eq_left ((coverF_iff t Xs).1 h), ENNReal.ofReal_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((coverF_iff t Xs).2 h')), ENNReal.ofReal_zero]
  simp only [hpt]
  rw [freshAvg_ofReal _ (fun t => coverR_nonneg _ _), avgR_equiv fieldMT]
  simp only [Equiv.apply_symm_apply]

omit [Params] in
theorem avgN_φF (n : ℕ) : avgN φF n 0 = ENNReal.ofReal (Ψ1R n) := by
  rw [avgN_field φF (fun X => avgR fun t : MT => coverR t X) coverAvg_nonneg φF_eq n 0]
  rfl

omit [Params] in
theorem avgN_φF_sq (n : ℕ) : avgN (fun Xs => φF Xs ^ 2) n 0 = ENNReal.ofReal (Ψ2R n) := by
  rw [avgN_field (fun Xs => φF Xs ^ 2) (fun X => (avgR fun t : MT => coverR t X) ^ 2)
    (fun X => sq_nonneg _) (fun Xs => by rw [φF_eq, ← ENNReal.ofReal_pow (coverAvg_nonneg _)]) n 0]
  rfl

omit [Params] in
theorem card_coord : Fintype.card Coord = 8 := by
  show Fintype.card (Fin forestCoords) = 8
  rw [Fintype.card_fin]
  rfl

omit [Params] in
/-- **`E[y | n] = Ψ1(n)^8`.** -/
theorem avgN_yM (n : ℕ) : avgN yM n 0 = ENNReal.ofReal (Ψ1R n) ^ 8 := by
  unfold yM
  rw [avgN_prod_coords (fun _ => φF) n 0]
  simp only [Multiset.map_zero, avgN_φF]
  rw [Finset.prod_const, Finset.card_univ, card_coord]

omit [Params] in
/-- **`E[y^2 | n] = Ψ2(n)^8`.** -/
theorem avgN_yM_sq (n : ℕ) : avgN (fun Ms => yM Ms ^ 2) n 0 = ENNReal.ofReal (Ψ2R n) ^ 8 := by
  unfold yM
  simp only [← Finset.prod_pow]
  rw [avgN_prod_coords (fun _ Xs => φF Xs ^ 2) n 0]
  simp only [Multiset.map_zero, avgN_φF_sq]
  rw [Finset.prod_const, Finset.card_univ, card_coord]


/-! ### The pointwise split of the excess -/

omit [Params] in
theorem φF_le_one (Xs : Multiset FieldVal) : φF Xs ≤ 1 := by
  classical
  unfold φF
  calc freshAvg Finset.univ (fun t : FieldVal => if CoverF t Xs then (1 : ℝ≥0∞) else 0)
      ≤ freshAvg Finset.univ (fun _ : FieldVal => (1 : ℝ≥0∞)) := freshAvg_mono _ fun t _ => by split_ifs <;> simp
    _ = 1 := freshAvg_const _ Finset.univ_nonempty 1

omit [Params] in
theorem yM_le_one (Ms : Multiset (Coord → FieldVal)) : yM Ms ≤ 1 :=
  Finset.prod_le_one fun c _ => φF_le_one _

omit [Params] in
theorem yM_ne_top (Ms : Multiset (Coord → FieldVal)) : yM Ms ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (yM_le_one Ms)

/-- The per-index weight `landing / L` of the cover probability. -/
noncomputable def κE : ℝ≥0∞ := landing * (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞)⁻¹

theorem κE_ne_top : κE ≠ ⊤ :=
  ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one)
    (ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero))

/-- The per-index excess part of the split. -/
noncomputable def gS (c1 : ℝ) (Ms : Multiset (Coord → FieldVal)) : ℝ≥0∞ :=
  ENNReal.ofReal (κE.toReal * (yM Ms).toReal - c1)

/-- The per-index Chernoff factor of the split. -/
noncomputable def hS (c1 θ : ℝ) (Ms : Multiset (Coord → FieldVal)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * min (κE.toReal * (yM Ms).toReal) c1))

/-- **The pointwise split** of the excess of the forest price over a threshold. -/
theorem excess_le_split (b0 : ℝ≥0∞) (c c1 θ : ℝ) (hc : ENNReal.ofReal c ≤ b0) (hθ : 0 < θ) (d : Multiset View) :
    ForsPotential.excess b0 d ≤ ∑ l : Fin (2 ^ subtreeHeight), gS c1 (marksAt l d) +
      ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) * ∏ l : Fin (2 ^ subtreeHeight), hS c1 θ (marksAt l d) := by
  unfold ForsPotential.excess
  rw [price_decomp]
  set y : Fin (2 ^ subtreeHeight) → ℝ := fun l => κE.toReal * (yM (marksAt l d)).toReal with hy
  have hsum : ∑ l : Fin (2 ^ subtreeHeight), (landing * (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞)⁻¹) *
      yM (marksAt l d) = ENNReal.ofReal (∑ l, y l) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hy, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal κE_ne_top,
      ENNReal.ofReal_toReal (yM_ne_top _)]
    rfl
  rw [hsum]
  calc ENNReal.ofReal (∑ l, y l) - b0 ≤ ENNReal.ofReal (∑ l, y l) - ENNReal.ofReal c := tsub_le_tsub_left hc _
    _ ≤ ENNReal.ofReal (∑ l, y l - c) := by
        rcases le_total c 0 with h0 | h0
        · rw [ENNReal.ofReal_of_nonpos h0, tsub_zero]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · rw [← ENNReal.ofReal_sub _ h0]
    _ ≤ ENNReal.ofReal (∑ l, max (y l - c1) 0 +
          Real.exp (-θ * c) / (Real.exp 1 * θ) * ∏ l, Real.exp (θ * min (y l) c1)) :=
        ENNReal.ofReal_le_ofReal (SphincsFors.Security.H0.split_real _ c c1 θ hθ)
    _ = _ := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun l _ => le_max_right _ _) (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun l _ => le_max_right _ _),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun l _ => by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold gS
        rcases le_total (y l - c1) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

/-! ### Bounds of the per-index parts by the moments -/

theorem gS_le_sq (c1 : ℝ) (hc1 : 0 < c1) (Ms : Multiset (Coord → FieldVal)) :
    gS c1 Ms ≤ ENNReal.ofReal (κE.toReal ^ 2 / (4 * c1)) * yM Ms ^ 2 := by
  unfold gS
  conv_rhs => rw [← ENNReal.ofReal_toReal (yM_ne_top Ms), ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set x := κE.toReal * (yM Ms).toReal
  have : x - c1 ≤ x ^ 2 / (4 * c1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - 2 * c1)]
  calc x - c1 ≤ x ^ 2 / (4 * c1) := this
    _ = _ := by rw [show x = κE.toReal * (yM Ms).toReal from rfl]; ring

theorem gS_le_lin (c1 : ℝ) (hc1 : 0 < c1) (Ms : Multiset (Coord → FieldVal)) :
    gS c1 Ms ≤ ENNReal.ofReal κE.toReal * yM Ms := by
  unfold gS
  conv_rhs => rw [← ENNReal.ofReal_toReal (yM_ne_top Ms), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem hS_le_cap (c1 θ : ℝ) (hθ : 0 < θ) (Ms : Multiset (Coord → FieldVal)) :
    hS c1 θ Ms ≤ ENNReal.ofReal (Real.exp (θ * c1)) := by
  unfold hS
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ.le)

theorem hS_le_quad (c1 θ : ℝ) (hc1 : 0 < c1) (hθ : 0 < θ) (Ms : Multiset (Coord → FieldVal)) :
    hS c1 θ Ms ≤ 1 + ENNReal.ofReal (θ * κE.toReal) * yM Ms +
      ENNReal.ofReal ((Real.exp (θ * c1) - 1 - θ * c1) / c1 ^ 2 * κE.toReal ^ 2) * yM Ms ^ 2 := by
  unfold hS
  have hA : 0 ≤ (Real.exp (θ * c1) - 1 - θ * c1) / c1 ^ 2 := by
    have := Real.add_one_le_exp (θ * c1)
    exact div_nonneg (by linarith) (by positivity)
  have hy0 : 0 ≤ (yM Ms).toReal := ENNReal.toReal_nonneg
  have hk0 : 0 ≤ κE.toReal := ENNReal.toReal_nonneg
  conv_rhs => rw [← ENNReal.ofReal_toReal (yM_ne_top Ms), ← ENNReal.ofReal_pow hy0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := exp_min_le θ c1 (κE.toReal * (yM Ms).toReal) hθ hc1 (by positivity)
  calc _ ≤ _ := this
    _ = _ := by ring

end Sphincs.Security.H0
