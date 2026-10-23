import SphincsFors.H0Assembly
import SphincsFors.BridgeForsPotential

/-! The repository's FORS count price in count form, `price D = 2^-266 Σ_l K_l(D)^24`, and the
uniform index marginal of a fresh kept view. -/

open ENNReal

namespace SphincsFors.Security.H0

open Concrete Domination ForsPrice

set_option exponentiation.threshold 512

set_option linter.unusedSectionVars false

/-- The fibres of a map partition a multiset. -/
theorem sum_card_filter_eq {α β : Type} [Fintype β] [DecidableEq β] (f : α → β) (M : Multiset α) :
    ∑ a : β, (M.filter fun v => f v = a).card = M.card := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons v M ih =>
      have h : ∀ a : β, (Multiset.filter (fun x => f x = a) (v ::ₘ M)).card =
          (if f v = a then 1 else 0) + (M.filter fun x => f x = a).card := by
        intro a
        rw [Multiset.filter_cons]
        split_ifs <;> simp [add_comm]
      simp only [h, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Multiset.card_cons]
      ring

variable [Params]

/-- The scale of the count price. -/
noncomputable def kappa : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 266)⁻¹

/-- The witness counts summed over all targets. -/
theorem sum_witness (D : Multiset View) :
    ∑ target : View, witness target D = ∑ l : Fin (2 ^ subtreeHeight), (cnt Prod.fst D l) ^ 24 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hfib : ∀ t : IndexGroup, ∑ a : FtsLeaf, (D.filter fun v : View => v.1 = l ∧ v.2 t = a).card =
      cnt Prod.fst D l := by
    intro t
    have h := sum_card_filter_eq (fun v : View => v.2 t) (D.filter fun v : View => v.1 = l)
    unfold cnt
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Multiset.filter_filter]
    exact congrArg Multiset.card (Multiset.filter_congr fun v _ => and_comm)
  calc ∑ r : IndexGroup → FtsLeaf, witness (l, r) D
      = ∑ r : IndexGroup → FtsLeaf, ∏ t, (D.filter fun v : View => v.1 = l ∧ v.2 t = r t).card := rfl
    _ = ∏ t : IndexGroup, ∑ a : FtsLeaf, (D.filter fun v : View => v.1 = l ∧ v.2 t = a).card := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ _t : IndexGroup, cnt Prod.fst D l := Finset.prod_congr rfl fun t _ => hfib t
    _ = cnt Prod.fst D l ^ 24 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl

theorem card_view : Fintype.card View = 2 ^ subtreeHeight * 2 ^ 240 := by
  simp only [View, Lifetime.KeptDigestView, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul]
  rfl

/-- **Count form of the price.** -/
theorem price_eq (D : Multiset View) : price D = countPrice Prod.fst kappa D := by
  unfold price freshAvg countPrice
  have hsum : ∑ target ∈ (Finset.univ : Finset View), (witness target D : ℝ≥0∞) =
      ∑ l : Fin (2 ^ subtreeHeight), ((cnt Prod.fst D l : ℝ≥0∞)) ^ 24 := by
    rw [← Nat.cast_sum, sum_witness]; push_cast; rfl
  rw [hsum, Finset.card_univ, card_view, ← Finset.mul_sum, ← mul_assoc]
  congr 1
  unfold landing kappa
  have hb := (inferInstance : Params).subtreeHeight_le
  have h26 : (2 : ℝ≥0∞) ^ 266 = ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞) *
      ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← pow_add, ← pow_add]
    have : totalHeight - subtreeHeight + (subtreeHeight + 240) = 266 := by
      unfold totalHeight at hb ⊢; omega
    rw [this, Nat.cast_pow, Nat.cast_ofNat]
  rw [h26, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]

theorem uniformIndex_univ : UniformIndex (Prod.fst : View → Fin (2 ^ subtreeHeight)) Finset.univ := by
  intro g
  unfold freshAvg
  have hB : (Fintype.card (IndexGroup → FtsLeaf) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card (IndexGroup → FtsLeaf) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hs : ∑ u ∈ (Finset.univ : Finset View), g u.1 =
      (Fintype.card (IndexGroup → FtsLeaf) : ℝ≥0∞) * ∑ l, g l := by
    rw [Finset.mul_sum]
    simp only [View, Lifetime.KeptDigestView]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hs, Finset.card_univ]
  simp only [Fintype.card_prod]
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr hBt) (Or.inl (ENNReal.natCast_ne_top _)), mul_assoc,
    ← mul_assoc _ _ (∑ l, g l), ENNReal.inv_mul_cancel hB hBt, one_mul]

/-- The FORS excess in count form. -/
theorem excess_eq (b0 : ℝ≥0∞) :
    ForsPotential.excess b0 = fun D => countPrice Prod.fst kappa D - b0 := by
  funext D
  unfold ForsPotential.excess
  rw [price_eq]

end SphincsFors.Security.H0
