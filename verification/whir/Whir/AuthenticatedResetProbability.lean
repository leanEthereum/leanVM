import Whir.RewindCoverage

/-! Finite probability facts for acceptance-dependent reset events. Independence
is used only for the complete product trial seed, never for prover answers. -/
namespace Whir.AuthenticatedResetProbability
open SamplingProbability
open scoped BigOperators

variable {A : Type*} [Fintype A] [Nonempty A]

theorem nonneg (P : A → Prop) : 0 ≤ probability P := by
  unfold probability
  positivity

theorem mono (P Q : A → Prop) (h : ∀ a, P a → Q a) :
    probability P ≤ probability Q := by
  classical
  simp only [probability, Fintype.card_subtype]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (by intro a ha; simpa using h a (Finset.mem_filter.mp ha).2)

theorem le_one (P : A → Prop) : probability P ≤ 1 := by
  classical
  unfold probability
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card A)).mpr
  rw [Fintype.card_subtype]
  exact_mod_cast Finset.card_filter_le Finset.univ P

theorem complement (P : A → Prop) : probability (fun a => ¬ P a) = 1 - probability P := by
  classical
  have partition : (Finset.univ.filter P).card + (Finset.univ.filter fun a => ¬ P a).card =
      Fintype.card A := by
    simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset A)) P
  simp only [probability, Fintype.card_subtype]
  have positive : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have castPartition : ((Finset.univ.filter P).card : ℝ) +
      (Finset.univ.filter fun a => ¬ P a).card = Fintype.card A := by exact_mod_cast partition
  field_simp
  linarith

omit [Nonempty A] in
theorem union_le {I : Type*} [Fintype I] (P : I → A → Prop) :
    probability (fun a => ∃ i, P i a) ≤ ∑ i, probability (P i) := by
  classical
  have events : (Finset.univ.filter fun a => ∃ i, P i a) =
      Finset.univ.biUnion (fun i => Finset.univ.filter (P i)) := by ext a; simp
  rw [probability_eq_uniformProb, events]
  simpa only [probability_eq_uniformProb, Rat.cast_sum] using
    (show (Soundness.uniformProb (Finset.univ.biUnion fun i => Finset.univ.filter (P i)) : ℝ) ≤
      ∑ i, (Soundness.uniformProb (Finset.univ.filter (P i)) : ℝ) by
      exact_mod_cast Soundness.union_bound (fun i => Finset.univ.filter (P i)))

def splitUnit (A : Type*) : A ≃ Unit × A where
  toFun a := ((), a)
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by cases a with | mk u a => cases u; rfl

theorem independent_misses (P : A → Prop) (rounds : Nat) :
    probability (fun seed : Fin rounds → A => ∀ r, ¬ P (seed r)) =
      (1 - probability P) ^ rounds := by
  have product := coordinateEvent_probability (splitUnit (Fin rounds → A)) (fun _ a => ¬ P a)
  change probability (fun seed : Fin rounds → A => ∀ r, ¬ P (seed r)) =
    ∏ _ : Fin rounds, probability (fun a => ¬ P a) at product
  simpa only [complement, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using product

omit [Nonempty A] in
theorem product_left {B : Type*} [Fintype B] [Nonempty B] (P : A → Prop) :
    probability (fun a : A × B => P a.1) = probability P := by
  classical
  let e : {a : A × B // P a.1} ≃ {a : A // P a} × B :=
    { toFun := fun a => (⟨a.val.1, a.property⟩, a.val.2)
      invFun := fun a => ⟨(a.1.val, a.2), a.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold probability
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_ne_zero)

omit [Nonempty A] in
theorem probability_average {B : Type*} [Fintype B] [Nonempty B] (P : A × B → Prop) :
    probability P = (∑ a, probability (fun b => P (a, b))) / Fintype.card A := by
  classical
  have cards : (Finset.univ.filter P).card =
      ∑ a : A, (Finset.univ.filter fun b : B => P (a, b)).card := by
    simpa using
      (Fintype.sum_prod_type (fun a : A × B => if P a then (1 : Nat) else 0))
  simp only [probability, Fintype.card_subtype, cards, Fintype.card_prod,
    Nat.cast_mul, Nat.cast_sum, ← Finset.sum_div]
  rw [div_div, mul_comm]

end Whir.AuthenticatedResetProbability
