import SphincsSecurity.Proof.Ots.EncodingNeighbors
namespace SphincsSecurity.TargetSum

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def backwardWeight (reference candidate : Encoding) : Nat :=
  ∑ index : ChainIndex, ((reference index).val - (candidate index).val)

theorem backwardWeight_balance {reference candidate : Encoding} (hsum : sum reference = sum candidate) :
    backwardWeight reference candidate = backwardWeight candidate reference := by
  have hpoint : ∀ index : ChainIndex,
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val := by intro index; omega
  have h := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at h
  change backwardWeight reference candidate + sum candidate = backwardWeight candidate reference + sum reference at h
  omega

private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, ?_⟩
  intro other hne
  have hpair := two_terms_le_sum f hne
  omega

theorem unitNeighbor_of_backwardWeight_one {reference candidate : Encoding}
    (hsum : sum reference = sum candidate) (hweight : backwardWeight reference candidate = 1) :
    ∃ lowered, UnitNeighborAt reference candidate lowered := by
  obtain ⟨lowered, hlower, hothers⟩ := single_of_sum_one (fun index => (reference index).val - (candidate index).val) hweight
  have hreverse : backwardWeight candidate reference = 1 := (backwardWeight_balance hsum).symm.trans hweight
  obtain ⟨raised, hraise, hotherRaised⟩ := single_of_sum_one (fun index => (candidate index).val - (reference index).val) hreverse
  refine ⟨lowered, raised, ?_, ?_, ?_, ?_⟩
  · intro he
    subst raised
    omega
  · omega
  · omega
  · intro index hl hr
    have hdown := hothers index hl
    have hup := hotherRaised index hr
    apply Fin.ext
    omega

theorem eq_of_backwardWeight_zero {reference candidate : Encoding}
    (hsum : sum reference = sum candidate) (hweight : backwardWeight reference candidate = 0) : reference = candidate := by
  apply eq_of_le_of_sum_eq _ hsum
  intro index
  have hle : (reference index).val - (candidate index).val ≤ backwardWeight reference candidate := by
    unfold backwardWeight
    exact Finset.single_le_sum (f := fun index : ChainIndex => (reference index).val - (candidate index).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  omega

theorem backwardWeight_two_witness {reference candidate : Encoding} (hweight : 2 ≤ backwardWeight reference candidate) :
    (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hlarge : ∃ index, (candidate index).val + 2 ≤ (reference index).val
  · exact Or.inl hlarge
  have hnonzero : ∃ index, (candidate index).val < (reference index).val := by
    by_contra hnone
    push Not at hnone
    have hz : backwardWeight reference candidate = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Nat.sub_eq_zero_of_le (hnone index)
    omega
  obtain ⟨left, hl⟩ := hnonzero
  by_cases hother : ∃ right, left ≠ right ∧ (candidate right).val < (reference right).val
  · obtain ⟨right, hne, hr⟩ := hother
    exact Or.inr ⟨left, right, hne, hl, hr⟩
  · have hzero : ∀ index, index ≠ left → (reference index).val - (candidate index).val = 0 := by
      intro index hne
      have hn : ¬(candidate index).val < (reference index).val := fun hi => hother ⟨index, hne.symm, hi⟩
      omega
    have hsum : backwardWeight reference candidate = (reference left).val - (candidate left).val := by
      apply Finset.sum_eq_single left
      · intro index _ hne
        exact hzero index hne
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    have hn := not_exists.mp hlarge left
    omega

theorem valid_encoding_classification {reference candidate : Encoding} (hreference : Valid reference) (hcandidate : Valid candidate) :
    reference = candidate ∨ (∃ lowered, UnitNeighborAt reference candidate lowered) ∨
      (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  have hsum : sum reference = sum candidate := hreference.trans hcandidate.symm
  by_cases hzero : backwardWeight reference candidate = 0
  · exact Or.inl (eq_of_backwardWeight_zero hsum hzero)
  by_cases hone : backwardWeight reference candidate = 1
  · exact Or.inr (Or.inl (unitNeighbor_of_backwardWeight_one hsum hone))
  exact Or.inr (Or.inr (backwardWeight_two_witness (by omega)))

end SphincsSecurity.TargetSum
