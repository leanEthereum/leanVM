import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeOperators
import SphincsSecurity.Proof.Fts.TargetShapeReindex
namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable

theorem sum_proper_subsets_card {α : Type} [DecidableEq α] (s : Finset α) (f : Nat → ENNReal) :
    (∑ kept ∈ s.powerset.erase s, f kept.card) = ∑ degree ∈ Finset.range s.card, (s.card.choose degree : ENNReal) * f degree := by
  have hindicator : (∑ kept ∈ s.powerset.erase s, f kept.card) =
      ∑ kept ∈ s.powerset, if kept.card = s.card then 0 else f kept.card := by
    rw [← Finset.filter_ne', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro kept hkept
    have heq : kept.card = s.card ↔ kept = s := by
      constructor
      · intro hcard
        exact Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hkept) hcard.ge
      · rintro rfl; rfl
    by_cases h : kept = s <;> simp only [heq, h, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
  rw [hindicator, Finset.sum_powerset_apply_card (fun degree => if degree = s.card then 0 else f degree), Finset.sum_range_succ]
  simp only [if_true, smul_zero, add_zero, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hdegree))]

abbrev TargetIndexVector := Nat → Nat → ENNReal

def liftTargetIndexVector (moments : TargetIndexVector) : TargetShapeVector := fun groups remaining => moments groups.card remaining.card

noncomputable def targetIndexCacheLower (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  ∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * moments lower degree

noncomputable def targetIndexTreeLower (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  ∑ lower ∈ Finset.range degree, (degree.choose lower : ENNReal) * moments power lower

noncomputable def targetIndexReuseStep (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  targetIndexTreeLower moments (power + 1) degree

theorem targetCacheLower_lift (moments : TargetIndexVector) :
    targetCacheLower (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexCacheLower moments) := by
  funext groups remaining
  exact sum_proper_subsets_card groups (fun power => moments power remaining.card)

theorem targetTreeLower_lift (moments : TargetIndexVector) :
    targetTreeLower (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexTreeLower moments) := by
  funext groups remaining
  unfold targetTreeLower liftTargetIndexVector targetIndexTreeLower
  rw [sum_nonempty_sdiff_eq_proper remaining (fun kept => moments groups.card kept.card)]
  exact sum_proper_subsets_card remaining (moments groups.card)

theorem targetReuseStep_lift (moments : TargetIndexVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (liftTargetIndexVector moments) groups remaining = liftTargetIndexVector (targetIndexReuseStep moments) groups remaining := by
  unfold targetReuseStep liftTargetIndexVector
  have hcard (selected : Finset FtsTree) (hselected : selected ∈ remaining.powerset.erase ∅) : (insert selected groups).card = groups.card + 1 :=
    Finset.card_insert_of_notMem (hvalid.new_group (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
      (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))
  rw [Finset.sum_congr rfl (fun selected hselected => congrArg (fun power => moments power (remaining \ selected).card) (hcard selected hselected))]
  rw [sum_nonempty_sdiff_eq_proper remaining (fun kept => moments (groups.card + 1) kept.card)]
  exact sum_proper_subsets_card remaining (moments (groups.card + 1))

end SphincsSecurity.Concrete
