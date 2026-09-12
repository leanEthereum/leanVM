import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetMomentShapes
namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev TargetShapeVector := Finset (Finset FtsTree) → Finset FtsTree → ENNReal

noncomputable def targetCacheAll (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  ∑ kept ∈ groups.powerset, f kept remaining

noncomputable def targetCacheLower (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  ∑ kept ∈ groups.powerset.erase groups, f kept remaining

noncomputable def targetTreeLower (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  ∑ selected ∈ remaining.powerset.erase ∅, f groups (remaining \ selected)

noncomputable def targetReuseStep (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  ∑ selected ∈ remaining.powerset.erase ∅, f (insert selected groups) (remaining \ selected)

theorem targetCacheAll_eq (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheAll f groups remaining = f groups remaining + targetCacheLower f groups remaining := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (Finset.Subset.refl groups))).symm

theorem targetCacheLower_add (f g : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (fun G R => f G R + g G R) groups remaining = targetCacheLower f groups remaining + targetCacheLower g groups remaining := by
  simp only [targetCacheLower, Finset.sum_add_distrib]

theorem targetTreeLower_add (f g : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetTreeLower (fun G R => f G R + g G R) groups remaining = targetTreeLower f groups remaining + targetTreeLower g groups remaining := by
  simp only [targetTreeLower, Finset.sum_add_distrib]

theorem targetReuseStep_add (f g : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetReuseStep (fun G R => f G R + g G R) groups remaining = targetReuseStep f groups remaining + targetReuseStep g groups remaining := by
  simp only [targetReuseStep, Finset.sum_add_distrib]

theorem targetCacheLower_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (fun G R => c * f G R) groups remaining = c * targetCacheLower f groups remaining := by
  simp only [targetCacheLower, Finset.mul_sum]

theorem targetTreeLower_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetTreeLower (fun G R => c * f G R) groups remaining = c * targetTreeLower f groups remaining := by
  simp only [targetTreeLower, Finset.mul_sum]

theorem targetReuseStep_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetReuseStep (fun G R => c * f G R) groups remaining = c * targetReuseStep f groups remaining := by
  simp only [targetReuseStep, Finset.mul_sum]

theorem targetCacheLower_tree_commute (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (targetTreeLower f) groups remaining = targetTreeLower (targetCacheLower f) groups remaining := by
  unfold targetCacheLower targetTreeLower
  exact Finset.sum_comm

private theorem sum_erase_as_indicator {α : Type} [DecidableEq α] (s : Finset α) (a : α) (f : α → ENNReal) :
    (∑ x ∈ s.erase a, f x) = ∑ x ∈ s, if x = a then 0 else f x := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x = a <;> simp only [h, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]

theorem targetCacheLower_insert (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining selected : Finset FtsTree)
    (hnot : selected ∉ groups) :
    targetCacheLower f (insert selected groups) remaining = targetCacheAll f groups remaining +
      targetCacheLower (fun G R => f (insert selected G) R) groups remaining := by
  unfold targetCacheLower targetCacheAll
  rw [sum_erase_as_indicator, Finset.sum_powerset_insert hnot]
  rw [sum_erase_as_indicator]
  congr 1
  · apply Finset.sum_congr rfl
    intro kept hkept
    have hne : kept ≠ insert selected groups := by
      intro heq
      exact hnot ((Finset.mem_powerset.mp hkept) (heq ▸ Finset.mem_insert_self selected groups))
    exact if_neg hne
  · apply Finset.sum_congr rfl
    intro kept hkept
    have hkeptNot : selected ∉ kept := fun hmem => hnot ((Finset.mem_powerset.mp hkept) hmem)
    have heq : insert selected kept = insert selected groups ↔ kept = groups := by
      constructor
      · intro heq
        have h := congrArg (fun s : Finset (Finset FtsTree) => s.erase selected) heq
        simpa only [Finset.erase_insert hkeptNot, Finset.erase_insert hnot] using h
      · rintro rfl; rfl
    simp only [heq]

theorem targetReuse_cache_commute (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (targetCacheLower f) groups remaining =
      targetCacheLower (targetReuseStep f) groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining := by
  unfold targetReuseStep
  have hinsert (selected : Finset FtsTree) (hselected : selected ∈ remaining.powerset.erase ∅) :
      targetCacheLower f (insert selected groups) (remaining \ selected) = targetCacheAll f groups (remaining \ selected) +
        targetCacheLower (fun G R => f (insert selected G) R) groups (remaining \ selected) :=
    targetCacheLower_insert f groups _ selected (hvalid.new_group
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
      (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))
  rw [Finset.sum_congr rfl hinsert]
  simp only [targetCacheAll_eq, Finset.sum_add_distrib, targetCacheLower, targetTreeLower]
  rw [Finset.sum_comm (s := remaining.powerset.erase ∅) (t := groups.powerset.erase groups)]
  rw [Finset.sum_comm (s := remaining.powerset.erase ∅) (t := groups.powerset.erase groups)]
  ring

end SphincsSecurity.Concrete
