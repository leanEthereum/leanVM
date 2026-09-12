import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeOperators
namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def targetShapeQuery (arrival : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  f groups remaining + arrival * targetCacheLower f groups remaining

noncomputable def targetShapeSigning (uniform reuse : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  f groups remaining + uniform *
    (targetCacheLower f groups remaining + targetTreeLower f groups remaining + targetCacheLower (targetTreeLower f) groups remaining) +
      reuse * targetReuseStep f groups remaining

def TargetShapeLE (f g : TargetShapeVector) : Prop := ∀ groups remaining, TargetShapeValid groups remaining → f groups remaining ≤ g groups remaining

theorem TargetShapeLE.refl (f : TargetShapeVector) : TargetShapeLE f f := fun _ _ _ => le_rfl

theorem TargetShapeLE.trans {f g h : TargetShapeVector} (hfg : TargetShapeLE f g) (hgh : TargetShapeLE g h) : TargetShapeLE f h :=
  fun G R hv => (hfg G R hv).trans (hgh G R hv)

theorem targetCacheLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetCacheLower f) (targetCacheLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun kept hkept => h kept remaining
    (hvalid.subsets (Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2) (Finset.Subset.refl _)))

theorem targetTreeLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetTreeLower f) (targetTreeLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun _ _ => h _ _ (hvalid.subsets (Finset.Subset.refl _) Finset.sdiff_subset))

theorem targetReuseStep_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetReuseStep f) (targetReuseStep g) := by
  intro groups remaining hvalid
  apply Finset.sum_le_sum
  intro selected hselected
  exact h _ _ (hvalid.reuse
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))

theorem targetShapeQuery_mono (arrival : ENNReal) {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetShapeQuery arrival f) (targetShapeQuery arrival g) := by
  intro groups remaining hvalid
  exact add_le_add (h groups remaining hvalid) (mul_le_mul' le_rfl (targetCacheLower_shape_mono h groups remaining hvalid))

theorem targetShapeSigning_mono (uniform reuse : ENNReal) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeSigning uniform reuse f) (targetShapeSigning uniform reuse g) := by
  intro groups remaining hvalid
  exact add_le_add (add_le_add (h groups remaining hvalid) (mul_le_mul' le_rfl
    (add_le_add (add_le_add (targetCacheLower_shape_mono h groups remaining hvalid) (targetTreeLower_shape_mono h groups remaining hvalid))
      (targetCacheLower_shape_mono (targetTreeLower_shape_mono h) groups remaining hvalid))))
    (mul_le_mul' le_rfl (targetReuseStep_shape_mono h groups remaining hvalid))

theorem targetShapeSigning_query_commute (uniform reuse arrival : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning uniform reuse (targetShapeQuery arrival f) groups remaining =
      targetShapeQuery arrival (targetShapeSigning uniform reuse f) groups remaining +
        arrival * reuse * (targetTreeLower f groups remaining + targetCacheLower (targetTreeLower f) groups remaining) := by
  have htree : targetTreeLower (targetShapeQuery arrival f) = fun G R =>
      targetTreeLower f G R + arrival * targetCacheLower (targetTreeLower f) G R := by
    funext G R
    change targetTreeLower (fun G R => f G R + arrival * targetCacheLower f G R) G R = _
    rw [targetTreeLower_add, targetTreeLower_mul, ← targetCacheLower_tree_commute]
  unfold targetShapeSigning
  rw [htree]
  unfold targetShapeQuery
  simp only [targetCacheLower_add, targetCacheLower_mul, targetReuseStep_add, targetReuseStep_mul]
  rw [targetReuse_cache_commute f groups remaining hvalid]
  ring

theorem targetShapeQuery_signing_le (uniform reuse arrival : ENNReal) (f : TargetShapeVector) :
    TargetShapeLE (targetShapeQuery arrival (targetShapeSigning uniform reuse f)) (targetShapeSigning uniform reuse (targetShapeQuery arrival f)) := by
  intro groups remaining hvalid
  rw [targetShapeSigning_query_commute uniform reuse arrival f groups remaining hvalid]
  exact le_self_add

noncomputable def targetShapeEnvelope (uniform reuse arrival : ENNReal) (queries signings : Nat) (f : TargetShapeVector) : TargetShapeVector :=
  (targetShapeSigning uniform reuse)^[signings] ((targetShapeQuery arrival)^[queries] f)

theorem targetShapeSigning_iterate_mono (uniform reuse : ENNReal) (signings : Nat) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE ((targetShapeSigning uniform reuse)^[signings] f) ((targetShapeSigning uniform reuse)^[signings] g) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetShapeSigning_mono uniform reuse ih

end SphincsSecurity.Concrete
