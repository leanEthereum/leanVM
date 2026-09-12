import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def targetGroupAt (groups : Finset (Finset FtsTree)) (slot : Fin groups.card) : Finset FtsTree :=
  (groups.equivFin.symm slot).val

theorem targetGroupAt_mem (groups : Finset (Finset FtsTree)) (slot : Fin groups.card) : targetGroupAt groups slot ∈ groups :=
  (groups.equivFin.symm slot).property

theorem targetGroupAt_injective (groups : Finset (Finset FtsTree)) : Function.Injective (targetGroupAt groups) :=
  fun _ _ h => groups.equivFin.symm.injective (Subtype.ext h)

theorem targetGroupAt_image (groups : Finset (Finset FtsTree)) : Finset.univ.image (targetGroupAt groups) = groups := by
  ext group
  constructor
  · intro h
    obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp h
    exact targetGroupAt_mem groups slot
  · intro h
    exact Finset.mem_image.mpr ⟨groups.equivFin ⟨group, h⟩, Finset.mem_univ _, by simp [targetGroupAt]⟩

theorem prod_targetGroupAt (groups : Finset (Finset FtsTree)) (f : Finset FtsTree → ENNReal) :
    (∏ slot : Fin groups.card, f (targetGroupAt groups slot)) = ∏ group ∈ groups, f group := by
  calc
    _ = ∏ group ∈ Finset.univ.image (targetGroupAt groups), f group :=
      (Finset.prod_image (targetGroupAt_injective groups).injOn).symm
    _ = _ := by rw [targetGroupAt_image]

theorem sum_targetGroupAt_proper (groups : Finset (Finset FtsTree)) (f : Finset (Finset FtsTree) → ENNReal) :
    (∑ kept ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase Finset.univ,
      f (kept.image (targetGroupAt groups))) = ∑ kept ∈ groups.powerset.erase groups, f kept := by
  have hi := Finset.image_injective (targetGroupAt_injective groups)
  rw [← Finset.sum_image hi.injOn, Finset.image_erase hi, ← Finset.powerset_image, targetGroupAt_image]

theorem sum_nonempty_sdiff_eq_proper {α : Type} [DecidableEq α] (s : Finset α) (f : Finset α → ENNReal) :
    (∑ removed ∈ s.powerset.erase ∅, f (s \ removed)) = ∑ kept ∈ s.powerset.erase s, f kept := by
  apply Finset.sum_bij' (fun removed _ => s \ removed) (fun kept _ => s \ kept)
  · intro removed hremoved
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hremoved
    exact Finset.mem_erase.mpr ⟨(Finset.sdiff_ssubset (Finset.mem_powerset.mp hsub)
      (Finset.nonempty_iff_ne_empty.mpr hne)).ne, Finset.mem_powerset.mpr Finset.sdiff_subset⟩
  · intro kept hkept
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hkept
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr Finset.sdiff_subset⟩
    intro hempty
    exact hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hsub) (Finset.sdiff_eq_empty_iff_subset.mp hempty))
  · intro removed hremoved
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2)
  · intro kept hkept
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2)
  · intro _ _; rfl

theorem sum_targetGroupAt_removed_products (groups : Finset (Finset FtsTree)) (f : Finset FtsTree → ENNReal) :
    (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      ∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed, f (targetGroupAt groups slot)) =
      ∑ kept ∈ groups.powerset.erase groups, ∏ group ∈ kept, f group := by
  rw [sum_nonempty_sdiff_eq_proper _ (fun kept => ∏ slot ∈ kept, f (targetGroupAt groups slot))]
  simp only [← Finset.prod_image (targetGroupAt_injective groups).injOn]
  exact sum_targetGroupAt_proper groups (fun kept => ∏ group ∈ kept, f group)

end SphincsSecurity.Concrete
