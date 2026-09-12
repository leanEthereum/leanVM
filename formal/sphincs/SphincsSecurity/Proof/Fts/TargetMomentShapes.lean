import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

attribute [local instance] Classical.propDecidable

structure TargetShapeValid (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : Prop where
  nonempty : ∀ group ∈ groups, group.Nonempty
  disjoint : ∀ first ∈ groups, ∀ second ∈ groups, first ≠ second → Disjoint first second
  remaining : ∀ group ∈ groups, Disjoint group remaining

theorem TargetShapeValid.subsets {groups kept : Finset (Finset FtsTree)} {remaining trees : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hgroups : kept ⊆ groups) (htrees : trees ⊆ remaining) :
    TargetShapeValid kept trees where
  nonempty group hgroup := hvalid.nonempty group (hgroups hgroup)
  disjoint first hfirst second hsecond hne := hvalid.disjoint first (hgroups hfirst) second (hgroups hsecond) hne
  remaining group hgroup := (hvalid.remaining group (hgroups hgroup)).mono_right htrees

theorem TargetShapeValid.new_group {groups : Finset (Finset FtsTree)} {remaining selected : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) : selected ∉ groups := by
  intro hmem
  obtain ⟨tree, htree⟩ := hselected
  exact Finset.disjoint_left.mp (hvalid.remaining selected hmem) htree (hsub htree)

theorem TargetShapeValid.reuse {groups : Finset (Finset FtsTree)} {remaining selected : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) :
    TargetShapeValid (insert selected groups) (remaining \ selected) := by
  constructor
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact hselected
    · exact hvalid.nonempty group hgroup
  · intro first hfirst second hsecond hne
    rcases Finset.mem_insert.mp hfirst with rfl | hfirstOld
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hne rfl).elim
      · exact ((hvalid.remaining second hsecond).mono_right hsub).symm
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hvalid.remaining first hfirstOld).mono_right hsub
      · exact hvalid.disjoint first hfirstOld second hsecond hne
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact Finset.disjoint_left.mpr (fun tree htree hrest => (Finset.mem_sdiff.mp hrest).2 htree)
    · exact (hvalid.remaining group hgroup).mono_right Finset.sdiff_subset

end SphincsSecurity.Concrete
