import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetAssignmentCount
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceSubsetMatch (target source : FewTimeView) (required : Finset FtsTree) : Nat :=
  ∏ tree ∈ required, sourceTreeMatch target source tree

theorem sourceTreeMatch_mul_self (target source : FewTimeView) (tree : FtsTree) :
    sourceTreeMatch target source tree * sourceTreeMatch target source tree = sourceTreeMatch target source tree := by
  unfold sourceTreeMatch
  split_ifs <;> decide

theorem sourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset FtsTree) :
    sourceSubsetMatch target source left * sourceSubsetMatch target source right =
      sourceSubsetMatch target source (left ∪ right) := by
  induction left using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert tree left hnot ih =>
      by_cases hright : tree ∈ right
      · rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right left hright)]
        simp only [sourceSubsetMatch, Finset.prod_insert hnot] at *
        rw [mul_assoc, ih]
        have hmem : tree ∈ left ∪ right := Finset.mem_union_right left hright
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, ← mul_assoc, sourceTreeMatch_mul_self]
      · have hnotunion : tree ∉ left ∪ right := by simp only [Finset.mem_union, not_or]; exact ⟨hnot, hright⟩
        simp only [sourceSubsetMatch, Finset.prod_insert hnot, Finset.insert_union,
          Finset.prod_insert hnotunion] at *
        rw [mul_assoc, ih]

end SphincsSecurity.Concrete
