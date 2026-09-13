import SphincsSecurity.Proof.Scheme.Code
namespace SphincsSecurity.TargetSum

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def UnitTransfer (reference candidate : Encoding) (lowered raised : ChainIndex) : Prop :=
  lowered ≠ raised ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    (reference raised).val + 1 = (candidate raised).val ∧
    ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index

def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  ∃ raised, UnitTransfer reference candidate lowered raised

theorem UnitTransfer.candidate_unique {reference left right : Encoding} {lowered raised : ChainIndex}
    (hleft : UnitTransfer reference left lowered raised) (hright : UnitTransfer reference right lowered raised) : left = right := by
  funext index
  by_cases hl : index = lowered
  · subst index
    apply Fin.ext
    have := hleft.2.1
    have := hright.2.1
    omega
  · by_cases hr : index = raised
    · subst index
      apply Fin.ext
      exact hleft.2.2.1.symm.trans hright.2.2.1
    · exact (hleft.2.2.2 index hl hr).trans (hright.2.2.2 index hl hr).symm

theorem UnitTransfer.lowered_unique {reference candidate : Encoding} {lowered raised otherLowered otherRaised : ChainIndex}
    (h : UnitTransfer reference candidate lowered raised) (hother : UnitTransfer reference candidate otherLowered otherRaised) :
    lowered = otherLowered := by
  by_contra hne
  have hd := h.2.1
  by_cases hr : lowered = otherRaised
  · subst otherRaised
    have := hother.2.2.1
    omega
  · have he := hother.2.2.2 lowered hne hr
    rw [he] at hd
    omega

theorem UnitTransfer.ne {reference candidate : Encoding} {lowered raised : ChainIndex}
    (h : UnitTransfer reference candidate lowered raised) : candidate ≠ reference := by
  intro he
  have hd := h.2.1
  rw [he] at hd
  omega

theorem UnitNeighborAt.lowered_unique {reference candidate : Encoding} {left right : ChainIndex}
    (hleft : UnitNeighborAt reference candidate left) (hright : UnitNeighborAt reference candidate right) : left = right := by
  obtain ⟨raised, hleft⟩ := hleft
  obtain ⟨otherRaised, hright⟩ := hright
  exact hleft.lowered_unique hright

noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) : (unitNeighbors reference lowered).card ≤ 41 := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} → {raised : ChainIndex // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.choose, candidate.property.choose_spec.1.symm⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    change left.property.choose = right.property.choose at he'
    apply left.property.choose_spec.candidate_unique
    rw [he']
    exact right.property.choose_spec
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : ChainIndex => raised ≠ lowered) = Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ] at hcard
  simpa only [unitNeighbors, Fintype.card_fin, numChains] using hcard

noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)

theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤ 1722 := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : ChainIndex, 41 := Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = 1722 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numChains, smul_eq_mul]

end SphincsSecurity.TargetSum
