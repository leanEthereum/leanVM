import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def eraseTableValue (allowed : ι → Finset α) (coordinate : ι) (candidate : α) : ι → Finset α :=
  Function.update allowed coordinate ((allowed coordinate).erase candidate)

def pairedMissAllowed (allowed : ι → Finset α) (child : ι) (candidate : α) (parent : ι) (answer : α) :
    ι → Finset α := eraseTableValue (eraseTableValue allowed child candidate) parent answer

omit [Fintype ι] in
theorem pairedMissAllowed_membership (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (table : ι → α) :
    (∀ coordinate, table coordinate ∈ pairedMissAllowed allowed child candidate parent answer coordinate) ↔
      (∀ coordinate, table coordinate ∈ allowed coordinate) ∧ table child ≠ candidate ∧ table parent ≠ answer := by
  constructor
  · intro h
    have hchild := h child
    have hparent := h parent
    simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self,
      Function.update_of_ne hne.symm, Finset.mem_erase] at hchild hparent
    refine ⟨?_, hchild.1, hparent.1⟩
    intro coordinate
    by_cases hp : coordinate = parent
    · simpa only [hp] using hparent.2
    by_cases hc : coordinate = child
    · simpa only [hc] using hchild.2
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using h coordinate
  · rintro ⟨h, hc, hp⟩ coordinate
    by_cases heqp : coordinate = parent
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm,
        Finset.mem_erase]
      exact ⟨hp, h parent⟩
    by_cases heqc : coordinate = child
    · subst coordinate
      simp only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self, Finset.mem_erase]
      exact ⟨hc, h child⟩
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne heqp, Function.update_of_ne heqc] using h coordinate

omit [Fintype ι] in
theorem pairedMissAllowed_card_lower (allowed : ι → Finset α) (child parent : ι) (hne : child ≠ parent)
    (candidate answer : α) (coordinate : ι) :
    (allowed coordinate).card - 1 ≤ (pairedMissAllowed allowed child candidate parent answer coordinate).card := by
  by_cases hp : coordinate = parent
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_self, Function.update_of_ne hne.symm] using
      (Finset.pred_card_le_card_erase (s := allowed parent) (a := answer))
  by_cases hc : coordinate = child
  · subst coordinate
    simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hne, Function.update_self] using
      (Finset.pred_card_le_card_erase (s := allowed child) (a := candidate))
  simpa only [pairedMissAllowed, eraseTableValue, Function.update_of_ne hp, Function.update_of_ne hc] using
    Nat.sub_le (allowed coordinate).card 1

end SphincsSecurity.Concrete
