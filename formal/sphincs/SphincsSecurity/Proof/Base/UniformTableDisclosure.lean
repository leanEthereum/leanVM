import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableRestriction
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def discloseTableValue (allowed : ι → Finset α) (coordinate : ι) (value : α) : ι → Finset α :=
  Function.update allowed coordinate {value}

omit [Fintype ι] [DecidableEq α] in
theorem discloseTableValue_nonempty (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (value : α) :
    ∀ other, (discloseTableValue allowed coordinate value other).Nonempty := by
  intro other
  by_cases heq : other = coordinate
  · subst other
    simp only [discloseTableValue, Function.update_self, Finset.singleton_nonempty]
  · simpa only [discloseTableValue, Function.update_of_ne heq] using ha other

theorem uniformTable_disclose_mass (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (value : α) (labels : ι → α) :
    PMF.uniformOfFinset (allowed coordinate) (ha coordinate) value *
        uniformTable (discloseTableValue allowed coordinate value)
          (discloseTableValue_nonempty allowed ha coordinate value) labels =
      if labels coordinate = value then uniformTable allowed ha labels else 0 := by
  rw [PMF.uniformOfFinset_apply]
  by_cases hvalue : value ∈ allowed coordinate
  · rw [if_pos hvalue]
    have h := uniformTable_update_restrict allowed ha coordinate {value} (Finset.singleton_nonempty _)
      (Finset.singleton_subset_iff.mpr hvalue) labels
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_div, discloseTableValue] using h.symm
  · rw [if_neg hvalue, zero_mul]
    by_cases hlabels : labels coordinate = value
    · rw [if_pos hlabels, uniformTable_apply,
        if_neg (fun h => hvalue (hlabels ▸ h coordinate))]
    · rw [if_neg hlabels]

end SphincsSecurity.Concrete
