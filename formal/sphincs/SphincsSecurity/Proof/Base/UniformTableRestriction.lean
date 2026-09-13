import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableConditioning
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq α] in
theorem piFinset_update_card (allowed : ι → Finset α) (coordinate : ι) (values : Finset α) :
    (Fintype.piFinset (Function.update allowed coordinate values)).card =
      values.card * ∏ other ∈ Finset.univ.erase coordinate, (allowed other).card := by
  rw [Fintype.card_piFinset]
  have h : (fun other => (Function.update allowed coordinate values other).card) =
      Function.update (fun other => (allowed other).card) coordinate values.card := by
    funext other
    by_cases heq : other = coordinate <;> simp only [Function.update_apply, heq, if_true, if_false]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ coordinate), Finset.sdiff_singleton_eq_erase]

omit [DecidableEq α] in
theorem piFinset_update_card_ratio (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α) :
    ((Fintype.piFinset (Function.update allowed coordinate values)).card : ENNReal) /
        (Fintype.piFinset allowed).card = (values.card : ENNReal) / (allowed coordinate).card := by
  rw [piFinset_update_card, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ (fun other => (allowed other).card) (Finset.mem_univ coordinate)]
  have hrest : ((∏ other ∈ Finset.univ.erase coordinate, (allowed other).card : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun other _ => Nat.ne_of_gt (ha other).card_pos)
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [ENNReal.mul_div_mul_right _ _ hrest (by finiteness)]

theorem uniformTable_update_restrict (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α)
    (hv : values.Nonempty) (hsub : values ⊆ allowed coordinate) (table : ι → α) :
    (if table coordinate ∈ values then uniformTable allowed ha table else 0) =
      ((values.card : ENNReal) / (allowed coordinate).card) *
        uniformTable (Function.update allowed coordinate values)
          (by intro other; by_cases heq : other = coordinate
              · simpa only [heq, Function.update_self] using hv
              · simpa only [Function.update_of_ne heq] using ha other) table := by
  classical
  letI : DecidableEq (ι → α) := Classical.decEq _
  let reduced := Function.update allowed coordinate values
  have hred : ∀ other, (reduced other).Nonempty := by
    intro other
    by_cases heq : other = coordinate <;> simp only [reduced, Function.update_apply, heq, if_true, if_false]
    · exact hv
    · exact ha other
  have hsub' : Fintype.piFinset reduced ⊆ Fintype.piFinset allowed := by
    apply Fintype.piFinset_subset
    intro other
    by_cases heq : other = coordinate <;> simp only [reduced, Function.update_apply, heq, if_true, if_false]
    · simpa only [heq] using hsub
    · exact Finset.Subset.refl _
  have h := uniformFinset_restrict_mass (Fintype.piFinset allowed) (Fintype.piFinset reduced)
    (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hred) hsub' table
  rw [show (Fintype.piFinset reduced).card =
      (Fintype.piFinset (Function.update allowed coordinate values)).card from rfl,
    piFinset_update_card_ratio allowed ha coordinate values] at h
  change (if table ∈ Fintype.piFinset reduced then uniformTable allowed ha table else 0) =
    ((values.card : ENNReal) / (allowed coordinate).card) * uniformTable reduced hred table at h
  rw [← h]
  by_cases ht : ∀ other, table other ∈ allowed other
  · have heq : table ∈ Fintype.piFinset reduced ↔ table coordinate ∈ values := by
      rw [Fintype.piFinset_update_eq_filter_piFinset_mem allowed coordinate hsub, Finset.mem_filter,
        Fintype.mem_piFinset]
      exact and_iff_right ht
    simp only [heq]
  · have hz : uniformTable allowed ha table = 0 := by rw [uniformTable_apply, if_neg ht]
    simp only [hz, ite_self]

theorem probEvent_uniformTable_member (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (values : Finset α)
    (hv : values.Nonempty) (hsub : values ⊆ allowed coordinate) :
    Pr[fun table => table coordinate ∈ values | uniformTable allowed ha] =
      (values.card : ENNReal) / (allowed coordinate).card := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    uniformTable_update_restrict allowed ha coordinate values hv hsub, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem probEvent_uniformTable_eq (allowed : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (coordinate : ι) (candidate : α) :
    Pr[fun table => table coordinate = candidate | uniformTable allowed ha] =
      if candidate ∈ allowed coordinate then ((allowed coordinate).card : ENNReal)⁻¹ else 0 := by
  by_cases hc : candidate ∈ allowed coordinate
  · have h := probEvent_uniformTable_member allowed ha coordinate {candidate} (Finset.singleton_nonempty _)
      (Finset.singleton_subset_iff.mpr hc)
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_div, hc, if_true] using h
  · simp only [hc, if_false, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro table
    by_cases heq : table coordinate = candidate
    · have hn : ¬ ∀ other, table other ∈ allowed other := fun h => hc (heq ▸ h coordinate)
      simp only [heq, if_true, uniformTable_apply, hn, if_false]
    · simp only [heq, if_false]

end SphincsSecurity.Concrete
