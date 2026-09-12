import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.PairedHiddenMiss
import SphincsSecurity.Proof.Base.UniformTableDisclosure
namespace SphincsSecurity.Concrete.UniformTableCompletion

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def complete (allowed : Coordinate → Finset Value) : SPMF (Coordinate → Value) :=
  if h : ∀ coordinate, (allowed coordinate).Nonempty then liftM (uniformTable allowed h) else failure

noncomputable def cell (allowed : Finset Value) : SPMF Value :=
  if h : allowed.Nonempty then liftM (PMF.uniformOfFinset allowed h) else failure

omit [DecidableEq Value] in
theorem complete_of_nonempty (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    complete allowed = liftM (uniformTable allowed ha) := by rw [complete, dif_pos ha]

omit [DecidableEq Value] in
theorem complete_of_empty (allowed : Coordinate → Finset Value)
    (ha : ¬∀ coordinate, (allowed coordinate).Nonempty) : complete allowed = failure := by
  rw [complete, dif_neg ha]

theorem complete_apply (allowed : Coordinate → Finset Value) (labels : Coordinate → Value) :
    complete allowed labels = if ∀ coordinate, labels coordinate ∈ allowed coordinate then
      ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)⁻¹ else 0 := by
  by_cases ha : ∀ coordinate, (allowed coordinate).Nonempty
  · rw [complete_of_nonempty allowed ha, SPMF.liftM_apply, uniformTable_apply]
  · rw [complete_of_empty allowed ha, SPMF.failure_apply,
      if_neg (fun h => ha (fun coordinate => ⟨labels coordinate, h coordinate⟩))]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem cell_apply (allowed : Finset Value) (value : Value) :
    cell allowed value = if value ∈ allowed then (allowed.card : ENNReal)⁻¹ else 0 := by
  by_cases ha : allowed.Nonempty
  · rw [cell, dif_pos ha, SPMF.liftM_apply, PMF.uniformOfFinset_apply]
    split <;> simp_all
  · rw [cell, dif_neg ha, SPMF.failure_apply, if_neg (fun h => ha ⟨value, h⟩)]

noncomputable def restrictionWeight (allowed reduced : Coordinate → Finset Value) : ENNReal :=
  ((∏ coordinate, (reduced coordinate).card : Nat) : ENNReal) /
    ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)

omit [DecidableEq Coordinate] [DecidableEq Value] in
theorem weight_of_empty (allowed reduced : Coordinate → Finset Value)
    (hr : ¬∀ coordinate, (reduced coordinate).Nonempty) : restrictionWeight allowed reduced = 0 := by
  obtain ⟨coordinate, hcoordinate⟩ := not_forall.mp hr
  have hcard : (reduced coordinate).card = 0 := by
    simpa only [Finset.card_eq_zero] using Finset.not_nonempty_iff_eq_empty.mp hcoordinate
  have hprod : (∏ coordinate, (reduced coordinate).card : Nat) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ coordinate) hcard
  simp only [restrictionWeight, hprod, Nat.cast_zero, ENNReal.zero_div]

omit [DecidableEq Value] in
theorem weight_tsum_complete (allowed reduced : Coordinate → Finset Value) :
    restrictionWeight allowed reduced * (∑' labels, complete reduced labels) = restrictionWeight allowed reduced := by
  by_cases hr : ∀ coordinate, (reduced coordinate).Nonempty
  · simp only [complete_of_nonempty reduced hr, SPMF.liftM_apply, PMF.tsum_coe, mul_one]
  · simp only [weight_of_empty allowed reduced hr, zero_mul]

theorem restrict_mass (allowed reduced : Coordinate → Finset Value)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (labels : Coordinate → Value) :
    (if ∀ coordinate, labels coordinate ∈ reduced coordinate then complete allowed labels else 0) =
      restrictionWeight allowed reduced * complete reduced labels := by
  by_cases hr : ∀ coordinate, (reduced coordinate).Nonempty
  · have ha : ∀ coordinate, (allowed coordinate).Nonempty := fun coordinate => (hr coordinate).mono (hsub coordinate)
    rw [complete_of_nonempty allowed ha, complete_of_nonempty reduced hr]
    simpa only [SPMF.liftM_apply, restrictionWeight] using uniformTable_restrict allowed reduced ha hr hsub labels
  · rw [complete_of_empty reduced hr, SPMF.failure_apply, mul_zero,
      if_neg (fun h => hr (fun coordinate => ⟨labels coordinate, h coordinate⟩))]

theorem restrict_guard (allowed reduced : Coordinate → Finset Value)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (event : (Coordinate → Value) → Prop)
    (hguard : ∀ labels, (∀ coordinate, labels coordinate ∈ reduced coordinate) ↔
      (∀ coordinate, labels coordinate ∈ allowed coordinate) ∧ event labels) (labels : Coordinate → Value) :
    (if event labels then complete allowed labels else 0) =
      restrictionWeight allowed reduced * complete reduced labels := by
  rw [← restrict_mass allowed reduced hsub labels]
  by_cases ha : ∀ coordinate, labels coordinate ∈ allowed coordinate
  · simp only [hguard, ha, implies_true, true_and]
  · simp only [complete_apply, ha, if_false, ite_self]

omit [Fintype Coordinate] in
theorem paired_subset (allowed : Coordinate → Finset Value) (child parent : Coordinate)
    (candidate answer : Value) :
    ∀ coordinate, pairedMissAllowed allowed child candidate parent answer coordinate ⊆ allowed coordinate := by
  intro coordinate
  unfold pairedMissAllowed eraseTableValue
  by_cases hp : coordinate = parent
  · subst coordinate
    rw [Function.update_self]
    apply Finset.Subset.trans (Finset.erase_subset _ _)
    by_cases hc : parent = child
    · subst parent
      rw [Function.update_self]
      exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hc]
  · rw [Function.update_of_ne hp]
    by_cases hc : coordinate = child
    · subst coordinate
      rw [Function.update_self]
      exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hc]

theorem paired_mass (allowed : Coordinate → Finset Value) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate answer : Value) (labels : Coordinate → Value) :
    (if labels child ≠ candidate ∧ labels parent ≠ answer then complete allowed labels else 0) =
      restrictionWeight allowed (pairedMissAllowed allowed child candidate parent answer) *
        complete (pairedMissAllowed allowed child candidate parent answer) labels := by
  have h := restrict_guard allowed _ (paired_subset allowed child parent candidate answer) _
    (pairedMissAllowed_membership allowed child parent hne candidate answer) labels
  by_cases hevent : labels child ≠ candidate ∧ labels parent ≠ answer
  · simpa only [if_pos hevent] using h
  · simpa only [if_neg hevent] using h

theorem single_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (value : Value)
    (labels : Coordinate → Value) :
    (if labels coordinate ≠ value then complete allowed labels else 0) =
      restrictionWeight allowed (eraseTableValue allowed coordinate value) *
        complete (eraseTableValue allowed coordinate value) labels := by
  have hsub : ∀ other, eraseTableValue allowed coordinate value other ⊆ allowed other := by
    intro other
    by_cases heq : other = coordinate
    · subst other
      simp only [eraseTableValue, Function.update_self]
      exact Finset.erase_subset _ _
    · rw [eraseTableValue, Function.update_of_ne heq]
  have hguard (labels : Coordinate → Value) :
      (∀ other, labels other ∈ eraseTableValue allowed coordinate value other) ↔
        (∀ other, labels other ∈ allowed other) ∧ labels coordinate ≠ value := by
    constructor
    · intro h
      refine ⟨fun other => hsub other (h other), ?_⟩
      have hc := h coordinate
      simp only [eraseTableValue, Function.update_self, Finset.mem_erase] at hc
      exact hc.1
    · rintro ⟨h, hne⟩ other
      by_cases heq : other = coordinate
      · subst other
        simpa only [eraseTableValue, Function.update_self, Finset.mem_erase] using And.intro hne (h coordinate)
      · simpa only [eraseTableValue, Function.update_of_ne heq] using h other
  have h := restrict_guard allowed _ hsub _ hguard labels
  by_cases hevent : labels coordinate ≠ value
  · simpa only [if_pos hevent] using h
  · simpa only [if_neg hevent] using h

theorem disclose_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (value : Value)
    (labels : Coordinate → Value) :
    cell (allowed coordinate) value * complete (discloseTableValue allowed coordinate value) labels =
      if labels coordinate = value then complete allowed labels else 0 := by
  by_cases ha : ∀ coordinate, (allowed coordinate).Nonempty
  · rw [complete_of_nonempty allowed ha, complete_of_nonempty _ (discloseTableValue_nonempty allowed ha coordinate value),
      cell, dif_pos (ha coordinate)]
    simpa only [SPMF.liftM_apply] using uniformTable_disclose_mass allowed ha coordinate value labels
  · rw [complete_of_empty allowed ha, SPMF.failure_apply, ite_self]
    by_cases hv : value ∈ allowed coordinate
    · have hr : ¬∀ other, (discloseTableValue allowed coordinate value other).Nonempty := by
        intro hr
        apply ha
        intro other
        by_cases heq : other = coordinate
        · subst other
          exact ⟨value, hv⟩
        · simpa only [discloseTableValue, Function.update_of_ne heq] using hr other
      rw [complete_of_empty _ hr, SPMF.failure_apply, mul_zero]
    · rw [cell_apply, if_neg hv, zero_mul]

theorem bind_disclose {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (next : Value → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (labels coordinate) labels) =
      (cell (allowed coordinate) >>= fun value =>
        complete (discloseTableValue allowed coordinate value) >>= next value) := by
  classical
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, disclose_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp

end SphincsSecurity.Concrete.UniformTableCompletion
