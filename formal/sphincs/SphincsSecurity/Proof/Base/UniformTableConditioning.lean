import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem uniformFinset_restrict_mass {α : Type} (source target : Finset α)
    (hs : source.Nonempty) (ht : target.Nonempty) (hsub : target ⊆ source) (value : α) :
    (if value ∈ target then PMF.uniformOfFinset source hs value else 0) =
      ((target.card : ENNReal) / source.card) * PMF.uniformOfFinset target ht value := by
  by_cases hv : value ∈ target
  · rw [if_pos hv, PMF.uniformOfFinset_apply_of_mem hs (hsub hv), PMF.uniformOfFinset_apply_of_mem ht hv]
    have ht0 : (target.card : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht.card_pos
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel ht0 (by finiteness), one_mul]
  · simp only [hv, if_false, PMF.uniformOfFinset_apply_of_notMem ht hv, mul_zero]

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]

noncomputable def uniformTable (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty) :
    PMF (ι → α) := PMF.uniformOfFinset (Fintype.piFinset allowed) (Fintype.piFinset_nonempty.mpr hallowed)

theorem uniformTable_apply (allowed : ι → Finset α) (hallowed : ∀ coordinate, (allowed coordinate).Nonempty)
    (table : ι → α) :
    uniformTable allowed hallowed table =
      if ∀ coordinate, table coordinate ∈ allowed coordinate then
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)⁻¹ else 0 := by
  simp only [uniformTable, PMF.uniformOfFinset_apply, Fintype.mem_piFinset, Fintype.card_piFinset]

theorem uniformTable_restrict (allowed reduced : ι → Finset α)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (hr : ∀ coordinate, (reduced coordinate).Nonempty)
    (hsub : ∀ coordinate, reduced coordinate ⊆ allowed coordinate) (table : ι → α) :
    (if ∀ coordinate, table coordinate ∈ reduced coordinate then uniformTable allowed ha table else 0) =
      (((∏ coordinate, (reduced coordinate).card : Nat) : ENNReal) /
        ((∏ coordinate, (allowed coordinate).card : Nat) : ENNReal)) * uniformTable reduced hr table := by
  simpa only [uniformTable, Fintype.mem_piFinset, Fintype.card_piFinset] using
    uniformFinset_restrict_mass (Fintype.piFinset allowed) (Fintype.piFinset reduced)
      (Fintype.piFinset_nonempty.mpr ha) (Fintype.piFinset_nonempty.mpr hr)
      (Fintype.piFinset_subset reduced allowed hsub) table

end SphincsSecurity.Concrete
